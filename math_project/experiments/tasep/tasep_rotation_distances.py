"""Constructive geodesics and exact distance polynomials for Cao's lift.

Only the Python standard library is required. This supplements, and does not
overwrite, the earlier BFS datasets. See tasep_rotation_distances.md.
"""

import argparse
from collections import Counter
from fractions import Fraction
import json
from math import comb
from pathlib import Path

from tasep_tamari import (cao_move, cherries, relabel, replace, rotations,
                         trees)


def subtree(t, path):
    for step in path:
        t = t[step]
    return t


def mirror(t):
    return t if isinstance(t, int) else (mirror(t[1]), mirror(t[0]))


def intervals(t):
    """Proper nonsingleton leaf intervals, with fixed inorder positions."""
    out = set()
    position = 0

    def walk(v, root=False):
        nonlocal position
        if isinstance(v, int):
            position += 1
            return
        lo = position
        walk(v[0]); walk(v[1])
        if not root:
            out.add((lo, position))

    walk(t, True)
    return out


def search_cost(t):
    """Number of left decisions in the first-right-leaf search."""
    if isinstance(t, int):
        return 0
    l, r = t
    return search_cost(r) if isinstance(l, int) else 1 + search_cost(l)


def geodesic(t, mark):
    """Return an explicit shortest rotation path for a marked Cao event.

    Trees are relabeled after rotations; integer labels denote inorder
    positions, not persistent particle identities.
    """
    if mark[-1] == 0:
        mirrored = relabel(mirror(t))
        return [relabel(mirror(v)) for v in geodesic(mirrored, tuple(1-x for x in mark))]

    states = [t]

    def rotate(path, right):
        v = subtree(states[-1], path)
        if right:
            (a, b), c = v
            new = (a, (b, c))
        else:
            a, (b, c) = v
            new = ((a, b), c)
        states.append(relabel(replace(states[-1], path, new)))

    def push(path, mirrored=False):
        """Push an extra end leaf through a subtree using search_cost moves."""
        v = subtree(states[-1], path)
        y = v[0] if mirrored else v[1]
        if isinstance(y, int):
            return
        near = y[1] if mirrored else y[0]
        if isinstance(near, int):
            # The end leaf and near leaf exchange only their inorder labels;
            # the tree shape at this root is already correct.
            push(path + ((0,) if mirrored else (1,)), mirrored)
        else:
            rotate(path, right=mirrored)
            push(path + ((1,) if mirrored else (0,)), mirrored)

    if 0 not in mark:  # right-boundary wrap
        parent = mark[:-1]
        rotate(parent, right=False)
        push(parent + (0,), mirrored=True)
    else:  # unique decomposition mark = prefix + L + R^k
        split = max(i for i, x in enumerate(mark) if x == 0)
        pivot = mark[:split]
        k = len(mark) - split - 1
        assert k >= 1
        for depth in range(k - 1, -1, -1):
            rotate(pivot + (0,) + (1,)*depth, right=False)
        rotate(pivot, right=True)
        push(pivot + (1,))
    return states


def distance_formula(t, mark):
    if mark[-1] == 0:
        return distance_formula(relabel(mirror(t)), tuple(1-x for x in mark))
    if 0 not in mark:
        sibling = subtree(t, mark[:-1])[0]
        return 1 + search_cost(mirror(sibling))
    split = max(i for i, x in enumerate(mark) if x == 0)
    k = len(mark) - split - 1
    y = subtree(t, mark[:split])[1]
    return k + 1 + search_cost(y)


def event_polynomials(max_sites):
    """Exact coefficients of the bivariate event GF, as distance Counters.

    C=1+z*C^2; W=1/(1-z-u*z*C); H=1+z*W.
    Boundary=2*z^2*u*C*H; bulk=2*z^3*u^2*C*W/sqrt(1-4*z).
    z counts internal nodes, so the N-site polynomial is [z^(N+1)].
    """
    catalan = [comb(2*n, n)//(n+1) for n in range(max_sites + 1)]
    w = [Counter({0: 1})]
    for n in range(1, max_sites):
        value = w[n-1].copy()
        for j in range(n):
            for distance, count in w[n-1-j].items():
                value[distance+1] += catalan[j]*count
        w.append(value)
    out = {}
    for n in range(1, max_sites + 1):
        boundary, bulk = Counter(), Counter()
        for j in range(n):
            h_degree = n-1-j
            h = Counter({0: 1}) if h_degree == 0 else w[h_degree-1]
            for distance, count in h.items():
                boundary[distance+1] += 2*catalan[j]*count
        for j in range(n-1):
            c_over_s = comb(2*j+1, j)
            for distance, count in w[n-2-j].items():
                bulk[distance+2] += 2*c_over_s*count
        out[n] = {'boundary': boundary, 'bulk': bulk, 'all': boundary + bulk}
    return out


def moments(hist):
    total = sum(hist.values())
    mean = Fraction(sum(d*c for d, c in hist.items()), total)
    second = Fraction(sum(d*d*c for d, c in hist.items()), total)
    return mean, second - mean*mean


def moment_formulas(n):
    """Exact coefficient extraction from first two derivatives of the GF."""
    def m(k):
        if k == 0:
            return Fraction(1)
        return Fraction(2*n*comb(2*n+k, n), (2*n+k)*comb(2*n, n))
    mean = Fraction(4*n*n-2*n+4, (n+1)*(n+2))
    second = 4*m(4)-10*m(3)+14*m(2)-11*m(1)+4
    return mean, second-mean*mean


def finite_distance_counts(n, d):
    """Closed finite sums, independent of the polynomial-series recursion."""
    if d == 1:
        return {'boundary': 2*sum(comb(2*k, k)//(k+1) for k in range(n)), 'bulk': 0}
    if d < 1:
        return {'boundary': 0, 'bulk': 0}
    bulk_degree = n-d
    h = d-1
    bulk = 2*sum(comb(2*j+h, j)*comb(bulk_degree-j+h-1, h-1)
                 for j in range(bulk_degree+1))
    boundary_degree = n-d-1
    boundary = 2*sum((d*comb(2*j+d, j)//(2*j+d))*comb(boundary_degree-j+d-1, d-1)
                     for j in range(boundary_degree+1))
    return {'boundary': boundary, 'bulk': bulk}


def verify(max_geometry=7, max_series=100):
    polynomials = event_polynomials(max_series)
    geometry_checks = []
    for n in range(1, max_geometry + 1):
        actual = Counter()
        steps = 0
        for t in trees(0, n+2):
            for mark, cherry in cherries(t):
                target, _ = cao_move(t, mark, cherry)
                path = geodesic(t, mark)
                assert path[0] == t and path[-1] == target
                distance = len(path)-1
                assert distance == distance_formula(t, mark)
                # One rotation removes one proper internal leaf interval.
                # This equality certifies shortestness, independent of BFS.
                target_intervals = intervals(target)
                assert distance == len(intervals(t)-target_intervals)
                for i, (a, b) in enumerate(zip(path, path[1:])):
                    assert b in rotations(a) or a in rotations(b)
                    assert len(intervals(a)-target_intervals) == distance-i
                    assert len(intervals(b)-target_intervals) == distance-i-1
                    steps += 1
                actual[distance] += 1
        assert actual == polynomials[n]['all']
        geometry_checks.append({'N': n, 'events': sum(actual.values()), 'certified_rotation_steps': steps})

    # These were generated by independent full-graph BFS before the proof.
    bfs_checks = []
    for name in ('tasep_tamari_results.json', 'tasep_tamari_extended_results.json'):
        p = Path(__file__).with_name(name)
        if not p.exists():
            continue
        for row in json.loads(p.read_text()):
            n = row['N']
            if n > max_series:
                continue
            observed = {int(d): c for d, c in row['cao_lift']['rotation_distance_histogram'].items()}
            assert observed == polynomials[n]['all']
            bfs_checks.append(n)

    summaries = []
    for n, groups in polynomials.items():
        hist = groups['all']
        mean, variance = moments(hist)
        assert (mean, variance) == moment_formulas(n)
        assert sum(hist.values()) == comb(2*n, n)
        assert sum(groups['boundary'].values()) == 2*comb(2*n, n)//(n+1)
        assert max(hist) == n
        assert hist[n] == 2
        assert groups['bulk'][1] == 0
        assert hist[1] == 2*sum(comb(2*k, k)//(k+1) for k in range(n))
        for d in range(1, n+2):
            closed = finite_distance_counts(n, d)
            assert closed['bulk'] == groups['bulk'][d]
            assert closed['boundary'] == groups['boundary'][d]
        if n <= 10 or n in (20, 50, 100, max_series):
            boundary_mean, boundary_variance = moments(groups['boundary'])
            summaries.append({'N': n, 'events': sum(hist.values()),
                              'mean': str(mean), 'variance': str(variance),
                              'mean_decimal': float(mean), 'variance_decimal': float(variance),
                              'boundary_mean': str(boundary_mean),
                              'boundary_variance': str(boundary_variance),
                              'distance_counts': dict(sorted(hist.items())),
                              'boundary_counts': dict(sorted(groups['boundary'].items())),
                              'bulk_counts': dict(sorted(groups['bulk'].items()))})
    return {'geometry_checks': geometry_checks, 'independent_bfs_sizes': sorted(set(bfs_checks)),
            'series_sizes_checked': max_series, 'series_summaries': summaries,
            'limiting_pgf': 'u^2/(3-2*u)', 'limiting_mean': 4, 'limiting_variance': 6,
            'limiting_boundary_pgf': 'u*(u^2-3*u+3)/(3-2*u)^2',
            'limiting_boundary_mean': 4, 'limiting_boundary_variance': 12,
            'sampling': 'stationary event flux; each tree/cherry pair has equal weight'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry-sites', type=int, default=7)
    parser.add_argument('--series-sites', type=int, default=100)
    args = parser.parse_args()
    if not 1 <= args.geometry_sites <= args.series_sites:
        parser.error('require 1 <= geometry-sites <= series-sites')
    result = verify(args.geometry_sites, args.series_sites)
    Path(__file__).with_name('tasep_rotation_distances_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'series_summaries'}), flush=True)
    for row in result['series_summaries']:
        print(json.dumps({k: v for k, v in row.items() if not k.endswith('_counts')}), flush=True)
