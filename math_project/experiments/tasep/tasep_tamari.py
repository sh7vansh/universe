"""Exact small-system TASEP/tree checks; see tasep_tamari.md.

Run with scipy for the optional exhaustive-assignment MILP:
  uv run --python 3.12 --with scipy python tasep_tamari.py --search
The MILP asks for strong lumpability on rotation edges, allowing arbitrary
nonnegative rates and requiring the exact stationary multiplicities. It does
not impose a uniform tree stationary state (a strictly stronger condition).
"""

import argparse
from collections import Counter
from functools import lru_cache
import json
import itertools
from math import comb
from pathlib import Path


@lru_cache(None)
def trees(lo, hi):
    if hi - lo == 1:
        return (lo,)
    return tuple((l, r) for k in range(lo + 1, hi)
                 for l in trees(lo, k) for r in trees(k, hi))


def rotations(t):
    if isinstance(t, int):
        return []
    l, r = t
    out = [(l[0], (l[1], r))] if isinstance(l, tuple) else []
    return out + [(u, r) for u in rotations(l)] + [(l, u) for u in rotations(r)]


def leaf_sides(t):
    out = []

    def walk(v, side):
        if isinstance(v, int):
            out.append((v, side))
        else:
            walk(v[0], 1)  # Cao: left child = particle
            walk(v[1], 0)

    walk(t, None)
    return out


def canopy(t):
    return ''.join(str(side) for _, side in leaf_sides(t)[1:-1])


def events(word):
    out = []
    if word[0] == '0':
        out.append(('inject', '1' + word[1:]))
    for k in range(len(word) - 1):
        if word[k:k + 2] == '10':
            out.append((f'hop_{k}', word[:k] + '01' + word[k + 2:]))
    if word[-1] == '1':
        out.append(('extract', word[:-1] + '0'))
    return out


@lru_cache(None)
def weight(word):
    """Matrix ansatz DE=D+E, <W|E=<W|, D|V>=|V>."""
    k = word.find('10')
    if k < 0:
        return 1
    return weight(word[:k] + '1' + word[k + 2:]) + weight(word[:k] + '0' + word[k + 2:])


def capacity_witness(n):
    """Finite check of the general degree-capacity obstruction in the notes.

    For N>=2 no allowed TASEP edge has an allowed reverse edge. Thus outgoing
    neighbor slots and incoming neighbor slots for a fiber are disjoint.
    Stationary balance gives incoming demand = weight(c)*out(c).
    """
    if n < 2:
        raise ValueError('The no-reverse-edge argument requires N >= 2')
    c = ('01' * ((n + 1) // 2))[:n]
    predecessors = []
    if c[0] == '1':
        predecessors.append('0' + c[1:])
    if c[-1] == '0':
        predecessors.append(c[:-1] + '1')
    predecessors.extend(c[:k] + '10' + c[k + 2:]
                        for k in range(n - 1) if c[k:k + 2] == '01')
    outgoing = len(events(c))
    demand = sum(weight(s) for s in predecessors)
    capacity = weight(c) * (n - outgoing)
    assert outgoing == n // 2 + 1
    assert demand == weight(c) * outgoing and demand > capacity
    return {'N': n, 'configuration': c, 'weight': weight(c), 'outgoing': outgoing,
            'incoming_capacity': capacity, 'incoming_demand': demand,
            'slack': capacity - demand, 'predecessors': predecessors}


def replace(t, path, value):
    if not path:
        return value
    side = path[0]
    return (replace(t[0], path[1:], value), t[1]) if side == 0 else (t[0], replace(t[1], path[1:], value))


def find_leaf(t, label, path=()):
    if isinstance(t, int):
        return path if t == label else None
    left = find_leaf(t[0], label, path + (0,))
    return left if left is not None else find_leaf(t[1], label, path + (1,))


def cherries(t, path=()):
    if isinstance(t, int):
        return []
    if all(isinstance(x, int) for x in t):
        return [(path, t)]
    return cherries(t[0], path + (0,)) + cherries(t[1], path + (1,))


def relabel(t):
    labels = iter(range(len(leaf_sides(t))))

    def walk(v):
        return next(labels) if isinstance(v, int) else (walk(v[0]), walk(v[1]))

    return walk(t)


def cao_move(t, path, cherry):
    """Cao 2014 §II marked-cherry leaf transfer, at alpha=beta=1."""
    a, b = cherry
    if path[-1] == 1:  # cherry is a right child: move its left edge
        reduced = replace(t, path, b)
        candidates = [x for x, side in leaf_sides(reduced) if x > b and side == 0]
        if candidates:
            target = candidates[0]
            graft = (a, target)
        else:
            target = [x for x, side in leaf_sides(reduced) if side == 1][-1]
            graft = (target, a)
    else:  # mirror case
        reduced = replace(t, path, a)
        candidates = [x for x, side in leaf_sides(reduced) if x < a and side == 1]
        if candidates:
            target = candidates[-1]
            graft = (target, b)
        else:
            target = [x for x, side in leaf_sides(reduced) if side == 0][0]
            graft = (b, target)
    graft_path = find_leaf(reduced, target)
    return relabel(replace(reduced, graft_path, graft)), graft_path


def assignment_search(verts, adjacency, n, seconds):
    """Exact integer feasibility formulation, solved with a stated time limit.

    x[v,c] selects a label. Each required successor of c must occur at a
    neighbor of EVERY vertex labelled c. These conditions are necessary and
    sufficient for SOME rotation-supported strongly lumpable CTMC, since one
    may select one edge per required successor at rate one, all others zero.
    The chosen multiplicities alone do not imply uniform tree stationarity.
    """
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import coo_matrix

    words = [format(i, f'0{n}b') for i in range(2**n)]
    ci = {w: i for i, w in enumerate(words)}
    k = len(words)
    row, col, data, lower, upper = [], [], [], [], []

    def add(items, lo, hi):
        r = len(lower)
        for c, value in items:
            row.append(r); col.append(c); data.append(value)
        lower.append(lo); upper.append(hi)

    for v in range(len(verts)):
        add([(v * k + c, 1) for c in range(k)], 1, 1)
    for c, w in enumerate(words):
        add([(v * k + c, 1) for v in range(len(verts))], weight(w), weight(w))
    for v in range(len(verts)):
        for c, w in enumerate(words):
            for _, dest in events(w):
                add([(v * k + c, 1)] + [(u * k + ci[dest], -1) for u in adjacency[v]], -np.inf, 0)
    matrix = coo_matrix((data, (row, col)), shape=(len(lower), len(verts) * k)).tocsc()
    result = milp(np.zeros(len(verts) * k), integrality=np.ones(len(verts) * k),
                  bounds=Bounds(0, 1), constraints=LinearConstraint(matrix, lower, upper),
                  options={'time_limit': seconds})
    out = {'status': int(result.status), 'message': result.message, 'time_limit_seconds': seconds,
           'variables': len(verts) * k, 'constraints': len(lower), 'requires_uniform_tree_stationarity': False}
    if result.x is not None:
        labels = [words[int(np.argmax(result.x[v*k:(v+1)*k]))] for v in range(len(verts))]
        assert Counter(labels) == {w: weight(w) for w in words}
        assert all(any(labels[u] == dest for u in adjacency[v])
                   for v, w in enumerate(labels) for _, dest in events(w))
        out['assignment'] = labels
        out['verified_feasible'] = True
    return out


def experiment(n, search=False, seconds=20):
    verts = trees(0, n + 2)
    index = {t: i for i, t in enumerate(verts)}
    adjacency = [set() for _ in verts]
    edges = []
    for i, t in enumerate(verts):
        for dest in rotations(t):
            j = index[dest]
            adjacency[i].add(j); adjacency[j].add(i)
            edges.append((i, j))
    assert all(len(a) == n for a in adjacency)
    words = [canopy(t) for t in verts]
    counts = Counter(words)
    assert counts == {w: weight(w) for w in counts}
    z = comb(2*n + 2, n + 1) // (n + 2)
    assert len(verts) == sum(counts.values()) == z
    # Independent exact master-equation check for the matrix-ansatz weights.
    balance = Counter()
    for w, multiplicity in counts.items():
        for _, dest in events(w):
            balance[w] -= multiplicity
            balance[dest] += multiplicity
    assert all(v == 0 for v in balance.values())
    hamming = Counter(sum(a != b for a, b in zip(words[i], words[j])) for i, j in edges)
    assert set(hamming) <= {0, 1}
    missing = Counter()
    for i, w in enumerate(words):
        for kind, dest in events(w):
            if not any(words[j] == dest for j in adjacency[i]):
                missing[kind.split('_')[0]] += 1
    indegree = Counter()
    marked_targets = Counter()
    move_count = 0
    single_rotation = 0
    distance_hist = Counter()
    distances_by_kind = {kind: Counter() for kind in ('inject', 'hop', 'extract')}
    for i, t in enumerate(verts):
        actual = Counter()
        event_kinds = {dest: kind.split('_')[0] for kind, dest in events(words[i])}
        for path, cherry in cherries(t):
            dest, new_mark = cao_move(t, path, cherry)
            j = index[dest]
            marked_targets[j, new_mark] += 1
            actual[words[j]] += 1
            indegree[j] += 1
            move_count += 1
            single_rotation += j in adjacency[i]
            # Exact undirected rotation distance, using a small BFS.
            frontier, seen, distance = {i}, {i}, 0
            while j not in frontier:
                frontier = {v for u in frontier for v in adjacency[u]} - seen
                assert frontier
                seen.update(frontier)
                distance += 1
            distance_hist[distance] += 1
            distances_by_kind[event_kinds[words[j]]][distance] += 1
        assert actual == Counter(dest for _, dest in events(words[i]))
    assert all(indegree[i] == len(cherries(t)) for i, t in enumerate(verts))
    assert marked_targets == Counter((i, path) for i, t in enumerate(verts) for path, _ in cherries(t))
    assert distances_by_kind['hop'][1] == 0
    # Stationary particle current through each bond must agree.
    currents = []
    currents.append(sum(c for w, c in counts.items() if w[0] == '0'))
    currents.extend(sum(c for w, c in counts.items() if w[k:k+2] == '10') for k in range(n-1))
    currents.append(sum(c for w, c in counts.items() if w[-1] == '1'))
    assert len(set(currents)) == 1
    assert currents[0] * (4*n + 2) == z * (n + 2)
    out = {'N': n, 'trees': len(verts), 'rotation_edges': len(edges),
           'stationary_weights': dict(sorted(counts.items())), 'exact_weight_balance': True,
           'rotation_canopy_hamming_histogram': dict(sorted(hamming.items())),
           'missing_rotation_lifts_per_microstate_event': dict(missing),
           'cao_lift': {'moves': move_count, 'strong_lumpability': True,
                        'uniform_tree_stationarity': True, 'marked_tree_bijection': True,
                        'single_rotation_moves': single_rotation,
                        'rotation_distance_histogram': dict(sorted(distance_hist.items())),
                        'distance_histograms_by_kind': {kind: dict(sorted(h.items()))
                                                       for kind, h in distances_by_kind.items()},
                        'mean_rotation_distance': {'numerator': sum(d*c for d, c in distance_hist.items()),
                                                   'denominator': move_count}},
           'bond_current': {'numerator': currents[0], 'denominator': z,
                            'formula': '(N+2)/(4*N+2)'}}
    if n >= 2:
        out['capacity_obstruction'] = capacity_witness(n)
    if search:
        out['arbitrary_assignment_search'] = assignment_search(verts, adjacency, n, seconds)
        if n == 2:
            candidates = set(itertools.permutations(['00', '01', '10', '10', '11']))
            feasible = [labels for labels in candidates if all(
                any(labels[u] == dest for u in adjacency[v])
                for v, w in enumerate(labels) for _, dest in events(w))]
            assert len(candidates) == 60 and not feasible
            out['arbitrary_assignment_search']['independent_brute_force'] = {
                'assignments': len(candidates), 'feasible': len(feasible)}
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', action='store_true')
    parser.add_argument('--seconds', type=float, default=20)
    parser.add_argument('--min-sites', type=int, default=2)
    parser.add_argument('--max-sites', type=int, default=5)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('tasep_tamari_results.json'))
    args = parser.parse_args()
    if args.min_sites < 1 or args.max_sites < args.min_sites:
        parser.error('require 1 <= min-sites <= max-sites')
    results = []
    for n in range(args.min_sites, args.max_sites + 1):
        result = experiment(n, args.search, args.seconds)
        results.append(result)
        print(json.dumps(result), flush=True)
        args.output.write_text(json.dumps(results, indent=2) + '\n')
