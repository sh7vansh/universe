"""Stationary physical-time noise and jump-index memory of Cao tree moves.

Run from repo root:
uv run --python 3.12 --with numpy --with scipy python math_project/experiments/tasep_rotation_noise.py

All original cherry clocks have rate one. No clock is assigned to the
elementary rotations used to measure jump distance.
"""

import argparse
from collections import deque
from fractions import Fraction
import json
from math import factorial, gcd
from pathlib import Path
import time

import numpy as np
from scipy import sparse
from scipy.sparse.csgraph import connected_components
from scipy.sparse.linalg import eigs, expm_multiply, splu

from tasep_tamari import cao_move, canopy, cherries, events, trees, weight
from tasep_rotation_distances import distance_formula, moment_formulas


def build(n):
    vertices = trees(0, n+2)
    index = {t: i for i, t in enumerate(vertices)}
    src, dst, rewards = [], [], []
    phase = []
    for i, t in enumerate(vertices):
        word = canopy(t)
        phase.append(sum((k+1)*int(x) for k, x in enumerate(word)) % (n+1))
        kind = {dest: name for name, dest in events(word)}
        for mark, cherry in cherries(t):
            target, _ = cao_move(t, mark, cherry)
            src.append(i); dst.append(index[target])
            rewards.append((distance_formula(t, mark), 1, int(kind[canopy(target)] == 'inject')))
    src = np.asarray(src); dst = np.asarray(dst)
    rewards = np.asarray(rewards, dtype=float)
    size = len(vertices)
    rate = np.bincount(src, minlength=size).astype(float)
    adjacency = sparse.csr_matrix((np.ones(len(src)), (src, dst)), shape=(size, size))
    q = adjacency-sparse.diags(rate)
    assert np.max(np.abs(np.asarray(q.sum(axis=0)).ravel())) == 0
    assert connected_components(adjacency, directed=True, connection='strong')[0] == 1
    phase = np.asarray(phase)
    assert np.all((phase[dst]-phase[src]) % (n+1) == 1)
    # Standard cycle-length gcd, independent of the phase-derived bound.
    level = np.full(size, -1, dtype=int)
    level[0] = 0
    queue = deque([0])
    while queue:
        v = queue.popleft()
        for u in adjacency.indices[adjacency.indptr[v]:adjacency.indptr[v+1]]:
            if level[u] < 0:
                level[u] = level[v]+1; queue.append(u)
    period = 0
    for i, j in zip(src, dst):
        period = gcd(period, int(level[i]+1-level[j]))
    assert period == n+1
    return q, src, dst, rewards, rate, phase, period


def poisson_statistics(q, src, dst, rewards, pi):
    """Row-generator Poisson equation and martingale covariance matrix."""
    size, count = rewards.shape[0], rewards.shape[1]
    vertices = q.shape[0]
    outgoing = np.column_stack([np.bincount(src, weights=rewards[:, k], minlength=vertices)
                                for k in range(count)])
    uniform = np.all(pi == pi[0])
    # Sum the integer unit-rate rewards before dividing. A long floating
    # dot product otherwise creates a tiny stationarity defect, magnified
    # by grounding a nearly singular generator at larger tree counts.
    means = outgoing.sum(axis=0)/vertices if uniform else pi @ outgoing
    rhs = means-outgoing
    correctors = np.zeros((vertices, count))
    # Grounding h[0]=0 removes the nullspace; center afterwards.
    lu = splu(q[1:, 1:].tocsc())
    correctors[1:] = lu.solve(rhs[1:])
    correction_rhs = rhs[1:]-q[1:, 1:] @ correctors[1:]
    correctors[1:] += lu.solve(correction_rhs)
    correctors -= correctors.mean(axis=0) if uniform else pi @ correctors
    residual = np.max(np.abs(q @ correctors-rhs))
    assert residual < 2e-8
    increments = rewards+correctors[dst]-correctors[src]
    event_weight = pi[src]
    covariance = increments.T @ (event_weight[:, None]*increments)
    shot = rewards.T @ (event_weight[:, None]*rewards)
    insertion = rewards.T @ (event_weight[:, None]*correctors[dst])
    assert np.allclose(covariance, shot+insertion+insertion.T, atol=2e-8, rtol=2e-8)
    assert np.min(np.linalg.eigvalsh(covariance)) > -2e-8
    return {'means': means, 'covariance': covariance, 'shot': shot,
            'correctors': correctors, 'outgoing': outgoing,
            'residual': float(residual), 'factor': lu}


def macro_statistics(n):
    words = [format(i, f'0{n}b') for i in range(2**n)]
    index = {w: i for i, w in enumerate(words)}
    src, dst, rewards = [], [], []
    for i, word in enumerate(words):
        for kind, dest in events(word):
            src.append(i); dst.append(index[dest])
            rewards.append((1, int(kind == 'inject')))
    src = np.asarray(src); dst = np.asarray(dst)
    rewards = np.asarray(rewards, dtype=float)
    rates = np.bincount(src, minlength=len(words)).astype(float)
    q = sparse.csr_matrix((np.ones(len(src)), (src, dst)), shape=(len(words), len(words))) - sparse.diags(rates)
    pi = np.asarray([weight(w) for w in words], dtype=float)
    pi /= pi.sum()
    assert np.max(np.abs(pi @ q)) < 1e-12
    stats = poisson_statistics(q, src, dst, rewards, pi)
    return {'means': stats['means'], 'covariance': stats['covariance']}


def exact_current_noise(n):
    """Unit-boundary open TASEP current Var(Q_t)/t; source in theory note.

    Antal--Krapivsky--Mallick 2007 Eq32 has Var/(2t), hence the factor two
    here. Their spider leg count is N+1, not the number N of TASEP sites.
    """
    numerator = 3*factorial(4*n+1)*(factorial(n)*factorial(n+2))**2
    denominator = 2*factorial(2*n+1)**3*factorial(2*n+3)
    return Fraction(numerator, denominator)


def fraction_solve(matrix, rhs):
    a = [[Fraction(x) for x in row]+[Fraction(y)] for row, y in zip(matrix, rhs)]
    n = len(a)
    for col in range(n):
        pivot = next(i for i in range(col, n) if a[i][col])
        a[col], a[pivot] = a[pivot], a[col]
        scale = a[col][col]
        a[col] = [v/scale for v in a[col]]
        for i in range(n):
            if i == col or not a[i][col]:
                continue
            scale = a[i][col]
            a[i] = [v-scale*w for v, w in zip(a[i], a[col])]
    return [row[-1] for row in a]


def exact_small(q, src, dst, rewards, numerical):
    size = q.shape[0]
    matrix = q.toarray().astype(int).tolist()
    means = [sum(int(r[k]) for r in rewards)*Fraction(1, size) for k in range(3)]
    correctors = []
    for k in range(3):
        outgoing = [0]*size
        for i, reward in zip(src, rewards):
            outgoing[i] += int(reward[k])
        rhs = [means[k]-x for x in outgoing]
        grounded = fraction_solve([row[1:] for row in matrix[1:]], rhs[1:])
        h = [Fraction(0)]+grounded
        center = sum(h)/size
        correctors.append([x-center for x in h])
        assert all(sum(Fraction(matrix[i][j])*correctors[k][j] for j in range(size)) == rhs[i]
                   for i in range(size))
    covariance = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for i, j, reward in zip(src, dst, rewards):
        jump = [int(reward[k])+correctors[k][j]-correctors[k][i] for k in range(3)]
        for a in range(3):
            for b in range(3):
                covariance[a][b] += jump[a]*jump[b]/size
    assert np.allclose(np.asarray(covariance, dtype=float), numerical, atol=1e-9)
    return {'means': [str(x) for x in means],
            'covariance': [[str(x) for x in row] for row in covariance]}


def tilted_check(q, src, dst, rewards, means, covariance, step=0.002):
    """Independent SCGF finite differences, keeping escape diagonal untilted."""
    size = q.shape[0]
    diagonal = q.diagonal()

    def eigenvalue(direction, value):
        weights = np.exp(value*(rewards @ direction))
        tilted = sparse.csr_matrix((weights, (src, dst)), shape=q.shape)+sparse.diags(diagonal)
        eig = np.linalg.eigvals(tilted.toarray()) if size <= 200 else eigs(tilted, k=1, which='LR', return_eigenvectors=False, tol=1e-11)
        return float(max(eig.real))

    checks = []
    for direction in (np.asarray([1., 0., 0.]), np.asarray([0., 0., 1.]), np.asarray([1., 0., 1.])):
        expected_first = float(direction @ means)
        expected_second = float(direction @ covariance @ direction)
        estimates = []
        for h in (step, step/2):
            plus = eigenvalue(direction, h); minus = eigenvalue(direction, -h)
            first = (plus-minus)/(2*h)
            second = (plus+minus)/(h*h)
            assert abs(first-expected_first) < 0.0003*(1+abs(expected_first))
            assert abs(second-expected_second) < 0.001*(1+abs(expected_second))
            estimates.append({'step': h, 'first': first, 'second': second})
        checks.append({'direction': direction.tolist(), 'first_expected': expected_first,
                       'second_expected': expected_second, 'estimates': estimates})
    return checks


def threshold_statistics(threshold, src, dst, rewards, stats, size):
    """Check clustering of genuinely larger marks, independent of the clock."""
    marks = (rewards[:, 0] >= threshold).astype(float)
    probability = float(np.mean(marks))
    if probability == 0:
        return {'distance_threshold': threshold, 'probability_per_event': 0.}
    drift = float(np.sum(marks)/size)
    outgoing = np.bincount(src, weights=marks, minlength=size)
    h = np.zeros(size)
    h[1:] = stats['factor'].solve((drift-outgoing)[1:])
    h -= np.mean(h)
    corrected = marks+h[dst]-h[src]
    variance = float(np.sum(corrected**2)/size)
    h_mark = h-probability*stats['correctors'][:, 1]
    corrected_mark = marks-probability+h_mark[dst]-h_mark[src]
    long_mark_variance = float(np.mean(corrected_mark**2))
    return {'distance_threshold': threshold, 'probability_per_event': probability,
            'count_mean_per_time': drift, 'count_variance_per_time': variance,
            'physical_count_noise_ratio_to_poisson': variance/drift,
            'centered_indicator_variance_per_event_long_time': long_mark_variance,
            'indicator_noise_ratio_to_iid': long_mark_variance/(probability*(1-probability))}


def analyze(n, lag_count=400, time_points=60):
    started = time.monotonic()
    q, src, dst, rewards, rates, phase, period = build(n)
    size = q.shape[0]
    pi = np.full(size, 1/size)
    stats = poisson_statistics(q, src, dst, rewards, pi)
    means, cov, shot = stats['means'], stats['covariance'], stats['shot']
    correctors, outgoing = stats['correctors'], stats['outgoing']
    event_rate = means[1]
    mark_mean = means[0]/event_rate
    mark_variance = shot[0, 0]/event_rate-mark_mean**2
    expected_mean, expected_variance = moment_formulas(n)
    assert np.allclose((mark_mean, mark_variance), (float(expected_mean), float(expected_variance)))
    assert abs(means[0]-(4*n*n-2*n+4)/(4*n+2)) < 1e-10
    macro = macro_statistics(n)
    assert np.allclose(means[1:], macro['means'], atol=1e-9)
    assert np.allclose(cov[1:, 1:], macro['covariance'], atol=2e-8)
    assert np.allclose(cov[:, 1], (n+1)*cov[:, 2], atol=2e-8)

    # Event-index centered marks, separated from the deterministic phase.
    p = sparse.diags(1/rates) @ (q+sparse.diags(rates))
    centered_mark = rewards[:, 0]-mark_mean
    expected_centered = outgoing[:, 0]/rates-mark_mean
    incoming_centered = np.bincount(dst, weights=centered_mark, minlength=size)/len(src)
    conditional_phase_mean = np.bincount(phase[src], weights=rewards[:, 0], minlength=n+1)
    phase_event_counts = np.bincount(phase[src], minlength=n+1)
    assert np.max(phase_event_counts) == np.min(phase_event_counts)
    conditional_phase_mean /= phase_event_counts
    phase_mean_centered = conditional_phase_mean-mark_mean
    phase_variance = float(np.mean(phase_mean_centered**2))
    mark_correlations = []
    vector = expected_centered.copy()
    for lag in range(1, lag_count+1):
        value = float(incoming_centered @ vector)
        periodic = float(np.mean(phase_mean_centered*np.roll(phase_mean_centered, -lag)))
        mark_correlations.append({'lag': lag, 'covariance': value, 'periodic_part': periodic,
                                  'transient_part': value-periodic})
        vector = p @ vector
    residual_direction = np.asarray([1., -mark_mean, 0.])
    long_mark_variance = float(residual_direction @ cov @ residual_direction/event_rate)
    assert long_mark_variance > -1e-8
    discrete_corrector = correctors[:, 0]-mark_mean*correctors[:, 1]
    assert np.max(np.abs((sparse.eye(size)-p) @ discrete_corrector-expected_centered)) < 2e-8
    direct_mark_increments = centered_mark+discrete_corrector[dst]-discrete_corrector[src]
    assert np.allclose(long_mark_variance, np.mean(direct_mark_increments**2), atol=2e-8)
    transient_variance = max(0., mark_variance-phase_variance)
    transient_green_kubo = transient_variance+2*sum(c['transient_part'] for c in mark_correlations)

    # Physical-time covariance of the jump flux, excluding its delta spike.
    b = outgoing[:, 0]-means[0]
    incoming_cost = np.bincount(dst, weights=rewards[:, 0], minlength=size)-means[0]
    integrated_flux = float(incoming_cost @ correctors[:, 0]/size)
    assert np.allclose(cov[0, 0], shot[0, 0]+2*integrated_flux, atol=2e-8)
    state_rate_variance = float(b @ b/size)
    state_tau = float(b @ correctors[:, 0]/size/state_rate_variance) if state_rate_variance > 1e-12 else None
    # A finite curve for inspection; the integral above is from the Poisson solve.
    horizon = max(10., 8*state_tau) if state_tau is not None else 10.
    times = np.linspace(0, horizon, time_points)
    curve = expm_multiply(q, b, start=0, stop=horizon, num=time_points, endpoint=True)
    time_correlations = [{'time': float(t), 'flux_covariance': float(incoming_cost @ x/size),
                          'state_rate_covariance': float(b @ x/size)} for t, x in zip(times, curve)]
    cost_current_corr = float(cov[0, 2]/np.sqrt(cov[0, 0]*cov[2, 2]))
    optimal_current_coeff = float(cov[0, 2]/cov[2, 2])
    residual_current_noise = float(cov[0, 0]-cov[0, 2]**2/cov[2, 2])
    current_benchmark = exact_current_noise(n)
    assert np.allclose(cov[2, 2], float(current_benchmark), atol=2e-8, rtol=2e-8)

    out = {'N': n, 'trees': size, 'events': len(src), 'jump_chain_period': period,
           'observable_order': ['rotation_cost', 'event_count', 'injection_current'],
           'mean_rates': means.tolist(), 'asymptotic_covariance_per_time': cov.tolist(),
           'compound_poisson_shot_covariance': shot.tolist(),
           'physical_cost_noise_ratio_to_shot': float(cov[0, 0]/shot[0, 0]),
           'integrated_cost_flux_correlation': integrated_flux,
           'cost_current_correlation': cost_current_corr,
           'optimal_current_coefficient': optimal_current_coeff,
           'cost_noise_after_current_regression': residual_current_noise,
           'state_cost_rate_correlation_time': state_tau,
           'mark_mean': mark_mean, 'mark_variance': mark_variance,
           'mark_variance_per_event_long_time': max(0., long_mark_variance),
           'mark_noise_ratio_to_iid': float(long_mark_variance/mark_variance) if mark_variance > 1e-12 else None,
           'mark_transient_integrated_correlation_steps': float(long_mark_variance/(2*transient_variance))
               if transient_variance > 1e-12 else None,
           'phase_conditional_mark_means': conditional_phase_mean.tolist(),
           'phase_variance': phase_variance, 'transient_mark_variance': transient_variance,
           'finite_lag_green_kubo': transient_green_kubo,
           'mark_lag_count': lag_count, 'mark_correlations': mark_correlations,
           'time_correlations': time_correlations,
           'exact_current_noise_benchmark': str(current_benchmark),
           'poisson_residual': stats['residual']}
    out['large_event_statistics'] = threshold_statistics(4, src, dst, rewards, stats, size)
    if n <= 3:
        out['exact_rational'] = exact_small(q, src, dst, rewards, cov)
    if n <= 5:
        out['tilted_generator_checks'] = tilted_check(q, src, dst, rewards, means, cov)
    out['seconds'] = time.monotonic()-started
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-sites', type=int, default=8)
    parser.add_argument('--lags', type=int, default=400)
    args = parser.parse_args()
    results = []
    output = Path(__file__).with_name('tasep_rotation_noise_results.json')
    for n in range(1, args.max_sites+1):
        result = analyze(n, args.lags)
        results.append(result)
        output.write_text(json.dumps(results, indent=2)+'\n')
        compact = {k: result[k] for k in ('N', 'trees', 'mean_rates', 'physical_cost_noise_ratio_to_shot',
                   'mark_noise_ratio_to_iid', 'cost_current_correlation', 'cost_noise_after_current_regression',
                   'state_cost_rate_correlation_time', 'seconds')}
        compact['cost_noise_per_time'] = result['asymptotic_covariance_per_time'][0][0]
        compact['current_noise_per_time'] = result['asymptotic_covariance_per_time'][2][2]
        print(json.dumps(compact), flush=True)
