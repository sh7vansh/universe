"""Variance-matched D1Q5 experiment: constant, Cao, and shuffled baths.

Run from the repository root:
uv run --python 3.12 --with numpy --with scipy --with matplotlib python useless_research/Economics/kinetic_cao_thermostat.py

This measures centered kinetic innovations at tau=1 and u=0. It does not
price options or assert a risk-neutral price law. See the companion notes.
"""

import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.linalg import expm

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

from kinetic_options_v2 import C, W, KineticLattice, equilibrium_populations

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'math_project'/'experiments'))
from tasep_rotation_noise import build
from tasep_tamari import canopy, trees


HORIZONS = np.asarray([1, 2, 4, 8, 16, 32, 64, 128])
CASES = ('constant', 'correlated', 'shuffled')


def make_bath(sites=5, clock=0.05):
    q, src, dst, rewards, rates, _, _ = build(sites)
    words = [canopy(t) for t in trees(0, sites+2)]
    boundary = np.asarray([sum(a != b for a, b in zip(words[i], words[j])) == 1
                           for i, j in zip(src, dst)])
    excess = rewards[:, 0]-np.where(boundary, 1, 2)
    assert np.min(excess) >= 0
    activity = np.bincount(src, weights=excess, minlength=q.shape[0])
    mean = activity.mean()
    assert np.allclose(mean, (sites-1)*(sites-2)/(2*sites+1))
    # Constitutive hypothesis: bounded, affine activity-to-temperature map.
    # Normalize in the stationary measure, never in the realized price data.
    gain = min(0.6/(mean-activity.min()), 1.6/(activity.max()-mean))
    theta = 1+gain*(activity-mean)
    assert np.allclose(theta.mean(), 1)
    assert theta.min() >= 0.4-1e-14 and theta.max() <= 2.6+1e-14
    p = expm(clock*q.toarray())
    assert p.min() >= 0
    assert np.max(np.abs(p.sum(axis=0)-1)) < 2e-14
    assert np.max(np.abs(p.sum(axis=1)-1)) < 2e-14
    offsets = np.concatenate(([0], np.cumsum(rates.astype(int))))
    assert np.array_equal(src, np.repeat(np.arange(len(rates)), rates.astype(int)))
    return {'q': q, 'p': p, 'src': src, 'dst': dst, 'rates': rates,
            'offsets': offsets, 'theta': theta, 'activity': activity,
            'gain': float(gain), 'clock': clock, 'sites': sites}


def temperature_history(bath, length, rng):
    """Exact Gillespie trajectory sampled at integer physical times.

    Uniform initial tree is already stationary; no burn-in and no event-
    biased sampling. Long holds appear repeatedly on the fixed time grid.
    """
    state = int(rng.integers(len(bath['theta'])))
    history = np.empty(length)
    cursor, physical_time, event_count = 0, 0., 0
    while cursor < length:
        physical_time += rng.exponential(1/(bath['clock']*bath['rates'][state]))
        stop = min(length, int(np.ceil(physical_time)))
        history[cursor:stop] = bath['theta'][state]
        cursor = stop
        if cursor == length:
            break
        start, end = bath['offsets'][state:state+2]
        state = int(bath['dst'][rng.integers(start, end)])
        event_count += 1
    return history, event_count


def draw_velocity(theta, uniforms):
    populations = equilibrium_populations(theta, u=0)
    cdf = np.cumsum(populations, axis=0)[:4]
    if populations.ndim == 1:
        indices = np.searchsorted(cdf, uniforms)
    else:
        indices = (uniforms[None, :] > cdf).sum(axis=0)
    return C[indices]


def acf(values, max_lag):
    centered = values-values.mean()
    length = len(values)
    size = 1 << (2*length-1).bit_length()
    spectrum = np.fft.rfft(centered, n=size)
    covariance = np.fft.irfft(spectrum*spectrum.conj(), n=size)[:max_lag+1]
    covariance /= length-np.arange(max_lag+1)
    return covariance/covariance[0]


def path_conditional_moments(theta, horizon):
    """Rao--Blackwellized moments, averaging over distinct time windows."""
    blocks = theta[:len(theta)//horizon*horizon].reshape(-1, horizon)
    v = blocks.sum(axis=1)
    fourth = 3*v*v+4*v-horizon-3*(blocks*blocks).sum(axis=1)
    return float(v.mean()), float(fourth.mean()/v.mean()**2-3)


def metrics(velocities, theta, horizons, max_lag):
    variance = float(np.var(velocities))
    kurtosis, rb_kurtosis = [], []
    for horizon in horizons:
        count = len(velocities)//horizon
        aggregated = velocities[:count*horizon].reshape(count, horizon).sum(axis=1)
        centered = aggregated-aggregated.mean()
        kurtosis.append(float(np.mean(centered**4)/np.mean(centered**2)**2-3))
        if np.isscalar(theta):
            rb_kurtosis.append(0.)  # constant theta=1 in this experiment
        else:
            rb_kurtosis.append(path_conditional_moments(theta, int(horizon))[1])
    return {'variance': variance, 'mean': float(velocities.mean()),
            'squared_return_acf': acf(velocities**2, max_lag),
            'return_acf': acf(velocities, max_lag),
            'excess_kurtosis': np.asarray(kurtosis),
            'conditional_moment_kurtosis': np.asarray(rb_kurtosis)}


def exact_moments(p, theta, max_horizon):
    """Joint bath/return moment propagation, independent of the covariance sum."""
    pi = np.full(len(theta), 1/len(theta))
    populations = equilibrium_populations(theta, 0)
    fourth_step = C**4 @ populations
    second_step = C**2 @ populations
    m2, m4 = np.zeros(len(theta)), np.zeros(len(theta))
    output = []
    for h in range(1, max_horizon+1):
        m4 = (m4+6*m2*second_step+pi*fourth_step) @ p
        m2 = (m2+pi*second_step) @ p
        output.append(float(m4.sum()/m2.sum()**2-3))
        assert abs(m2.sum()-h) < 2e-10
    return np.asarray(output)


def exact_predictions(bath, horizons, max_lag):
    theta, p = bath['theta'], bath['p']
    centered = theta-1
    # Also bound the finite-record shuffle artifact using the whole covariance
    # sum out to a much longer lag; the reported experiment uses long records.
    length = max(4096, int(max(horizons)), max_lag+1)
    vector = centered.copy()
    covariance = []
    for _ in range(length):
        covariance.append(float(centered @ vector/len(theta)))
        vector = p @ vector
    covariance = np.asarray(covariance)
    exact_kurtosis = []
    for horizon in horizons:
        lags = np.arange(1, horizon)
        exact_kurtosis.append(float(6*np.sum((horizon-lags)*covariance[lags])/horizon**2))
    propagated = exact_moments(p, theta, int(max(horizons)))
    assert np.allclose(propagated[horizons-1], exact_kurtosis, atol=5e-11)
    iid = np.full_like(p, 1/len(theta))
    assert np.max(np.abs(exact_moments(iid, theta, int(max(horizons))))) < 5e-11
    frozen = exact_moments(np.eye(len(theta)), theta, int(max(horizons)))
    h = np.arange(1, int(max(horizons))+1)
    assert np.allclose(frozen, 3*np.var(theta)*(1-1/h), atol=5e-11)
    return {'theta_covariance': covariance[:max_lag+1].tolist(),
            'squared_return_acf': np.concatenate(([1.], covariance[1:max_lag+1]/2)).tolist(),
            'excess_kurtosis': exact_kurtosis,
            'iid_excess_kurtosis': [0.]*len(horizons),
            'integrated_theta_covariance': float(np.sum(covariance[1:])),
            'theta_correlation_time_in_steps': float(0.5+np.sum(covariance[1:])/covariance[0]),
            'last_covariance_used_in_sum': float(covariance[-1])}


def shuffled_predictions(bath, record_length, horizons):
    """Account for random record means in the actual finite permutation.

    This is the unconditional covariance of two distinct shuffled slots.
    Conditional on one fixed record, centering at its own mean instead
    gives negative covariance. These are different conditioning conventions.
    """
    p, theta = bath['p'], bath['theta']
    size = len(theta)
    a = p-np.full_like(p, 1/size)
    centered = theta-theta.mean()
    resolvent = np.eye(size)-a
    inverse_once = np.linalg.solve(resolvent, centered)
    tail = np.linalg.matrix_power(a, record_length) @ centered
    inverse_twice = np.linalg.solve(resolvent, np.linalg.solve(resolvent, centered-tail))
    weighted_covariance_sum = centered @ (record_length*(a @ inverse_once)-a @ inverse_twice)/size
    covariance = float(2*weighted_covariance_sum/(record_length*(record_length-1)))
    return {'covariance_between_distinct_shuffled_temperatures': covariance,
            'excess_kurtosis': [float(3*(h-1)*covariance/h) for h in horizons],
            'squared_return_acf_positive_lags': covariance/2}


def verify_engine():
    theta = np.linspace(0.4, 2.6, 101)
    populations = equilibrium_populations(theta, 0)
    assert np.allclose(populations.sum(axis=0), 1)
    assert np.allclose(C @ populations, 0)
    assert np.allclose(C**2 @ populations, theta)
    assert np.allclose(C**4 @ populations, 4*theta-1)
    # A nontrivial two-temperature mixture has exactly the reference W.
    assert np.allclose(equilibrium_populations(np.asarray([0.5, 1.5])).mean(axis=1), W)
    for invalid in (0.2, 3.1):
        try:
            equilibrium_populations(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError('unrealisable bath accepted')
    schedule = 1+0.5*np.sin(np.arange(40)/5)
    lat = KineticLattice(0.14, 40/252, 0.03, 40, tau=1)
    density = lat.evolve(temperature_schedule=schedule)
    u = (lat.r-0.5*lat.sigma0**2*schedule)*lat.dt/lat.dx
    steps = equilibrium_populations(schedule, u)
    convolved = np.asarray([1.])
    for k in range(len(schedule)):
        convolved = np.convolve(convolved, steps[[4, 2, 0, 1, 3], k])
    expected = np.zeros_like(density)
    expected[lat.c0-2*lat.N:lat.c0+2*lat.N+1] = convolved
    assert np.max(np.abs(density-expected)) < 5e-15
    assert abs(lat.mass-1) < 1e-13
    static = KineticLattice(0.14, 0.1, 0.03, 40, tau=1)
    temporal = KineticLattice(0.14, 0.1, 0.03, 40, tau=1)
    assert np.allclose(static.evolve(), temporal.evolve(temperature_schedule=np.ones(40)), atol=1e-15)
    # Preserve the v2 static-temperature pricing validation at tau=1.
    from kinetic_options_v2 import bs_call
    flat = KineticLattice(0.14, 0.15, 0.06, 600, tau=1)
    flat.evolve()
    strikes = 25000*np.asarray([0.95, 1., 1.05])
    call_error = float(np.max(np.abs(flat.calls(25000, strikes)-bs_call(25000, strikes, .15, .06, .14))))
    assert call_error < 0.2
    return {'equilibrium_moments': True, 'realisability_rejections': True,
            'dynamic_density_convolution_max_error': float(np.max(np.abs(density-expected))),
            'dynamic_density_mass': lat.mass, 'static_schedule_equivalence': True,
            'static_pricing_call_error_rupees': call_error}


def summarize(values):
    values = np.asarray(values)
    return {'mean': np.mean(values, axis=0).tolist(),
            'standard_error': (np.std(values, axis=0, ddof=1)/np.sqrt(len(values))).tolist()}


def run(batches=16, length=262144, seed=20261111):
    started = time.monotonic()
    checks = verify_engine()
    bath = make_bath()
    max_lag = 128
    theory = exact_predictions(bath, HORIZONS, max_lag)
    data = {case: [] for case in CASES}
    temp_data = []
    example = None
    for batch, sequence in enumerate(np.random.SeedSequence(seed).spawn(batches)):
        temperature_seed, shuffle_seed, velocity_seed = sequence.spawn(3)
        theta, events_count = temperature_history(bath, length, np.random.default_rng(temperature_seed))
        shuffled = np.random.default_rng(shuffle_seed).permutation(theta)
        uniforms = np.random.default_rng(velocity_seed).random(length)
        for case, schedule in (('constant', 1.), ('correlated', theta), ('shuffled', shuffled)):
            velocities = draw_velocity(schedule, uniforms)
            data[case].append(metrics(velocities, schedule, HORIZONS, max_lag))
        temp_data.append({'mean': float(theta.mean()), 'variance': float(theta.var()),
                          'events': events_count, 'acf': acf(theta, max_lag)})
        if example is None:
            example = {'correlated_theta': theta[:2048].tolist(),
                       'shuffled_theta': shuffled[:2048].tolist()}
        print(f'batch {batch+1}/{batches}', flush=True)
    summary = {case: {key: summarize([row[key] for row in rows]) for key in rows[0]}
               for case, rows in data.items()}
    paired = {key: summarize([a[key]-b[key] for a, b in zip(data['correlated'], data['shuffled'])])
              for key in ('excess_kurtosis', 'squared_return_acf', 'variance')}
    # Analytically all cases have variance 1, not fitted from the return samples.
    sampling_checks = {}
    for case in CASES:
        value = summary[case]['variance']
        sampling_checks[case] = abs(value['mean']-1) < 6*value['standard_error']+0.003
    lag = 1
    difference = paired['squared_return_acf']
    acf_z = float(difference['mean'][lag]/difference['standard_error'][lag])
    middle = list(HORIZONS).index(16)
    difference = paired['excess_kurtosis']
    kurt_z = float(difference['mean'][middle]/difference['standard_error'][middle])
    assert theory['excess_kurtosis'][middle] > 0
    result = {'configuration': {'sites': bath['sites'], 'states': len(bath['theta']),
                'clock_per_step': bath['clock'], 'batches': batches, 'steps_per_batch': length,
                'total_increments_per_case': batches*length, 'seed': seed,
                'tau': 1., 'drift_u': 0., 'reference_annual_sigma': .14, 'dt_years': 1/252,
                'price_increment_scale': .14/np.sqrt(252), 'variance_matching': 'analytic E_theta=1; no return rescaling',
                'target_one_step_variance': .14**2/252,
                'temperature_min': float(bath['theta'].min()), 'temperature_max': float(bath['theta'].max()),
                'temperature_mean': float(bath['theta'].mean()), 'temperature_variance': float(bath['theta'].var()),
                'activity_mean': float(bath['activity'].mean()), 'activity_gain': bath['gain']},
              'horizons': HORIZONS.tolist(), 'lags': list(range(max_lag+1)),
              'exact_theory': theory, 'simulation': summary,
              'finite_record_shuffled_theory': shuffled_predictions(bath, length, HORIZONS),
              'paired_correlated_minus_shuffled': paired,
              'temperature_simulation': {key: summarize([x[key] for x in temp_data]) for key in ('mean', 'variance', 'events', 'acf')},
              'sampling_checks': {'variance_consistent': sampling_checks,
                                  'paired_squared_acf_lag_one_standard_errors': acf_z,
                                  'paired_kurtosis_horizon_16_standard_errors': kurt_z},
              'example': example, 'engine_checks': checks,
              'seconds': time.monotonic()-started}
    return result


def plot(result, path):
    colors = {'constant': '#777777', 'correlated': '#23628c', 'shuffled': '#b46b32'}
    labels = {'constant': 'Constant bath', 'correlated': 'Correlated Cao bath', 'shuffled': 'Shuffled bath'}
    plt.rcParams.update({'axes.spines.top': False, 'axes.spines.right': False, 'font.size': 10, 'svg.fonttype': 'none'})
    fig, axes = plt.subplots(2, 2, figsize=(11, 8), layout='constrained')
    example = result['example']
    ax = axes[0, 0]
    ax.plot(example['correlated_theta'][:512], color=colors['correlated'], lw=1.4, label='Correlated')
    ax.plot(example['shuffled_theta'][:512], color=colors['shuffled'], lw=.7, alpha=.55, label='Shuffled')
    ax.axhline(1, color=colors['constant'], ls='--', label='Constant')
    ax.set(xlabel='Kinetic time step', ylabel='Temperature', title='A  Correlated and shuffled temperature histories')
    ax.legend(frameon=False, fontsize=8)
    ax = axes[0, 1]
    for case in CASES:
        row = result['simulation'][case]['squared_return_acf']
        ax.plot(result['lags'][1:], row['mean'][1:], color=colors[case], label=labels[case])
    ax.plot(result['lags'][1:], result['exact_theory']['squared_return_acf'][1:], '--', color='black', lw=1.2, label='Exact correlated prediction')
    ax.axhline(0, color='#aaaaaa', lw=.7)
    ax.set(xlabel='Lag in kinetic time steps', ylabel='Squared-innovation autocorrelation', title='B  Volatility memory survives')
    ax.legend(frameon=False, fontsize=8)
    ax = axes[1, 0]
    for case in CASES:
        row = result['simulation'][case]['excess_kurtosis']
        ax.errorbar(result['horizons'], row['mean'], yerr=2*np.asarray(row['standard_error']),
                    fmt='o-', color=colors[case], ms=4, capsize=2, label=labels[case])
    ax.plot(result['horizons'], result['exact_theory']['excess_kurtosis'], '--', color='black', label='Exact correlated prediction')
    ax.set_xscale('log', base=2)
    ax.set(xlabel='Aggregation horizon in steps', ylabel='Excess kurtosis', title='C  Temperature memory changes aggregate tails')
    ax.axhline(0, color='#aaaaaa', lw=.7)
    ax.legend(frameon=False, fontsize=8)
    ax = axes[1, 1]
    for case in CASES:
        row = result['simulation'][case]['return_acf']
        ax.plot(result['lags'][1:33], row['mean'][1:33], color=colors[case], label=labels[case])
    ax.axhline(0, color='black', ls='--', lw=1)
    ax.set(xlabel='Lag in kinetic time steps', ylabel='Signed-innovation autocorrelation', title='D  No directional predictability was added')
    ax.legend(frameon=False, fontsize=8)
    for ax in axes.flat:
        ax.grid(axis='y', alpha=.2)
    fig.suptitle('D1Q5 thermostat comparison: identical one-step laws and matched variance', fontsize=13)
    fig.savefig(path.with_suffix('.png'), dpi=180)
    fig.savefig(path.with_suffix('.svg'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batches', type=int, default=16)
    parser.add_argument('--steps', type=int, default=262144)
    parser.add_argument('--seed', type=int, default=20261111)
    args = parser.parse_args()
    if args.batches < 2 or args.steps < 1024:
        parser.error('require at least two batches and 1024 steps per batch')
    output = run(args.batches, args.steps, args.seed)
    path = Path(__file__).with_name('kinetic_cao_thermostat_results.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    plot(output, Path(__file__).with_name('kinetic_cao_thermostat'))
    print(json.dumps({'configuration': output['configuration'], 'engine_checks': output['engine_checks'],
                      'exact_kurtosis': output['exact_theory']['excess_kurtosis'], 'seconds': output['seconds']}), flush=True)
