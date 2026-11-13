"""Plot the saved finite-generator noise calculations (Matplotlib only)."""

import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


base = Path(__file__).parent
rows = json.loads((base/'tasep_rotation_noise_results.json').read_text())
sites = [r['N'] for r in rows]
blue, orange, green = '#23628c', '#ba6637', '#39745c'
plt.rcParams.update({'font.size': 10, 'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.titleweight': 'bold', 'svg.fonttype': 'none'})
fig, axes = plt.subplots(2, 2, figsize=(11, 8), layout='constrained')

ax = axes[0, 0]
ax.plot(sites, [r['asymptotic_covariance_per_time'][0][0] for r in rows], 'o-', color=blue, label='Cao dynamics')
ax.plot(sites, [r['compound_poisson_shot_covariance'][0][0] for r in rows], 's--', color=orange, label='Independent-event baseline')
ax.set(xlabel='Sites N', ylabel='Variance of accumulated cost / time', title='A  Physical-time noise')
ax.legend(frameon=False)

ax = axes[0, 1]
ax.plot(sites, [r['physical_cost_noise_ratio_to_shot'] for r in rows], 'o-', color=blue, label='Physical-time cost')
subset = [r for r in rows if r['mark_noise_ratio_to_iid'] is not None]
ax.plot([r['N'] for r in subset], [r['mark_noise_ratio_to_iid'] for r in subset], 's-', color=orange, label='Distance marks by event index')
subset = [r for r in rows if r['large_event_statistics']['probability_per_event'] > 0]
ax.plot([r['N'] for r in subset], [r['large_event_statistics']['indicator_noise_ratio_to_iid'] for r in subset], '^-', color=green, label='Indicator: distance ≥ 4, by event index')
ax.axhline(1, color='#888888', linewidth=1, linestyle=':')
ax.set(xlabel='Sites N', ylabel='Noise / corresponding independent baseline', title='B  Correlation enhancement')
ax.legend(frameon=False, fontsize=8)

ax = axes[1, 0]
for n, color in ((4, green), (7, orange), (10, blue)):
    row = next((r for r in rows if r['N'] == n), None)
    if row is None:
        continue
    correlations = row['mark_correlations'][:200]
    ax.plot([c['lag'] for c in correlations],
            [c['transient_part']/row['transient_mark_variance'] for c in correlations],
            color=color, label=f'N = {n}')
ax.axhline(0, color='#888888', linewidth=1, linestyle=':')
ax.set(xlabel='Separation in number of events', ylabel='Phase-corrected distance covariance / variance',
       title='C  Mark memory after removing cyclic phase')
ax.legend(frameon=False)

ax = axes[1, 1]
rho = np.asarray([r['cost_current_correlation'] for r in rows])
ax.plot(sites, rho, 'o-', color=blue, label='Cost–current correlation')
ax.plot(sites, 1-rho**2, 's-', color=orange, label='Residual cost-noise fraction')
ax.set(xlabel='Sites N', ylabel='Dimensionless', ylim=(-.03, 1.04), title='D  Geometric noise beyond particle current')
ax.legend(frameon=False, fontsize=8)

for ax in axes.flat:
    ax.grid(axis='y', color='#dddddd', linewidth=.5)
fig.suptitle('Cao tree lift: finite single-event moments, correlated accumulated cost', fontsize=14)
fig.savefig(base/'tasep_rotation_noise.png', dpi=180)
fig.savefig(base/'tasep_rotation_noise.svg')
print(base/'tasep_rotation_noise.png')
