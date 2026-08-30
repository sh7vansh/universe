import numpy as np
from scipy.signal import find_peaks
from prime_trace import construct_H_trace

N = 2000
kappa = 2.0
Phi = np.pi / 4
H = construct_H_trace(N, kappa, Phi, 'arithmetic', use_potential=False)
evals = np.linalg.eigvalsh(H)

t_array = np.linspace(0.1, 5, 5000) 
Z_t = np.array([np.sum(np.exp(-1j * t * evals)) for t in t_array])
K_t = np.abs(Z_t)**2

# Mean of K(t) to set prominence
mean_K = np.mean(K_t)
peaks, _ = find_peaks(K_t, prominence=mean_K*0.5)

print("Top peaks in K(t):")
peak_times = t_array[peaks]
peak_vals = K_t[peaks]
sorted_idx = np.argsort(peak_vals)[::-1]
for i in sorted_idx[:15]:
    print(f"t = {peak_times[i]:.4f}, K(t) = {peak_vals[i]:.0f}")
