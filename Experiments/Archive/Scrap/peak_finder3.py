import numpy as np
from scipy.signal import find_peaks
import matplotlib.pyplot as plt
from prime_trace import construct_H_trace

N = 2000
kappa = 2.0
Phi = np.pi / 4
H = construct_H_trace(N, kappa, Phi, 'arithmetic', use_potential=False)
evals = np.linalg.eigvalsh(H)

# Smooth density of states using Gaussian KDE
from scipy.stats import gaussian_kde
kde = gaussian_kde(evals, bw_method=0.1)

t_array = np.linspace(0.1, 10, 5000)
E_grid = np.linspace(evals.min(), evals.max(), 1000)
rho_bar = kde(E_grid) * N

Z_t_full = np.array([np.sum(np.exp(-1j * t * evals)) for t in t_array])

# Fourier transform of smooth density
dE = E_grid[1] - E_grid[0]
Z_t_smooth = np.array([np.sum(rho_bar * np.exp(-1j * t * E_grid)) * dE for t in t_array])

Z_t_osc = Z_t_full - Z_t_smooth
K_t_osc = np.abs(Z_t_osc)**2

# Find peaks
mean_K = np.mean(K_t_osc)
peaks, properties = find_peaks(K_t_osc, prominence=mean_K*1.0)

print("Top peaks in K_osc(t) for V=0 Arithmetic Flux:")
peak_times = t_array[peaks]
peak_vals = K_t_osc[peaks]
sorted_idx = np.argsort(peak_vals)[::-1]
for i in sorted_idx[:15]:
    print(f"t = {peak_times[i]:.4f}, K_osc(t) = {peak_vals[i]:.0f}")

plt.figure(figsize=(10, 4))
plt.plot(t_array, K_t_osc, 'k-', alpha=0.8)
plt.title("K_osc(t) for V=0 Arithmetic Flux")
plt.xlabel("t")
plt.ylabel("K_osc(t)")
plt.grid(True)
plt.savefig("Results_Quantum_Chaos/K_osc_v0.png")

