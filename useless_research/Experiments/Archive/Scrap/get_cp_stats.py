import numpy as np
from orbit_lab import get_primes, get_random_B, get_arithmetic_B, compute_Cp_L3_vec

kappa = 2.0
Phi = np.pi / 4
primes = get_primes(500)
num_p = len(primes)

B_rand_ensemble = np.zeros((1000, num_p, num_p))
np.random.seed(42)
for r in range(1000):
    B_rand_ensemble[r] = get_random_B(num_p)

Cp_rand_ensemble = compute_Cp_L3_vec(primes, B_rand_ensemble, kappa, Phi)
Cp_rand_mean = np.mean(Cp_rand_ensemble, axis=0)
Cp_rand_std = np.std(Cp_rand_ensemble, axis=0)

B_arith = get_arithmetic_B(primes)
Cp_arith = compute_Cp_L3_vec(primes, B_arith[np.newaxis, :, :], kappa, Phi)[0]

# Check how many primes fall outside the 2-sigma band of random
z_scores = np.abs(Cp_arith - Cp_rand_mean) / (Cp_rand_std + 1e-12)
outside_95 = np.sum(z_scores > 2.0)
outside_99 = np.sum(z_scores > 2.58)

print(f"Primes outside 95% random band: {outside_95} / {num_p} ({(outside_95/num_p)*100:.1f}%)")
print(f"Primes outside 99% random band: {outside_99} / {num_p} ({(outside_99/num_p)*100:.1f}%)")
print(f"Max Z-score: {np.max(z_scores):.2f}")

# Check scaling of |Cp_arith|
# We fit log(|Cp|) vs log(p)
fit = np.polyfit(np.log(primes), np.log(np.abs(Cp_arith) + 1e-12), 1)
print(f"Scaling |C_p| ~ p^alpha, alpha = {fit[0]:.3f}")

# Fit for Random Mean
fit_rand = np.polyfit(np.log(primes), np.log(np.abs(Cp_rand_mean) + 1e-12), 1)
print(f"Scaling |C_p, rand| ~ p^alpha, alpha = {fit_rand[0]:.3f}")

print("\nSample values:")
for i in range(10):
    print(f"p = {primes[i]:3}, Cp_arith = {Cp_arith[i]:.4f}, Cp_rand = {Cp_rand_mean[i]:.4f} +- {Cp_rand_std[i]:.4f}")

