import numpy as np
from prime_trace import construct_H_trace

N = 2000
kappa = 2.0
Phi = np.pi / 4
H = construct_H_trace(N, kappa, Phi, 'arithmetic', use_potential=False)
evals = np.linalg.eigvalsh(H)

primes = [2, 3, 5, 7, 11, 13]
print("K(t) at log(p):")
for p in primes:
    t = np.log(p)
    Z_t = np.sum(np.exp(-1j * t * evals))
    K_t = np.abs(Z_t)**2
    print(f"p={p}, t={t:.4f}, K(t)={K_t:.0f}")

print("\nK(t) at some random t:")
for t in [0.5, 1.0, 1.5, 2.0, 2.5]:
    Z_t = np.sum(np.exp(-1j * t * evals))
    K_t = np.abs(Z_t)**2
    print(f"t={t:.4f}, K(t)={K_t:.0f}")
