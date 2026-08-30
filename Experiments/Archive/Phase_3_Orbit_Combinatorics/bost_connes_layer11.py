import numpy as np
from sympy import primerange, mobius
import math

class BostConnesLayer11:
    def __init__(self, N_max=200):
        self.N_max = N_max
        self.dim = N_max

    def mu(self, n):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            if n * k <= self.dim:
                mat[n * k - 1, k - 1] = 1.0
        return mat
        
    def mu_star(self, n):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            if k % n == 0:
                mat[(k // n) - 1, k - 1] = 1.0
        return mat

    def F_s_operator(self, s_val, primes):
        F = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for p in primes:
            F += (p ** (-s_val)) * self.mu(p)
        return F

    def B_operator(self, primes):
        B = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for p in primes:
            B += self.mu_star(p)
        return B

def moebius_inversion_trace(matrix):
    """
    Extracts the orbit coefficients c_n from the diagonal of the matrix.
    If diag = sum c_n P_n, then diag[k] = sum_{n|k} c_n.
    By Moebius inversion: c_n = sum_{d|n} mu(n/d) diag[d].
    Returns the sum of all c_n for n >= 2.
    """
    N = matrix.shape[0]
    diag = np.diag(matrix).real
    c = np.zeros(N + 1)
    
    for n in range(2, N + 1):
        c_n = 0
        for d in range(1, n + 1):
            if n % d == 0:
                # index in matrix is d-1
                c_n += mobius(n // d) * diag[d - 1]
        c[n] = c_n
        
    return c

def run_layer11(N_max=150, s_val=0.5):
    bc = BostConnesLayer11(N_max=N_max)
    primes = list(primerange(2, 20))
    
    F_s = bc.F_s_operator(s_val, primes)
    B = bc.B_operator(primes)
    
    FB = F_s @ B
    
    print(f"=== Layer 11: Orbit Trace Laboratory (N={N_max}) ===")
    print(f"Target: tau_orbit((FB)^k) ~ sum_p p^{{-ks}}")
    print(f"{'k':>2} | {'tau_matrix':>12} | {'tau_density':>12} | {'tau_orbit':>12} | {'Expected':>12}")
    print("-" * 65)
    
    for k in range(1, 5):
        FB_k = np.linalg.matrix_power(FB, k)
        
        tau_mat = np.trace(FB_k).real
        tau_den = tau_mat / N_max
        
        c = moebius_inversion_trace(FB_k)
        
        # We can sum all c_n to get the total number of primitive orbits traced out.
        # Let's sum c_n for prime powers n = p^k. 
        # Actually, let's just sum all c_n for n >= 2 to see the total orbit trace.
        tau_orb = np.sum(c[2:])
        
        expected = sum((p ** (-k * s_val)) for p in primes)
        
        print(f"{k:2d} | {tau_mat:12.4f} | {tau_den:12.4f} | {tau_orb:12.4f} | {expected:12.4f}")
        
    print("\nDetailed c_n extracted from Moebius Inversion for (FB)^1:")
    c1 = moebius_inversion_trace(FB)
    for n in range(2, 11):
        print(f"  n={n:2d}: c_n = {c1[n]:8.4f}")

    print("\nDetailed c_n extracted from Moebius Inversion for (FB)^2:")
    c2 = moebius_inversion_trace(np.linalg.matrix_power(FB, 2))
    for n in range(2, 11):
        print(f"  n={n:2d}: c_n = {c2[n]:8.4f}")

if __name__ == "__main__":
    run_layer11(N_max=150, s_val=1.5)
