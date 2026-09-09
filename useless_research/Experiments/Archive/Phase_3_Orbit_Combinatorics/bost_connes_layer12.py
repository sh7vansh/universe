import numpy as np
from sympy import primerange, mobius, legendre_symbol
import scipy.linalg as la

class BostConnesLayer12:
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

def build_K(bc, primes, s_val=1.5, Phi=0.0, random_phase=False):
    K = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    odd_primes = [p for p in primes if p > 2]
    n_p = len(odd_primes)
    
    chi = np.zeros((n_p, n_p))
    if random_phase:
        np.random.seed(42)
        for i in range(n_p):
            for j in range(i+1, n_p):
                val = np.random.uniform(-1, 1)
                chi[i, j] = val
                chi[j, i] = -val
        np.random.seed(None)
    else:
        for i in range(n_p):
            for j in range(n_p):
                if i != j:
                    chi[i, j] = legendre_symbol(odd_primes[i], odd_primes[j]) - legendre_symbol(odd_primes[j], odd_primes[i])
                    
    for i, p in enumerate(odd_primes):
        for j, q in enumerate(odd_primes):
            weight = p ** (-s_val)
            if i != j:
                phase = np.exp(1j * Phi * chi[i, j])
            else:
                phase = 1.0
            
            K += weight * phase * (bc.mu(p) @ bc.mu_star(q))
    return K

def moebius_inversion_trace(matrix):
    N = matrix.shape[0]
    diag = np.diag(matrix).real
    c = np.zeros(N + 1)
    for n in range(2, N + 1):
        c_n = 0
        for d in range(1, n + 1):
            if n % d == 0:
                c_n += mobius(n // d) * diag[d - 1]
        c[n] = c_n
    return c

def exp_A_cutoff_convergence():
    print("=== A. Cutoff Convergence ===")
    primes = list(primerange(2, 20))
    s_val = 1.5
    
    print(f"{'N_max':>6} | {'c_3^(1)':>10} | {'c_3^(2)':>10} | {'c_3^(3)':>10}")
    print("-" * 45)
    
    for N_max in [100, 150, 300, 600, 1000]:
        bc = BostConnesLayer12(N_max=N_max)
        K = build_K(bc, primes, s_val=s_val, Phi=0.0)
        
        c1 = moebius_inversion_trace(K)
        c2 = moebius_inversion_trace(K @ K)
        c3 = moebius_inversion_trace(K @ K @ K)
        
        print(f"{N_max:6d} | {c1[3]:10.5f} | {c2[3]:10.5f} | {c3[3]:10.5f}")
        
    print(f"Expect | {3**(-s_val):10.5f} | {3**(-2*s_val):10.5f} | {3**(-3*s_val):10.5f}")
    print()

def exp_B_legendre_preservation(N_max=400, s_val=1.5):
    print("=== B. Legendre Preservation ===")
    bc = BostConnesLayer12(N_max=N_max)
    primes = list(primerange(2, 20))
    
    K_0 = build_K(bc, primes, s_val=s_val, Phi=0.0)
    K_Leg = build_K(bc, primes, s_val=s_val, Phi=np.pi/4, random_phase=False)
    K_rand = build_K(bc, primes, s_val=s_val, Phi=np.pi/4, random_phase=True)
    
    for k in [1, 2]:
        print(f"\nOrbit extraction for K^{k}:")
        c_0 = moebius_inversion_trace(np.linalg.matrix_power(K_0, k))
        c_Leg = moebius_inversion_trace(np.linalg.matrix_power(K_Leg, k))
        c_rand = moebius_inversion_trace(np.linalg.matrix_power(K_rand, k))
        
        print(f"{'p':>2} | {'K_0':>10} | {'K_Leg':>10} | {'K_rand':>10} | {'Expected':>10}")
        print("-" * 55)
        for p in [3, 5, 7]:
            exp_val = p ** (-k * s_val)
            print(f"{p:2d} | {c_0[p]:10.5f} | {c_Leg[p]:10.5f} | {c_rand[p]:10.5f} | {exp_val:10.5f}")
    print()
    return K_0, K_Leg, K_rand

def exp_C_fredholm_reconstruction(K_0, K_Leg, K_rand):
    print("=== C. Fredholm Reconstruction ===")
    z = 0.5
    I = np.eye(K_0.shape[0], dtype=np.complex128)
    
    def compare_fredholm(name, K):
        log_det = -np.log(la.det(I - z * K)).real
        
        # Expansion sum_{m=1}^M (z^m / m) tau_orb(K^m)
        M = 5
        expansion_sum = 0
        for m in range(1, M + 1):
            K_m = np.linalg.matrix_power(K, m)
            c = moebius_inversion_trace(K_m)
            tau_orb = np.sum(c[2:])  # Total primitive trace
            expansion_sum += (z**m / m) * tau_orb
            
        print(f"{name:>6}: -log det = {log_det:8.5f} | expansion = {expansion_sum:8.5f}")
        
    compare_fredholm("K_0", K_0)
    compare_fredholm("K_Leg", K_Leg)
    compare_fredholm("K_rand", K_rand)

if __name__ == "__main__":
    exp_A_cutoff_convergence()
    K0, KLeg, Krand = exp_B_legendre_preservation(N_max=400, s_val=1.5)
    exp_C_fredholm_reconstruction(K0, KLeg, Krand)
