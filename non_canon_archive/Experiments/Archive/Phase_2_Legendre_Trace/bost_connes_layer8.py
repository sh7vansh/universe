import numpy as np
import scipy.linalg as la
from sympy import primerange, legendre_symbol
import math

class BostConnesLayer8:
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

    def D_operator(self):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            mat[k - 1, k - 1] = np.log(k)
        return mat

    def von_mangoldt(self, n, flat=False):
        if n <= 1: return 0
        if flat:
            for p in primerange(2, int(math.sqrt(n)) + 2):
                if n % p == 0:
                    temp = n
                    while temp % p == 0: temp //= p
                    if temp == 1: return 1.0
                    return 0
            return 1.0
        
        for p in primerange(2, int(math.sqrt(n)) + 2):
            if n % p == 0:
                temp = n
                while temp % p == 0: temp //= p
                if temp == 1: return np.log(p)
                return 0
        return np.log(n)

    def L_s_operator(self, s_val=0.5, flat=False):
        L_s = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for n in range(2, self.N_max + 1):
            lam = self.von_mangoldt(n, flat=flat)
            if lam > 0:
                L_s += lam * (n ** (-s_val)) * self.mu(n)
        return L_s

    def legendre_exchange(self, primes, s_val=0.5, Phi=np.pi/4, random_phase=False, sign=1.0):
        V = np.zeros((self.dim, self.dim), dtype=np.complex128)
        
        odd_primes = [p for p in primes if p > 2]
        n_p = len(odd_primes)
        chi = np.zeros((n_p, n_p))
        if random_phase:
            # Fixed seed for reproducibility of the random control
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
                if i != j:
                    weight = (p * q) ** (-s_val / 2.0)
                    phase = np.exp(1j * sign * Phi * chi[i, j])
                    R_pq = self.mu(p) @ self.mu_star(q)
                    V += weight * phase * R_pq
        return V

def compute_Z_t(evals, t_vals):
    # Z(t) = sum_j e^{-i t E_j}
    # returns magnitude |Z(t)|
    Z_mag = np.zeros_like(t_vals, dtype=np.float64)
    for i, t in enumerate(t_vals):
        Z = np.sum(np.exp(-1j * t * evals))
        Z_mag[i] = np.abs(Z)
    return Z_mag

def run_layer8(N_max=300, s_val=0.5, lam=0.5, kappa=1.0):
    bc = BostConnesLayer8(N_max=N_max)
    primes = list(primerange(2, 50))
    
    D = bc.D_operator()
    
    L_s = bc.L_s_operator(s_val=s_val, flat=False)
    L_s_sym = L_s + L_s.T.conj()
    
    L_flat = bc.L_s_operator(s_val=s_val, flat=True)
    L_flat_sym = L_flat + L_flat.T.conj()
    
    V_0 = bc.legendre_exchange(primes, s_val, Phi=0.0)
    V_Leg = bc.legendre_exchange(primes, s_val, Phi=np.pi/4, random_phase=False)
    V_rand = bc.legendre_exchange(primes, s_val, Phi=np.pi/4, random_phase=True)
    V_Leg_neg = bc.legendre_exchange(primes, s_val, Phi=np.pi/4, random_phase=False, sign=-1.0)
    
    H_BC = D + lam * L_s_sym + kappa * V_0
    H_Leg = D + lam * L_s_sym + kappa * V_Leg
    H_rand = D + lam * L_s_sym + kappa * V_rand
    H_flat = D + lam * L_flat_sym + kappa * V_Leg
    H_Leg_neg = D + lam * L_s_sym + kappa * V_Leg_neg
    
    evals_BC = np.sort(la.eigvals(H_BC).real)
    evals_Leg = np.sort(la.eigvals(H_Leg).real)
    evals_rand = np.sort(la.eigvals(H_rand).real)
    evals_flat = np.sort(la.eigvals(H_flat).real)
    evals_Leg_neg = np.sort(la.eigvals(H_Leg_neg).real)
    
    # Check if V -> -V leaves spectrum invariant
    diff_neg = la.norm(evals_Leg - evals_Leg_neg)
    
    print(f"=== Layer 8: Trace Formula & Primer Power Projection (N={N_max}) ===")
    print(f"Time Reversal Check (V -> -V): spectrum difference norm = {diff_neg:.2e}")
    
    # We will probe exactly at t = k log p
    probe_primes = [2, 3, 5, 7]
    k_vals = [1, 2]
    
    print("\nProbing |Z_H(t)| at exactly t = k*log(p)")
    print(f"{'Prime':>5} | {'k':>3} | {'t':>6} | {'H_BC':>8} | {'H_Leg':>8} | {'H_rand':>8} | {'H_flat':>8}")
    print("-" * 65)
    
    for p in probe_primes:
        for k in k_vals:
            t = k * np.log(p)
            z_BC = compute_Z_t(evals_BC, [t])[0]
            z_Leg = compute_Z_t(evals_Leg, [t])[0]
            z_rand = compute_Z_t(evals_rand, [t])[0]
            z_flat = compute_Z_t(evals_flat, [t])[0]
            
            print(f"{p:5d} | {k:3d} | {t:6.3f} | {z_BC:8.2f} | {z_Leg:8.2f} | {z_rand:8.2f} | {z_flat:8.2f}")
            
    # Compute average background level (Z_osc amplitude) by sampling non-prime times
    np.random.seed(101)
    bg_times = np.random.uniform(0.5, 3.0, 50)
    bg_BC = np.mean(compute_Z_t(evals_BC, bg_times))
    bg_Leg = np.mean(compute_Z_t(evals_Leg, bg_times))
    bg_rand = np.mean(compute_Z_t(evals_rand, bg_times))
    bg_flat = np.mean(compute_Z_t(evals_flat, bg_times))
    
    print("-" * 65)
    print(f"{'Bkgnd Avg':>9} | {'------':>6} | {bg_BC:8.2f} | {bg_Leg:8.2f} | {bg_rand:8.2f} | {bg_flat:8.2f}")
    
if __name__ == "__main__":
    run_layer8(N_max=300, s_val=0.5, lam=0.5, kappa=1.0)
