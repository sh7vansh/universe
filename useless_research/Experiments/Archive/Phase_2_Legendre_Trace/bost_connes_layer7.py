import numpy as np
import scipy.linalg as la
from sympy import primerange, legendre_symbol
import math

class BostConnesLayer7:
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

    def von_mangoldt(self, n):
        if n <= 1: return 0
        for p in primerange(2, int(math.sqrt(n)) + 2):
            if n % p == 0:
                temp = n
                while temp % p == 0: temp //= p
                if temp == 1: return np.log(p)
                return 0
        return np.log(n)

    def L_s_operator(self, s_val=0.5):
        L_s = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for n in range(2, self.N_max + 1):
            lam = self.von_mangoldt(n)
            if lam > 0:
                L_s += lam * (n ** (-s_val)) * self.mu(n)
        return L_s

    def legendre_exchange(self, primes, s_val=0.5, Phi=np.pi/4, random_phase=False):
        V = np.zeros((self.dim, self.dim), dtype=np.complex128)
        
        # Filter out 2 for Legendre
        odd_primes = [p for p in primes if p > 2]
        n_p = len(odd_primes)
        chi = np.zeros((n_p, n_p))
        if random_phase:
            for i in range(n_p):
                for j in range(i+1, n_p):
                    val = np.random.uniform(-1, 1)
                    chi[i, j] = val
                    chi[j, i] = -val
        else:
            for i in range(n_p):
                for j in range(n_p):
                    if i != j:
                        p, q = odd_primes[i], odd_primes[j]
                        chi[i, j] = legendre_symbol(p, q) - legendre_symbol(q, p)
                        
        for i, p in enumerate(odd_primes):
            for j, q in enumerate(odd_primes):
                if i != j:
                    weight = (p * q) ** (-s_val / 2.0)
                    phase = np.exp(1j * Phi * chi[i, j])
                    R_pq = self.mu(p) @ self.mu_star(q)
                    V += weight * phase * R_pq
        return V

def calc_r_ratio(evals):
    spacings = np.diff(evals)
    spacings = spacings[spacings > 1e-10]
    if len(spacings) < 2: return 0
    r_n = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
    return np.mean(r_n)

def check_loop_flux(V, p, q, r):
    # R_pq moves q -> p. Let's trace p -> r -> q -> p
    # In V, V_{rp} moves p -> r. 
    # State p is index p-1.
    # We want amplitude for |p> -> |r> -> |q> -> |p>
    amp1 = V[r-1, p-1]
    amp2 = V[q-1, r-1]
    amp3 = V[p-1, q-1]
    prod = amp1 * amp2 * amp3
    if abs(prod) < 1e-12:
        return 0.0
    return np.angle(prod)

def run_layer7(N_max=300, s_val=0.5, lam=1.0, kappa=1.0):
    bc = BostConnesLayer7(N_max=N_max)
    primes = list(primerange(2, 50))
    
    D = bc.D_operator()
    L_s = bc.L_s_operator(s_val=s_val)
    L_s_sym = L_s + L_s.T.conj()
    
    V_0 = bc.legendre_exchange(primes, s_val, Phi=0.0)
    V_Leg = bc.legendre_exchange(primes, s_val, Phi=np.pi/4, random_phase=False)
    V_rand = bc.legendre_exchange(primes, s_val, Phi=np.pi/4, random_phase=True)
    
    # 1. Gauge test
    flux_0 = check_loop_flux(V_0, 3, 5, 7)
    flux_Leg = check_loop_flux(V_Leg, 3, 5, 7)
    flux_rand = check_loop_flux(V_rand, 3, 5, 7)
    
    print(f"=== Layer 7: Legendre Exchange Dynamics (N={N_max}) ===")
    print(f"Wilson Loop Flux (|3> -> |7> -> |5> -> |3>):")
    print(f"  V_0 (No Phase)     : {flux_0:.4f} rad")
    print(f"  V_Leg (Legendre)   : {flux_Leg:.4f} rad")
    print(f"  V_rand (Random)    : {flux_rand:.4f} rad")
    
    if abs(flux_Leg) < 1e-8:
        print("WARNING: Legendre loop flux is zero. It might be pure gauge.")
        return
        
    print("\nFlux is non-zero. Calculating spectral statistics...")
    
    # We apply the transport mixing + the exchange mixing
    H_BC = D + lam * L_s_sym + kappa * V_0
    H_Leg = D + lam * L_s_sym + kappa * V_Leg
    H_rand = D + lam * L_s_sym + kappa * V_rand
    
    def analyze(H):
        evals, _ = la.eigh(H)
        return calc_r_ratio(evals)
        
    r_BC = analyze(H_BC)
    r_Leg = analyze(H_Leg)
    r_rand = analyze(H_rand)
    
    print(f"\nSpectral Ratios (<r>):")
    print(f"  H_BC (Real/GOE expected ~0.53)    : {r_BC:.4f}")
    print(f"  H_Leg (Legendre expected ~0.60)   : {r_Leg:.4f}")
    print(f"  H_rand (Random phase GUE ~0.60)   : {r_rand:.4f}")

if __name__ == "__main__":
    # Test at critical line s=0.5
    run_layer7(N_max=300, s_val=0.5, lam=0.5, kappa=1.0)
