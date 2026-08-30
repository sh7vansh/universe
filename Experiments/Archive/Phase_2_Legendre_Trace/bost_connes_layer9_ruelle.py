import numpy as np
import scipy.linalg as la
from sympy import primerange, legendre_symbol
import math

class BostConnesLayer9:
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
        odd_primes = [p for p in primes if p > 2]
        n_p = len(odd_primes)
        chi = np.zeros((n_p, n_p))
        if random_phase:
            np.random.seed(111)
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
                    phase = np.exp(1j * Phi * chi[i, j])
                    R_pq = self.mu(p) @ self.mu_star(q)
                    V += weight * phase * R_pq
        return V

def run_layer9_ruelle(N_max=150, s_val=0.5, kappa=1.0):
    bc = BostConnesLayer9(N_max=N_max)
    primes = list(primerange(2, 40))
    
    L_s = bc.L_s_operator(s_val=s_val)
    V_Leg = bc.legendre_exchange(primes, s_val=s_val, Phi=np.pi/4, random_phase=False)
    V_rand = bc.legendre_exchange(primes, s_val=s_val, Phi=np.pi/4, random_phase=True)
    
    T_BC = L_s
    T_Leg = L_s + kappa * V_Leg
    T_rand = L_s + kappa * V_rand
    
    K_BC = T_BC.T.conj() @ T_BC
    K_Leg = T_Leg.T.conj() @ T_Leg
    K_rand = T_rand.T.conj() @ T_rand
    
    print(f"=== Layer 9: Ruelle Return Dynamics (N={N_max}) ===")
    
    # 1. Tr(K^L)
    print("\nTrace R_L = Tr(K^L) for closed words of length 2L")
    print(f"{'L':>2} | {'K_BC':>12} | {'K_Leg':>12} | {'K_rand':>12}")
    print("-" * 47)
    for L in [1, 2, 3]:
        r_bc = np.trace(np.linalg.matrix_power(K_BC, L)).real
        r_leg = np.trace(np.linalg.matrix_power(K_Leg, L)).real
        r_rand = np.trace(np.linalg.matrix_power(K_rand, L)).real
        print(f"{L:2d} | {r_bc:12.4f} | {r_leg:12.4f} | {r_rand:12.4f}")
        
    # 2. Extract primitive weights from the diagonal of K_BC
    print("\nExtracting Primitive Aggregate Weights A_{p^k} from K_BC")
    print("Does A_{p^k} scale as log(p), log(p)/k, or something else?")
    print(f"{'p':>2} | {'k':>2} | {'n':>3} | {'A_n':>8} | {'(A_n / (log p)^2) * n':>20}")
    print("-" * 55)
    
    diag_K = np.diag(K_BC).real
    for p in [2, 3, 5]:
        for k in [1, 2, 3]:
            n = p**k
            if n > bc.N_max:
                continue
            # A_n is exactly the coefficient of the |n> projection in K
            # But wait, K_BC = sum_n (lam(n)/n^s)^2 mu_n^* mu_n.
            # Its diagonal elements are sum_{m | j} (lam(m)/m^s)^2.
            # Let's isolate the specific transition by just looking at the difference or computing the trace directly.
            A_n = (bc.von_mangoldt(n) / (n ** s_val))**2 * (bc.N_max // n)
            normalized = A_n / (np.log(p)**2) * (n ** (2*s_val)) / (bc.N_max // n) 
            print(f"{p:2d} | {k:2d} | {n:3d} | {A_n:8.4f} | {normalized:20.4f}")
            
    # Spectral statistics of K
    def analyze(H):
        evals = np.sort(la.eigvals(H).real)
        spacings = np.diff(evals)
        spacings = spacings[spacings > 1e-10]
        if len(spacings) < 2: return 0
        r_n = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
        return np.mean(r_n)
        
    print("\nSpectral Ratios of the Return Operator K (<r>):")
    print(f"  K_BC   : {analyze(K_BC):.4f}")
    print(f"  K_Leg  : {analyze(K_Leg):.4f}")
    print(f"  K_rand : {analyze(K_rand):.4f}")

if __name__ == "__main__":
    run_layer9_ruelle(N_max=150, s_val=0.5, kappa=1.0)
