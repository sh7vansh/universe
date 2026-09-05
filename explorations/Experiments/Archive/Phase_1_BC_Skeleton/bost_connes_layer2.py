import numpy as np
from sympy import primerange
import scipy.linalg as la

class BostConnesAlgebra:
    """
    Layer 1: The arithmetic algebra of the Bost-Connes system.
    """
    def __init__(self, N_max=100):
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

    def e(self, r):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            mat[k - 1, k - 1] = np.exp(2j * np.pi * r * k)
        return mat

    def trace(self, op):
        return np.trace(op)

def exp1_projector_construction(bc, primes):
    print("=== Experiment 1: P_p Construction ===")
    for p in primes:
        # P_p = mu_p * mu_p^*
        P_p_mu = bc.mu(p) @ bc.mu_star(p)
        
        # P_p from phase algebra
        P_p_phase = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
        for a in range(p):
            P_p_phase += bc.e(a / p)
        P_p_phase /= p
        
        # Verify
        is_close = np.allclose(P_p_mu, P_p_phase)
        print(f"p={p}: P_p from phases matches mu_p mu_p^*? {is_close}")
        if is_close:
            print(f"       Trace of P_p = {bc.trace(P_p_phase).real:.2f} (Expected ~ {bc.dim/p:.2f})")
    print()

def exp2_hecke_compositions(bc, p, q):
    print("=== Experiment 2: Hecke/Scaling Compositions ===")
    T_p = bc.mu(p) + bc.mu_star(p)
    T_q = bc.mu(q) + bc.mu_star(q)
    
    P_p = bc.mu(p) @ bc.mu_star(p)
    P_q = bc.mu(q) @ bc.mu_star(q)
    
    print(f"Trace(T_p) for p={p}: {bc.trace(T_p)}")
    print(f"Trace(P_p) for p={p}: {bc.trace(P_p).real:.2f}")
    
    # Compositions
    Tp_Pq = T_p @ P_q
    Pp_Tq = P_p @ T_q
    Pp_Pq = P_p @ P_q
    
    print(f"Trace(T_p P_q) for p={p}, q={q}: {bc.trace(Tp_Pq).real:.2f}")
    print(f"Trace(P_p T_q) for p={p}, q={q}: {bc.trace(Pp_Tq).real:.2f}")
    print(f"Trace(P_p P_q) for p={p}, q={q}: {bc.trace(Pp_Pq).real:.2f} (Expected ~ {bc.dim/(p*q):.2f})")
    
    # Let's look at the eigenvalues of T_p
    vals = la.eigvals(T_p)
    print(f"Max eigenvalue of T_p: {np.max(np.abs(vals)):.4f}")
    print()

def exp3_multiplicative_growth(bc, primes, z=0.5):
    print("=== Experiment 3: Multiplicative Semigroup Growth ===")
    # A(z) = \prod_{p<=P} (1 - z P_p)^{-1}
    # Since P_p is a projector, (1 - z P_p)^{-1} = I + (z / (1 - z)) P_p
    A = np.eye(bc.dim, dtype=np.complex128)
    for p in primes:
        P_p = bc.mu(p) @ bc.mu_star(p)
        term = np.eye(bc.dim, dtype=np.complex128) + (z / (1.0 - z)) * P_p
        A = A @ term
        
    print(f"Computed A(z) for z={z} over primes {primes}")
    print(f"Trace(A(z)): {bc.trace(A).real:.2f}")
    
    # Let's check some diagonal entries A_nn
    # A_nn should be closely related to z^omega(n) where omega is the number of prime factors from `primes`
    print("Diagonal entries of A(z) (first 10):")
    diag = np.diag(A).real
    for n in range(1, 11):
        factors = sum(1 for p in primes if n % p == 0)
        expected = (1 / (1 - z)) ** factors  # Since P_p |n> = |n> if p|n
        print(f"  n={n:2d}: computed={diag[n-1]:.4f}, expected=(1/(1-z))^{factors}={expected:.4f}")
    print()

def exp4_generator_search(bc, primes):
    print("=== Experiment 4: Generator Search ===")
    print("Seeking an additive generator for mu_p mu_q = mu_{pq}.")
    print("If mu_p = exp(G_p), what is G_p? Since mu_p is a truncated shift, it is nilpotent.")
    print("Let's analyze the spectrum of the Hecke sum H = sum T_p.")
    
    H = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    for p in primes:
        H += bc.mu(p) + bc.mu_star(p)
        
    vals = np.sort(la.eigvals(H).real)
    print(f"Hecke sum eigenvalues over primes {primes}:")
    print(f"  Min: {vals[0]:.4f}")
    print(f"  Max: {vals[-1]:.4f}")
    
    # We can also look at the commutators [T_p, T_q].
    # In the infinite basis they commute, but finite truncation breaks it slightly.
    T_2 = bc.mu(2) + bc.mu_star(2)
    T_3 = bc.mu(3) + bc.mu_star(3)
    comm = T_2 @ T_3 - T_3 @ T_2
    print(f"Frobenius norm of [T_2, T_3] due to truncation: {la.norm(comm):.4f}")

if __name__ == "__main__":
    bc = BostConnesAlgebra(N_max=100)
    primes = list(primerange(2, 20))  # 2, 3, 5, 7, 11, 13, 17, 19
    
    exp1_projector_construction(bc, primes[:3])
    exp2_hecke_compositions(bc, 2, 3)
    exp3_multiplicative_growth(bc, primes)
    exp4_generator_search(bc, primes)
