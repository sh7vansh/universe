import numpy as np
from sympy import primerange
import scipy.linalg as la
import math

class BostConnesLayer4:
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
        
    def P(self, n):
        """
        Divisibility projector P_n
        """
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            if k % n == 0:
                mat[k - 1, k - 1] = 1.0
        return mat

    def D_operator(self):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            mat[k - 1, k - 1] = np.log(k)
        return mat

    def von_mangoldt(self, n):
        """
        Returns log(p) if n = p^k for some prime p and integer k >= 1.
        Otherwise returns 0.
        """
        if n <= 1:
            return 0
        for p in primerange(2, int(math.sqrt(n)) + 2):
            if n % p == 0:
                # p is a prime factor. Check if it's the only one.
                temp = n
                while temp % p == 0:
                    temp //= p
                if temp == 1:
                    return np.log(p)
                return 0
        # If no prime factor found <= sqrt(n), n must be prime itself
        return np.log(n)

def exp1_von_mangoldt_operator(bc, s_val=2.0):
    print(f"=== Experiment 1: Von Mangoldt Transfer Operator L_s at s={s_val} ===")
    L_s = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    
    for n in range(2, bc.N_max + 1):
        lam = bc.von_mangoldt(n)
        if lam > 0:
            L_s += lam * (n ** (-s_val)) * bc.mu(n)
            
    print(f"Constructed L_s. Trace: {np.trace(L_s).real:.4f}")
    # Return operator
    ret = L_s.T.conj() @ L_s
    print(f"Trace(L_s^dagger L_s): {np.trace(ret).real:.4f}")
    print()

def exp2_arithmetic_return_words(bc, p, q):
    print(f"=== Experiment 2: Arithmetic Return Operators (Words) ===")
    print(f"Testing primitive closed words for p={p}, q={q}")
    
    # 1. mu_p^dagger P_p mu_p
    W1 = bc.mu_star(p) @ bc.P(p) @ bc.mu(p)
    print(f"Tr(mu_{p}^dagger P_{p} mu_{p}): {np.trace(W1).real:.2f} (Expected: {bc.dim // p})")
    
    # 2. mu_p^dagger P_q mu_p
    W2 = bc.mu_star(p) @ bc.P(q) @ bc.mu(p)
    print(f"Tr(mu_{p}^dagger P_{q} mu_{p}): {np.trace(W2).real:.2f} (Expected: {bc.dim // (p*q)})")
    
    # 3. Mixing scales: mu_p^dagger mu_q^dagger P_{pq} mu_q mu_p
    W3 = bc.mu_star(p) @ bc.mu_star(q) @ bc.P(p*q) @ bc.mu(q) @ bc.mu(p)
    print(f"Tr(mu_{p}^dagger mu_{q}^dagger P_{p*q} mu_{q} mu_{p}): {np.trace(W3).real:.2f} (Expected: {bc.dim // (p*q)})")
    
    print()

def exp3_arithmetic_trace_spectrum(bc, primes, beta=1.0):
    print(f"=== Experiment 3: Arithmetic Trace Spectrum ===")
    D = bc.D_operator()
    e_minus_beta_D = np.zeros_like(D)
    for k in range(bc.dim):
        e_minus_beta_D[k, k] = np.exp(-beta * D[k, k])
        
    print(f"Thermal trace of e^(-beta D) at beta={beta}: {np.trace(e_minus_beta_D).real:.4f} (Expected approx zeta({beta}))")
    
    print("\nMeasuring Tr(W e^(-beta D)) for simple return words W = mu_n^dagger mu_n")
    print("Does it organize by p^k?")
    for p in primes:
        for k in [1, 2, 3]:
            n = p**k
            if n > bc.N_max:
                continue
            W = bc.mu_star(n) @ bc.mu(n)  # Projection on valid domain
            
            trace_W = np.trace(W).real
            trace_W_thermal = np.trace(W @ e_minus_beta_D).real
            
    print("\nMeasuring Tr(P_n e^(-beta D)) for divisibility projectors P_n")
    print("Does it naturally generate the n^-beta Euler weight?")
    for p in primes:
        for k in [1, 2]:
            n = p**k
            if n > bc.N_max:
                continue
            P_n = bc.P(n)
            
            trace_P_thermal = np.trace(P_n @ e_minus_beta_D).real
            expected = (n ** -beta) * np.trace(e_minus_beta_D).real
            
            print(f"p={p}, k={k} (n={n:2d}): Tr(P_n e^(-D))={trace_P_thermal:.4f}, Expected n^-beta * Z={expected:.4f}")

if __name__ == "__main__":
    bc = BostConnesLayer4(N_max=100)
    primes = list(primerange(2, 20))
    
    exp1_von_mangoldt_operator(bc, s_val=1.5)
    exp2_arithmetic_return_words(bc, 2, 3)
    exp3_arithmetic_trace_spectrum(bc, primes[:5], beta=2.0)
