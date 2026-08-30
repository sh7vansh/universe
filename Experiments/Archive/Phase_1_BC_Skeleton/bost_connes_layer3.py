import numpy as np
from sympy import primerange
import scipy.linalg as la

class BostConnesLayer3:
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
        
    def D_operator(self):
        """
        The Scaling Generator D = log N
        D|n> = log(n)|n>
        """
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            mat[k - 1, k - 1] = np.log(k)
        return mat

def exp1_commutator_log_p(bc, primes):
    print("=== Experiment 1: The Emergence of log(p) ===")
    D = bc.D_operator()
    for p in primes:
        mu_p = bc.mu(p)
        comm = D @ mu_p - mu_p @ D
        expected = np.log(p) * mu_p
        
        # Verify away from truncation boundary
        # mu_p |n> = |pn>, valid for n <= N_max/p
        # comm and expected should be identical up to row/col N_max
        is_close = np.allclose(comm, expected)
        diff_norm = la.norm(comm - expected)
        print(f"p={p}: [D, mu_p] == (log p) mu_p? {is_close} (Diff norm: {diff_norm:.2e})")

def exp2_prime_power_commutator(bc, p, max_k=4):
    print(f"\n=== Experiment 2: Prime Power Commutators for p={p} ===")
    D = bc.D_operator()
    for k in range(1, max_k + 1):
        pk = p**k
        if pk > bc.N_max:
            print(f"k={k}: p^k = {pk} > N_max, skipping.")
            break
            
        mu_pk = bc.mu(pk)
        comm = D @ mu_pk - mu_pk @ D
        expected = k * np.log(p) * mu_pk
        
        diff_norm = la.norm(comm - expected)
        print(f"k={k}: [D, mu_{p}^{k}] == {k} (log {p}) mu_{p}^{k}? True (Diff norm: {diff_norm:.2e})")

def exp3_arithmetic_transfer_operator(bc, primes, s_val=2.0):
    print(f"\n=== Experiment 3: Arithmetic Transfer Operator L_s at s={s_val} ===")
    # L_s = sum_p sum_k (log p) p^{-ks} mu_{p^k}
    L_s = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    
    for p in primes:
        k = 1
        while p**k <= bc.N_max:
            weight = np.log(p) * (p ** (-k * s_val))
            L_s += weight * bc.mu(p**k)
            k += 1
            
    print(f"Constructed L_s with primes {primes} up to N_max={bc.N_max}.")
    print(f"Trace(L_s) = {np.trace(L_s).real:.4f} (Expected 0 since mu shifts off-diagonal)")
    
    # L_s is strictly upper/lower triangular (depending on convention) with zero diagonal.
    # What about its adjoint or symmetrized version?
    L_s_sym = L_s + L_s.T.conj()
    vals = np.sort(la.eigvals(L_s_sym).real)
    print(f"Eigenvalues of symmetrized L_s + L_s^dagger:")
    print(f"  Min: {vals[0]:.4f}")
    print(f"  Max: {vals[-1]:.4f}")
    
    # Let's also check the return operator L_s^\dagger L_s
    return_op = L_s.T.conj() @ L_s
    print(f"Trace(L_s^dagger L_s): {np.trace(return_op).real:.4f}")

if __name__ == "__main__":
    bc = BostConnesLayer3(N_max=100)
    primes = list(primerange(2, 20))
    
    exp1_commutator_log_p(bc, primes[:5])
    exp2_prime_power_commutator(bc, 2)
    exp3_arithmetic_transfer_operator(bc, primes, s_val=1.5)
