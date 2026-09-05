import numpy as np
import scipy.linalg as la
from sympy import primerange
import math

class BostConnesLayer10:
    def __init__(self, N_max=200):
        self.N_max = N_max
        self.dim = N_max

    def mu(self, n):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            if n * k <= self.dim:
                mat[n * k - 1, k - 1] = 1.0
        return mat

    def D_operator(self):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            mat[k - 1, k - 1] = np.log(k)
        return mat

    def unweighted_transfer(self, s_val):
        """
        Bare transfer operator T_s = sum_{p,k} p^{-ks} mu_{p^k}
        No log(p) weights.
        """
        T_s = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for p in primerange(2, self.N_max + 1):
            k = 1
            while p**k <= self.N_max:
                n = p**k
                T_s += (n ** (-s_val)) * self.mu(n)
                k += 1
        return T_s

def run_layer10(N_max=150, s_val=0.5):
    bc = BostConnesLayer10(N_max=N_max)
    D = bc.D_operator()
    
    # 1. Bare transfer operator
    T_s = bc.unweighted_transfer(s_val)
    
    # 2. Scaling commutator C_s = [D, T_s]
    C_s = D @ T_s - T_s @ D
    
    # Compute numerical derivative -\partial_s T_s
    ds = 1e-5
    T_s_plus = bc.unweighted_transfer(s_val + ds)
    T_s_minus = bc.unweighted_transfer(s_val - ds)
    neg_dT_ds = - (T_s_plus - T_s_minus) / (2 * ds)
    
    diff_norm = la.norm(C_s - neg_dT_ds)
    
    print(f"=== Layer 10: Ruelle Determinant Experiment (N={N_max}) ===")
    print(f"Identity Check: [D, T_s] == -\partial_s T_s")
    print(f"Difference norm: {diff_norm:.2e}")
    
    # 3. Fredholm/Ruelle expansion
    # F(z, s) = -\log\det(I - z T_s)
    z = 0.5
    I = np.eye(bc.dim)
    det_val = la.det(I - z * T_s)
    # Since T_s is strictly upper triangular, its diagonal is 0. 
    # Therefore I - z T_s is upper triangular with 1s on the diagonal.
    # Determinant is exactly 1.0!
    
    print(f"\nEvaluating F(z,s) = -\log det(I - z T_s) at z={z}")
    print(f"Determinant det(I - z T_s): {det_val.real:.4f} + {det_val.imag:.4f}j")
    
    # Trace expansion
    print(f"\nTrace expansion sum_{{m>=1}} (z^m/m) Tr(T_s^m)")
    for m in range(1, 4):
        tr_val = np.trace(np.linalg.matrix_power(T_s, m))
        print(f"m={m}: Tr(T_s^{m}) = {tr_val.real:.4f}")
        
    print("\nCONCLUSION:")
    print("Because T_s acts purely as a forward shift |k> -> |nk>, it has no fixed points on the integers.")
    print("Consequently, Tr(T_s^m) = 0 for all m, and det(I - z T_s) = 1 exactly.")
    print("To get a non-trivial Ruelle trace, we must close the arithmetic orbits using return operators (like K = T^dagger T, or projector-dressed operators P_n T_s).")

if __name__ == "__main__":
    run_layer10(N_max=150, s_val=0.5)
