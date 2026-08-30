import numpy as np
import scipy.linalg as la
from sympy import primerange

def run_layer14():
    primes = list(primerange(2, 50))
    N_p = len(primes)
    
    # 1. Primitive Orbit Space (H_prim)
    # T_s is purely diagonal, carrying the prime weights
    s_val = 0.5
    T_s = np.diag([p**(-s_val) for p in primes])
    
    print("=== Layer 14: Two-Space Prototype ===")
    print(f"H_prim dimension: {N_p}")
    
    tau_1 = np.trace(T_s)
    tau_2 = np.trace(T_s @ T_s)
    print(f"Bare Trace(T_s)   = {tau_1:.4f}")
    print(f"Bare Trace(T_s^2) = {tau_2:.4f}")
    
    # 2. Add Global Mixing M
    # H = T_s + lambda * M
    np.random.seed(42)
    M_GOE = np.random.randn(N_p, N_p)
    M_GOE = (M_GOE + M_GOE.T) / 2.0
    # Zero out diagonal to preserve Tr(H) = Tr(T_s)
    np.fill_diagonal(M_GOE, 0)
    
    # Add Legendre-like TRS breaking (GUE)
    M_GUE_imag = np.random.randn(N_p, N_p)
    M_GUE_imag = (M_GUE_imag - M_GUE_imag.T) / 2.0
    M_GUE = M_GOE + 1j * M_GUE_imag
    
    lam = 0.5
    H_mixed_GOE = T_s + lam * M_GOE
    H_mixed_GUE = T_s + lam * M_GUE
    
    # Traces of mixed operator
    mix_tau_1 = np.trace(H_mixed_GUE).real
    mix_tau_2 = np.trace(H_mixed_GUE @ H_mixed_GUE).real
    
    print(f"\nAfter adding Mixing M (lambda={lam}):")
    print(f"Mixed Trace(H)   = {mix_tau_1:.4f}  (Invariant because diag(M) = 0)")
    print(f"Mixed Trace(H^2) = {mix_tau_2:.4f}  (Shifted because Tr(M^2) > 0)")
    
    # Spectral statistics
    def calc_r(evals):
        spacings = np.diff(np.sort(evals))
        spacings = spacings[spacings > 1e-10]
        if len(spacings) < 2: return 0
        r_n = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
        return np.mean(r_n)
        
    r_bare = calc_r(np.diag(T_s).real)
    r_GOE = calc_r(la.eigvals(H_mixed_GOE).real)
    r_GUE = calc_r(la.eigvals(H_mixed_GUE).real)
    
    print("\nSpectral Ratios <r>:")
    print(f"  Bare T_s (Poisson) : {r_bare:.4f}")
    print(f"  Mixed GOE          : {r_GOE:.4f}")
    print(f"  Mixed GUE          : {r_GUE:.4f}")

if __name__ == "__main__":
    run_layer14()
