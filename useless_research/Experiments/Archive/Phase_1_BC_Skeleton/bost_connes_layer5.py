import numpy as np
import scipy.linalg as la
from sympy import primerange
import math

class BostConnesLayer5:
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

    def von_mangoldt(self, n):
        if n <= 1:
            return 0
        for p in primerange(2, int(math.sqrt(n)) + 2):
            if n % p == 0:
                temp = n
                while temp % p == 0:
                    temp //= p
                if temp == 1:
                    return np.log(p)
                return 0
        return np.log(n)

    def L_s_operator(self, s_val=1.5):
        L_s = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for n in range(2, self.N_max + 1):
            lam = self.von_mangoldt(n)
            if lam > 0:
                L_s += lam * (n ** (-s_val)) * self.mu(n)
        return L_s

def calc_r_ratio(evals):
    # evals should be sorted real values
    spacings = np.diff(evals)
    spacings = spacings[spacings > 1e-10]
    if len(spacings) < 2: return 0
    r_n = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
    return np.mean(r_n)

def calc_PR(evecs):
    # evecs[:, i] is the i-th eigenvector
    # PR = 1 / sum |psi_k|^4
    probs = np.abs(evecs)**2
    ipr = np.sum(probs**2, axis=0)
    pr = 1.0 / ipr
    return np.mean(pr)

def exp_A_arithmetic_mixing(bc, s_val=0.5):
    print(f"=== Experiment A: Arithmetic Mixing (s={s_val}) ===")
    D = bc.D_operator()
    L_s = bc.L_s_operator(s_val=s_val)
    L_s_sym = L_s + L_s.T.conj()
    
    lambdas = [0.0, 0.01, 0.03, 0.1, 0.3, 1.0]
    print(f"{'lambda':>8} | {'<r>':>8} | {'PR':>8}")
    print("-" * 30)
    for lam in lambdas:
        H_lam = D + lam * L_s_sym
        evals, evecs = la.eigh(H_lam)
        r_val = calc_r_ratio(evals)
        pr_val = calc_PR(evecs)
        print(f"{lam:8.3f} | {r_val:8.4f} | {pr_val:8.2f}")
    print()

def exp_null_hypothesis(bc, s_val=0.5, lam=1.0):
    print(f"=== Null Hypothesis: Randomized Phases (lam={lam}, s={s_val}) ===")
    D = bc.D_operator()
    L_s = bc.L_s_operator(s_val=s_val)
    
    # Randomize the phases of the off-diagonal elements
    L_s_rand = np.zeros_like(L_s)
    for i in range(bc.dim):
        for j in range(bc.dim):
            if np.abs(L_s[i, j]) > 1e-12:
                phase = np.exp(1j * np.random.uniform(0, 2*np.pi))
                L_s_rand[i, j] = L_s[i, j] * phase
                
    H_rand = D + lam * (L_s_rand + L_s_rand.T.conj())
    evals, evecs = la.eigh(H_rand)
    r_val = calc_r_ratio(evals)
    pr_val = calc_PR(evecs)
    
    print(f"{'Condition':>15} | {'<r>':>8} | {'PR':>8}")
    print("-" * 37)
    
    # Run exact again for comparison
    H_exact = D + lam * (L_s + L_s.T.conj())
    evals_e, evecs_e = la.eigh(H_exact)
    r_val_e = calc_r_ratio(evals_e)
    pr_val_e = calc_PR(evecs_e)
    
    print(f"{'Deterministic':>15} | {r_val_e:8.4f} | {pr_val_e:8.2f}")
    print(f"{'Random Phase':>15} | {r_val:8.4f} | {pr_val:8.2f}")
    print()

if __name__ == "__main__":
    # N_max = 200 gives a solid matrix size for r-ratio and PR.
    bc = BostConnesLayer5(N_max=300)
    
    # Using s=0.5 (critical line scaling) and s=1.5
    for s_val in [1.5, 0.5]:
        exp_A_arithmetic_mixing(bc, s_val=s_val)
        exp_null_hypothesis(bc, s_val=s_val, lam=1.0)
