import numpy as np
import scipy.linalg as la
from sympy import primerange
import math

class BostConnesLayer6:
    def __init__(self, N_max=200):
        self.N_max = N_max
        self.dim = N_max

    def mu(self, n):
        mat = np.zeros((self.dim, self.dim), dtype=np.complex128)
        for k in range(1, self.dim + 1):
            if n * k <= self.dim:
                mat[n * k - 1, k - 1] = 1.0
        return mat

    def P(self, n):
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
        if n <= 1: return 0
        for p in primerange(2, int(math.sqrt(n)) + 2):
            if n % p == 0:
                temp = n
                while temp % p == 0: temp //= p
                if temp == 1: return np.log(p)
                return 0
        return np.log(n)

def calc_r_ratio(evals):
    spacings = np.diff(evals)
    spacings = spacings[spacings > 1e-10]
    if len(spacings) < 2: return 0
    r_n = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
    return np.mean(r_n)

def check_flux(L):
    # Check flux around the p=2, p=3 plaquette starting at |1> (index 0)
    # path 1: 1 -> 2 -> 6
    # path 2: 1 -> 3 -> 6
    # flux = arg(L[1,0] * L[5,1] * conj(L[2,0] * L[5,2]))
    if L[1,0] == 0 or L[5,1] == 0 or L[2,0] == 0 or L[5,2] == 0:
        return 0.0
    amp1 = L[1,0] * L[5,1]
    amp2 = L[2,0] * L[5,2]
    return np.angle(amp1 * np.conj(amp2))

def run_layer6_experiment(N_max=150, s_val=0.5, lam=1.0, theta=np.pi/4):
    bc = BostConnesLayer6(N_max=N_max)
    D = bc.D_operator()
    
    # Base operator L_s
    L_s = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    for n in range(2, bc.N_max + 1):
        lam_n = bc.von_mangoldt(n)
        if lam_n > 0:
            L_s += lam_n * (n ** (-s_val)) * bc.mu(n)
            
    # H0: Deterministic arithmetic mixing
    H0 = D + lam * (L_s + L_s.T.conj())
    
    # H1: BC-native phase dressing
    # Let's dress mu_p with e^{i theta P_q} where q is the next prime after p
    L_phase = np.zeros((bc.dim, bc.dim), dtype=np.complex128)
    primes = list(primerange(2, 20))
    for n in range(2, bc.N_max + 1):
        lam_n = bc.von_mangoldt(n)
        if lam_n > 0:
            # find the prime factor
            for p in primes:
                if n % p == 0:
                    break
            # Pick a dressing prime q. Just use q=2 for odd p, and q=3 for p=2.
            q = 2 if p != 2 else 3
            # Apply dressing: e^{i theta P_q} * mu_n
            # P_q is diagonal. e^{i theta P_q} has e^{i theta} on q|k, 1 else.
            phase_op = np.eye(bc.dim, dtype=np.complex128)
            for k in range(1, bc.dim + 1):
                if k % q == 0:
                    phase_op[k-1, k-1] = np.exp(1j * theta)
            
            term = lam_n * (n ** (-s_val)) * (phase_op @ bc.mu(n))
            L_phase += term
            
    H1 = D + lam * (L_phase + L_phase.T.conj())
    
    # Check flux of L_phase
    flux = check_flux(L_phase)
    
    # H2: Random phase (same support and magnitudes)
    L_rand = np.zeros_like(L_s)
    for i in range(bc.dim):
        for j in range(bc.dim):
            if np.abs(L_s[i, j]) > 1e-12:
                L_rand[i, j] = L_s[i, j] * np.exp(1j * np.random.uniform(0, 2*np.pi))
    H2 = D + lam * (L_rand + L_rand.T.conj())

    # H3: Pure gauge (diagonal random phase transform of H0)
    U_gauge = np.diag(np.exp(1j * np.random.uniform(0, 2*np.pi, bc.dim)))
    H3 = U_gauge @ H0 @ U_gauge.conj().T
    
    # Analyze
    def analyze(H):
        evals, _ = la.eigh(H)
        return calc_r_ratio(evals)
        
    r0 = analyze(H0)
    r1 = analyze(H1)
    r2 = analyze(H2)
    r3 = analyze(H3)
    
    print(f"=== Layer 6 Trace & Flux Analysis (N={N_max}, s={s_val}) ===")
    print(f"Flux around |1> -> |2> -> |6> vs |1> -> |3> -> |6>: {flux:.4f} radians")
    print("\nSpectral Ratios:")
    print(f"H0 (Unphased GOE-like)  : {r0:.4f}")
    print(f"H1 (BC Native Dressing) : {r1:.4f}")
    print(f"H2 (Random Phase GUE)   : {r2:.4f}")
    print(f"H3 (Gauge Transformed)  : {r3:.4f}")
    
    if abs(flux) < 1e-10:
        print("\nCONCLUSION: Flux is zero. The BC phase dressing is pure gauge.")
    else:
        print("\nCONCLUSION: Flux is nonzero. Time-reversal symmetry is genuinely broken by the BC algebra.")

if __name__ == "__main__":
    run_layer6_experiment(N_max=200, s_val=0.5, lam=1.0, theta=np.pi/3)
