import numpy as np

class BostConnesAlgebra:
    """
    Layer 1: The arithmetic algebra of the Bost-Connes system.
    We represent the C*-algebra generators over a truncated Hilbert space H = l^2(N).
    
    Basis states: |k> for k in {1, 2, ..., N_max}
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

if __name__ == "__main__":
    bc = BostConnesAlgebra(N_max=50)
    mu_2 = bc.mu(2)
    mu_2_star = bc.mu_star(2)
    e_half = bc.e(0.5)
    
    print("Testing relations...")
    print("mu_2 * mu_2_star (projection):")
    proj = mu_2 @ mu_2_star
    print("Trace of projection =", bc.trace(proj))
    print("Trace of mu_2 =", bc.trace(mu_2))
