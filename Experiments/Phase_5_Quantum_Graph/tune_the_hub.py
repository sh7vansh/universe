import numpy as np
from scipy.optimize import minimize
from scipy.linalg import expm
from sympy import primerange
import matplotlib.pyplot as plt
import os

# Target the first three Riemann zeros
TARGET_ZEROS = np.array([14.1347, 21.0220, 25.0108])

class HubTuner:
    def __init__(self, num_primes=15):
        self.primes = list(primerange(2, 200))[:num_primes]
        self.N = len(self.primes)
        
        # Precompute the diagonal phase matrices for our target zeros
        self.D_targets = [self.diagonal_phase_matrix(k) for k in TARGET_ZEROS]
        
    def diagonal_phase_matrix(self, k):
        D = np.zeros((self.N, self.N), dtype=complex)
        for j, p in enumerate(self.primes):
            amplitude = 1.0 / np.sqrt(p)
            phase = np.exp(1j * k * np.log(p))
            D[j, j] = amplitude * phase
        return D

    def build_unitary_S(self, params):
        """
        Builds a unitary matrix S from a set of real parameters.
        We construct a Hermitian matrix H, then S = exp(i * H)
        """
        H = np.zeros((self.N, self.N), dtype=complex)
        idx = 0
        # Fill diagonal (real)
        for i in range(self.N):
            H[i, i] = params[idx]
            idx += 1
        # Fill off-diagonal (complex)
        for i in range(self.N):
            for j in range(i + 1, self.N):
                H[i, j] = params[idx] + 1j * params[idx+1]
                H[j, i] = params[idx] - 1j * params[idx+1]
                idx += 2
                
        S = expm(1j * H)
        return S

    def loss_function(self, params):
        """
        The goal is to make the spectral determinant exactly zero 
        at the TARGET_ZEROS. We sum the absolute squared determinant.
        """
        S = self.build_unitary_S(params)
        loss = 0.0
        for D in self.D_targets:
            matrix = np.eye(self.N) - S @ D
            det_val = np.abs(np.linalg.det(matrix))
            loss += det_val**2
        return loss

def run_tuning():
    tuner = HubTuner(num_primes=10)
    print("=== Tuning the Hub ===")
    print(f"Network size: {tuner.N} prime loops.")
    print(f"Targeting Riemann Zeros: {TARGET_ZEROS}")
    
    # Total parameters for NxN Hermitian matrix is N^2
    num_params = tuner.N ** 2
    initial_params = np.random.randn(num_params) * 0.1
    
    print("\nStarting optimization to find the perfect scattering matrix (S)...")
    result = minimize(
        tuner.loss_function, 
        initial_params, 
        method='BFGS', 
        options={'maxiter': 500, 'disp': True}
    )
    
    print("\nOptimization Complete.")
    print(f"Final Loss (closer to 0 is better): {result.fun:.6e}")
    
    # Build the winning matrix
    best_S = tuner.build_unitary_S(result.x)
    
    # Evaluate across a sweep to see the new standing waves
    k_vals = np.linspace(10, 30, 2000)
    det_vals = []
    for k in k_vals:
        D = tuner.diagonal_phase_matrix(k)
        matrix = np.eye(tuner.N) - best_S @ D
        det_vals.append(np.abs(np.linalg.det(matrix)))
        
    plt.figure(figsize=(12, 6))
    plt.plot(k_vals, det_vals, label="Tuned Hub", color='purple', linewidth=2)
    
    for rz in TARGET_ZEROS:
        plt.axvline(rz, color='red', linestyle='--', alpha=0.7)
        
    plt.title("Acoustic Resonance of the Perfectly Tuned Hub")
    plt.xlabel("Frequency (k)")
    plt.ylabel("Spectral Determinant")
    plt.legend()
    plt.grid(True)
    
    plt.savefig("tuned_hub_results.png")
    print("\nGraph generated: tuned_hub_results.png")
    
    np.save("optimal_S_matrix.npy", best_S)
    print("Optimal matrix saved to optimal_S_matrix.npy")
    
if __name__ == "__main__":
    run_tuning()
