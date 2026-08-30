import numpy as np
import matplotlib.pyplot as plt
from sympy import primerange
from scipy.stats import unitary_group
import os

class ScatteringLab:
    def __init__(self, num_primes=15):
        self.primes = list(primerange(2, 200))[:num_primes]
        self.N = len(self.primes)
        
    def diagonal_phase_matrix(self, k):
        """
        The phase accumulated by the wave traveling around each prime loop.
        D_jj = exp(i * k * log(p_j)) = p_j^(i*k)
        We also inject the 1/sqrt(p) amplitude here to model the classical stability
        required by the explicit formula.
        """
        D = np.zeros((self.N, self.N), dtype=complex)
        for j, p in enumerate(self.primes):
            # The 1/sqrt(p) forces the system onto the 1/2 critical line.
            amplitude = 1.0 / np.sqrt(p) 
            phase = np.exp(1j * k * np.log(p))
            D[j, j] = amplitude * phase
        return D

    def spectral_determinant(self, S, k_vals):
        """
        Calculates the resonance of the network.
        Acoustic resonance occurs when Det(I - S * D) approaches 0.
        S is the scattering matrix at the hub.
        D is the phase accumulation matrix of the loops.
        """
        det_vals = []
        for k in k_vals:
            D = self.diagonal_phase_matrix(k)
            # Calculate det(I - S * D)
            matrix = np.eye(self.N) - S @ D
            det_vals.append(np.abs(np.linalg.det(matrix)))
        return np.array(det_vals)

def generate_uniform_scattering(N):
    """A 'dumb' hub where a wave splits equally into all wires."""
    # To make it unitary, we use the standard discrete Fourier transform matrix
    # or a Householder reflection. We'll use a normalized DFT for perfect mixing.
    omega = np.exp(2j * np.pi / N)
    S = np.zeros((N, N), dtype=complex)
    for i in range(N):
        for j in range(N):
            S[i, j] = (omega ** (i * j)) / np.sqrt(N)
    return S

def run_lab():
    lab = ScatteringLab(num_primes=20)
    k_vals = np.linspace(10, 30, 2000)
    
    print("=== The Scattering Lab ===")
    print("Testing different hub scattering rules to find acoustic resonances.")
    print("Target Riemann Zeros: 14.13, 21.02, 25.01\n")
    
    # Test 1: Identity (Isolated loops, no mixing)
    S_id = np.eye(lab.N)
    det_id = lab.spectral_determinant(S_id, k_vals)
    
    # Test 2: Uniform Mixing (Dumb Hub)
    S_uni = generate_uniform_scattering(lab.N)
    det_uni = lab.spectral_determinant(S_uni, k_vals)
    
    # Test 3: Chaotic Mixing (Random Unitary Hub)
    S_rand = unitary_group.rvs(lab.N)
    det_rand = lab.spectral_determinant(S_rand, k_vals)
    
    # Plotting
    plt.figure(figsize=(12, 6))
    plt.plot(k_vals, det_id, label="Isolated Hub (No Mixing)", alpha=0.5)
    plt.plot(k_vals, det_uni, label="Uniform Hub (Equal Splitting)", linewidth=2)
    plt.plot(k_vals, det_rand, label="Chaotic Hub (Random Splitting)", alpha=0.5)
    
    # Mark Riemann zeros
    for rz in [14.1347, 21.0220, 25.0108]:
        plt.axvline(rz, color='red', linestyle='--', alpha=0.7)
    
    plt.title("Acoustic Resonance of the Prime Network")
    plt.xlabel("Frequency (k)")
    plt.ylabel("Spectral Determinant (Resonance at dips)")
    plt.legend()
    plt.grid(True)
    
    plt.savefig("scattering_results.png")
    print("Graph generated: scattering_results.png")
    
    # Find local minima for Uniform Hub
    from scipy.signal import find_peaks
    # We want minima, so we find peaks of the negative
    peaks, _ = find_peaks(-det_uni)
    print("Resonances found for Uniform Hub:")
    for p in peaks:
        print(f"k = {k_vals[p]:.2f}")

if __name__ == "__main__":
    run_lab()
