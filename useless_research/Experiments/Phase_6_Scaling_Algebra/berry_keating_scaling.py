import numpy as np
from scipy.optimize import root_scalar
import os

def riemann_von_mangoldt(E):
    """
    The continuous volume of the scaled phase space.
    This equation naturally emerges from integrating the scaling operator 
    D = x(d/dx) + 1/2 over a truncated phase space.
    It represents the number of standing waves with frequency < E.
    """
    # Riemann-von Mangoldt formula for the smoothed counting function of Riemann zeros
    term1 = (E / (2 * np.pi)) * np.log(E / (2 * np.pi))
    term2 = -(E / (2 * np.pi))
    term3 = 7.0 / 8.0
    return term1 + term2 + term3

def target_resonance(E, n):
    """
    We want to find the energy level E where the phase space volume 
    perfectly fits exactly 'n' complete standing waves.
    N(E) = n - 0.5 (semiclassical quantization condition)
    """
    return riemann_von_mangoldt(E) - (n - 0.5)

def run_scaling_algebra():
    import matplotlib.pyplot as plt
    from mpmath import zetazero
    import warnings
    warnings.filterwarnings("ignore")

    print("=== Phase 6: Continuous Scaling Algebra (Extended) ===")
    print("Mapping the first 50 zeros using the pure scaling operator...\n")
    
    # Get actual Riemann zeros using mpmath
    actual_zeros = [float(zetazero(n).imag) for n in range(1, 51)]
    
    calculated_zeros = []
    for n in range(1, 51):
        # Solve for E where the wave perfectly fits the space
        res = root_scalar(target_resonance, args=(n,), bracket=[10, 200])
        calculated_zeros.append(res.root)

    print(f"{'n (Wave #)':<12} | {'Calculated (Scaling)':<20} | {'Actual (Riemann)'}")
    print("-" * 60)
    for n in range(1, 6): # Just print first 5 to console
        print(f"{n:<12} | {calculated_zeros[n-1]:<20.4f} | {actual_zeros[n-1]:.4f}")
    print("... (calculated 50 zeros) ...")
    print(f"{50:<12} | {calculated_zeros[-1]:<20.4f} | {actual_zeros[-1]:.4f}")

    # Generate a plot to visualize the alignment
    plt.figure(figsize=(10, 6))
    plt.plot(range(1, 51), actual_zeros, 'ro', label='Actual Riemann Zeros (Discrete Primes)', alpha=0.6)
    plt.plot(range(1, 51), calculated_zeros, 'b-', label='Scaling Operator (Smooth Expansion)', linewidth=2)
    plt.title("Scaling Operator Prediction vs Actual Riemann Zeros")
    plt.xlabel("n (Wave Number)")
    plt.ylabel("Frequency (Imaginary Part)")
    plt.legend()
    plt.grid(True)
    plt.savefig("scaling_operator_50_zeros.png")
    print("\nGraph saved as scaling_operator_50_zeros.png")

if __name__ == "__main__":
    run_scaling_algebra()
