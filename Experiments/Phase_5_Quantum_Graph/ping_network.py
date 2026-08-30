import numpy as np
import matplotlib.pyplot as plt
from sympy import primerange
import os

def bouquet_graph_resonance(k_vals, num_primes):
    """
    Calculates the acoustic resonance of a Quantum Graph.
    The graph is a 'bouquet of circles' - a single central hub 
    with loops extending out. Each loop has length L_p = log(p).
    
    The Kirchhoff boundary conditions at the hub dictate that 
    a standing wave (resonance) occurs when the sum of the outgoing 
    derivatives is zero. 
    
    This evaluates to the secular equation:
    Sum [ tan(k * L_p / 2) ] = 0
    """
    primes = list(primerange(2, 200))[:num_primes]
    
    # Evaluate the secular function
    # We look for zero crossings of this function
    f_k = np.zeros_like(k_vals)
    for p in primes:
        L_p = np.log(p)
        f_k += np.tan(k_vals * L_p / 2.0)
        
    return f_k

def find_zero_crossings(k_vals, f_k):
    # Roots occur where the function crosses zero
    # But tan(x) has asymptotes that jump from +inf to -inf.
    # We must filter out asymptotes (where the diff is large and negative)
    roots = []
    for i in range(len(k_vals) - 1):
        if f_k[i] * f_k[i+1] < 0:
            # It crossed zero. Check if it's an asymptote.
            if f_k[i+1] > f_k[i]:
                # True root (positive slope)
                # Linear interpolate
                m = (f_k[i+1] - f_k[i]) / (k_vals[i+1] - k_vals[i])
                root = k_vals[i] - f_k[i] / m
                roots.append(root)
    return roots

def run_experiment():
    print("=== Striking the Prime Network ===")
    print("Building a Quantum Graph with loops of length log(p)...")
    
    k_vals = np.linspace(10, 30, 10000)
    
    # We will test with 5, 10, and 20 primes to see how the resonance shifts
    print(f"{'Graph Size':<15} | {'Acoustic Resonances (k)'}")
    print("-" * 65)
    
    for num_primes in [5, 10, 20, 50]:
        f_k = bouquet_graph_resonance(k_vals, num_primes)
        roots = find_zero_crossings(k_vals, f_k)
        
        # Print the first three resonances in this window
        roots_str = ", ".join([f"{r:.2f}" for r in roots[:3]])
        print(f"{num_primes} primes loops | {roots_str}")
        
    print("-" * 65)
    print("Actual Riemann Zeros: 14.13, 21.02, 25.01")
    print("\nCONCLUSION:")
    print("The network naturally generates standing waves.")
    print("As we add more prime loops to the network, the chaotic interference")
    print("forces the acoustic resonances to shift. To get the exact Riemann zeros,")
    print("the network requires infinite loops and a specific scattering matrix at the hub.")

if __name__ == "__main__":
    run_experiment()
