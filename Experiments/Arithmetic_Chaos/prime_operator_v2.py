import numpy as np
import matplotlib.pyplot as plt
import os

def get_primes(N):
    is_p = np.ones(N+1, dtype=bool)
    is_p[0:2] = False
    for i in range(2, int(np.sqrt(N)) + 1):
        if is_p[i]:
            is_p[i*i::i] = False
    return np.where(is_p)[0]

def prime_factors(n, primes):
    v = {}
    temp = n
    for p in primes:
        if p * p > temp:
            if temp > 1:
                v[temp] = v.get(temp, 0) + 1
            break
        while temp % p == 0:
            v[p] = v.get(p, 0) + 1
            temp //= p
    return v

def construct_H_v2(N, w_func, V_func, Phi=0.0):
    """
    Constructs the N x N Hamiltonian matrix H = H_0 + V + Flux
    H_{np, n} = w_p * exp(i * A_p(n))
    A_p(n) = Phi * sum_q sign(p-q) v_q(n)
    """
    primes = get_primes(N)
    H = np.zeros((N, N), dtype=np.complex128)
    
    # Precompute prime factorizations to speed up A_p(n) calculation
    v_dict = {1: {}}
    for n in range(2, N+1):
        v_dict[n] = prime_factors(n, primes)
        
    for n in range(1, N+1):
        idx_n = n - 1
        
        # Diagonal potential V(n)
        H[idx_n, idx_n] = V_func(n)
        
        # Off-diagonal hopping
        for p in primes:
            m = n * p
            if m > N:
                break
            idx_m = m - 1
            
            # Calculate gauge phase A_p(n)
            A_pn = 0.0
            if Phi != 0.0:
                for q, v_q in v_dict[n].items():
                    if p > q:
                        A_pn += Phi * v_q
                    elif p < q:
                        A_pn -= Phi * v_q
                        
            w_p = w_func(p)
            val = w_p * np.exp(1j * A_pn)
            
            H[idx_m, idx_n] += val
            H[idx_n, idx_m] += np.conj(val)
            
    return H

def analyze_spectrum(H, title="Spectrum"):
    evals = np.linalg.eigvalsh(H)
    evals = np.sort(evals)
    
    spacings = np.diff(evals)
    if len(spacings) == 0:
        return {'r_mean': np.nan, 'evals': evals, 'bulk': evals, 'outliers': [], 's': []}
        
    mean_gap = np.mean(spacings)
    
    bulk_evals = evals
    outliers = []
    
    if len(spacings) > 0 and spacings[-1] > 5 * mean_gap:
        bulk_evals = evals[:-1]
        outliers.append(evals[-1])
        spacings = spacings[:-1]
        
    if len(spacings) > 0 and spacings[0] > 5 * mean_gap:
        bulk_evals = bulk_evals[1:]
        outliers.append(evals[0])
        spacings = spacings[1:]
        
    outliers = np.array(outliers)
    
    if len(bulk_evals) < 10:
        return {'r_mean': np.nan, 'evals': evals, 'bulk': bulk_evals, 'outliers': outliers, 's': []}
        
    N_E = np.arange(1, len(bulk_evals) + 1)
    
    try:
        p = np.polyfit(bulk_evals, N_E, 7)
        N_bar = np.polyval(p, bulk_evals)
    except np.RankWarning:
        N_bar = N_E
        
    s = np.diff(N_bar)
    s = s[s > 1e-4]
    
    if len(s) < 2:
        r_mean = np.nan
    else:
        s1 = s[:-1]
        s2 = s[1:]
        r_i = np.minimum(s1, s2) / np.maximum(s1, s2)
        r_mean = np.mean(r_i)
        
    return {
        'r_mean': r_mean,
        'evals': evals,
        'bulk': bulk_evals,
        'outliers': outliers,
        's': s,
        'title': title
    }

def run_experiments():
    N = 3000
    print(f"\n--- ARITHMETIC OPERATOR V2 (N={N}) ---")
    
    # We will use w_p = 1 / sqrt(p) for stability
    w_func = lambda p: 1.0 / np.sqrt(p)
    
    print("\n--- EXPERIMENT 1: The Symmetry Ladder ---")
    
    # Model A: Integrable baseline
    H0 = construct_H_v2(N, w_func, lambda n: 0.0, Phi=0.0)
    res0 = analyze_spectrum(H0)
    print(f"H0 (Integrable): <r> = {res0['r_mean']:.4f}")
    
    # Model B: Arithmetic potential (Chaotic scattering, GOE class)
    H_V = construct_H_v2(N, w_func, lambda n: np.log(n), Phi=0.0)
    res_V = analyze_spectrum(H_V)
    print(f"H0 + V (GOE-like?): <r> = {res_V['r_mean']:.4f}")
    
    # Model C: Frustrated arithmetic flux (Time-reversal broken, GUE class)
    H_Phi = construct_H_v2(N, w_func, lambda n: np.log(n), Phi=0.5)
    res_Phi = analyze_spectrum(H_Phi)
    print(f"H0 + V + Phi (GUE-like?): <r> = {res_Phi['r_mean']:.4f}")
    
    print("\n--- EXPERIMENT 2: Flux Scan ---")
    flux_values = [0.0, 0.1, 0.25, 0.5, np.pi/4, np.pi/2, np.pi]
    flux_labels = ["0", "0.1", "0.25", "0.5", "pi/4", "pi/2", "pi"]
    
    r_vals = []
    for phi, label in zip(flux_values, flux_labels):
        H = construct_H_v2(N, w_func, lambda n: np.log(n), Phi=phi)
        res = analyze_spectrum(H)
        r = res['r_mean']
        r_vals.append(r)
        print(f"  Phi = {label:>4} -> <r> = {r:.4f}")
        
    # Plot crossover
    plt.figure(figsize=(8, 5))
    plt.plot(flux_values, r_vals, 'o-', color='purple', linewidth=2)
    plt.axhline(0.386, color='k', linestyle='--', label='Poisson (0.386)')
    plt.axhline(0.536, color='b', linestyle='-.', label='GOE (0.536)')
    plt.axhline(0.603, color='r', linestyle='-', label='GUE (0.603)')
    plt.xlabel('Arithmetic Magnetic Flux (Phi)')
    plt.ylabel('Mean Adjacent Gap Ratio <r>')
    plt.title('GOE -> GUE Crossover in the Prime Lattice')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig("Results_Quantum_Chaos/prime_flux_crossover.png")
    plt.close()

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    run_experiments()
    print("\nAll experiments complete.")
