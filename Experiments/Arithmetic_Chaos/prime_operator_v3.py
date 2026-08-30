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

def construct_H_v3(N, kappa, Phi):
    primes = get_primes(N)
    H = np.zeros((N, N), dtype=np.complex128)
    
    for n in range(1, N+1):
        idx_n = n - 1
        
        # 1. Diagonal potential V(n) = log(n)
        H[idx_n, idx_n] = np.log(n)
        
        # 2. H0 (Addition/Removal of primes)
        for p in primes:
            m = n * p
            if m > N:
                break
            idx_m = m - 1
            w_p = 1.0 / np.sqrt(p)
            H[idx_m, idx_n] += w_p
            H[idx_n, idx_m] += w_p
            
        # 3. H_exchange (Exchange of primes: n -> n * p / q)
        if kappa > 0:
            # Find prime factors of n
            factors = []
            temp = n
            for p in primes:
                if p * p > temp:
                    if temp > 1:
                        factors.append(temp)
                    break
                if temp % p == 0:
                    factors.append(p)
                    while temp % p == 0:
                        temp //= p
                        
            for q in factors:
                for p in primes:
                    # We only process p > q to avoid double-counting undirected edges
                    if p <= q:
                        continue
                    m = (n // q) * p
                    if m > N:
                        break
                    idx_m = m - 1
                    
                    J_pq = 1.0 / np.sqrt(p * q)
                    # Phase is Phi * sign(p-q). Since p > q, sign is +1.
                    val = kappa * J_pq * np.exp(1j * Phi)
                    
                    H[idx_m, idx_n] += val
                    H[idx_n, idx_m] += np.conj(val)
                    
    return H

def analyze_spectrum(H):
    # Diagonalize
    evals, evecs = np.linalg.eigh(H)
    
    # Drop top and bottom 5% as outliers (macroscopic roots, edge states)
    k = max(1, int(0.05 * len(evals)))
    bulk_evals = evals[k:-k]
    bulk_evecs = evecs[:, k:-k]
    
    # 1. Participation Ratio (PR)
    # PR_j = 1 / sum_n |psi_j(n)|^4
    ipr = np.sum(np.abs(bulk_evecs)**4, axis=0)
    pr = 1.0 / ipr
    pr_mean = np.mean(pr)
    
    # 2. Raw Adjacent Gap Ratio <r>
    # r_i is scale invariant, so we don't need polynomial unfolding!
    spacings = np.diff(bulk_evals)
    spacings = spacings[spacings > 1e-7] # Filter degeneracies
    
    if len(spacings) < 2:
        r_mean = np.nan
    else:
        r_i = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
        r_mean = np.mean(r_i)
        
    return {
        'r_mean': r_mean,
        'pr_mean': pr_mean,
        'evals': evals
    }

def run_experiments():
    N = 3000
    print(f"\n=========================================================")
    print(f"ARITHMETIC OPERATOR V3: CONDUCTIVITY & CHAOS (N={N})")
    print(f"=========================================================\n")
    
    kappas = [0.0, 0.1, 0.25, 0.5, 1.0, 2.0]
    phis = [0.0, np.pi/4]
    
    results = {}
    
    print(f"{'kappa':<8} | {'Phi':<8} | {'<r>':<8} | {'PR':<8}")
    print("-" * 40)
    
    for kappa in kappas:
        for phi in phis:
            H = construct_H_v3(N, kappa, phi)
            res = analyze_spectrum(H)
            
            r = res['r_mean']
            pr = res['pr_mean']
            phi_label = "0" if phi == 0.0 else "pi/4"
            
            print(f"{kappa:<8.2f} | {phi_label:<8} | {r:<8.4f} | {pr:<8.2f}")
            results[(kappa, phi)] = (r, pr)
            
    # Plotting PR vs Kappa
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    k_vals = kappas
    pr_0 = [results[(k, 0.0)][1] for k in kappas]
    pr_phi = [results[(k, np.pi/4)][1] for k in kappas]
    
    plt.plot(k_vals, pr_0, 'b-o', label='Phi = 0')
    plt.plot(k_vals, pr_phi, 'r-s', label='Phi = pi/4')
    plt.xlabel('Arithmetic Connectivity (kappa)')
    plt.ylabel('Mean Participation Ratio (PR)')
    plt.title('Eigenstate Delocalization')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # Plotting <r> vs Kappa
    plt.subplot(1, 2, 2)
    r_0 = [results[(k, 0.0)][0] for k in kappas]
    r_phi = [results[(k, np.pi/4)][0] for k in kappas]
    
    plt.plot(k_vals, r_0, 'b-o', label='Phi = 0')
    plt.plot(k_vals, r_phi, 'r-s', label='Phi = pi/4')
    plt.axhline(0.386, color='k', linestyle='--', label='Poisson (0.386)')
    plt.axhline(0.536, color='b', linestyle='-.', label='GOE (0.536)')
    plt.axhline(0.603, color='r', linestyle='-', label='GUE (0.603)')
    plt.xlabel('Arithmetic Connectivity (kappa)')
    plt.ylabel('Mean Adjacent Gap Ratio <r>')
    plt.title('Spectral Chaos Transition')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig("Results_Quantum_Chaos/prime_v3_conductivity.png")
    plt.close()

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    run_experiments()
    print("\nAll experiments complete. Saved to prime_v3_conductivity.png")
