import numpy as np
import matplotlib.pyplot as plt
import os
import time

def get_primes(N):
    is_p = np.ones(N+1, dtype=bool)
    is_p[0:2] = False
    for i in range(2, int(np.sqrt(N)) + 1):
        if is_p[i]:
            is_p[i*i::i] = False
    return np.where(is_p)[0]

def legendre(a, p):
    if p == 2:
        return 1 if a % 2 != 0 else -1
    res = pow(int(a), int((p - 1) // 2), int(p))
    return res if res <= 1 else res - p

def get_B_matrix(primes, flux_type):
    num_p = len(primes)
    B = np.zeros((num_p, num_p))
    
    if flux_type == 'ordered':
        for i in range(num_p):
            for j in range(i+1, num_p):
                B[i, j] = 1
                B[j, i] = -1
    elif flux_type == 'random':
        np.random.seed(42) # Fixed seed for stable comparison
        for i in range(num_p):
            for j in range(i+1, num_p):
                val = np.random.choice([-1, 1])
                B[i, j] = val
                B[j, i] = -val
    elif flux_type == 'arithmetic':
        for i in range(num_p):
            for j in range(i+1, num_p):
                p = int(primes[i])
                q = int(primes[j])
                val = legendre(p, q)
                if val == 0:
                    val = 1
                B[i, j] = val
                B[j, i] = -val
    return B

def construct_H_v4(N, kappa, Phi, flux_type):
    primes = get_primes(N)
    B = get_B_matrix(primes, flux_type)
    p_idx = {p: i for i, p in enumerate(primes)}
    
    H = np.zeros((N, N), dtype=np.complex128)
    
    for n in range(1, N+1):
        idx_n = n - 1
        H[idx_n, idx_n] = np.log(n)
        
        # H0 (Addition of primes) - Real hopping
        for p in primes:
            m = n * p
            if m > N:
                break
            idx_m = m - 1
            w_p = 1.0 / np.sqrt(p)
            H[idx_m, idx_n] += w_p
            H[idx_n, idx_m] += w_p
            
        # H_exchange (n -> n * p / q) - Complex hopping
        if kappa > 0:
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
                i_q = p_idx[q]
                for p in primes:
                    if p <= q:
                        continue
                    m = (n // q) * p
                    if m > N:
                        break
                    idx_m = m - 1
                    i_p = p_idx[p]
                    
                    J_pq = 1.0 / np.sqrt(p * q)
                    val = kappa * J_pq * np.exp(1j * Phi * B[i_p, i_q])
                    
                    H[idx_m, idx_n] += val
                    H[idx_n, idx_m] += np.conj(val)
    return H

def analyze_spectrum(H):
    evals, evecs = np.linalg.eigh(H)
    k = max(1, int(0.05 * len(evals)))
    bulk_evals = evals[k:-k]
    bulk_evecs = evecs[:, k:-k]
    
    ipr = np.sum(np.abs(bulk_evecs)**4, axis=0)
    pr = 1.0 / ipr
    pr_mean = np.mean(pr)
    
    spacings = np.diff(bulk_evals)
    spacings = spacings[spacings > 1e-7]
    
    if len(spacings) < 2:
        r_mean = np.nan
    else:
        r_i = np.minimum(spacings[:-1], spacings[1:]) / np.maximum(spacings[:-1], spacings[1:])
        r_mean = np.mean(r_i)
        
    return r_mean, pr_mean

def run_v4():
    print("=========================================================")
    print("ARITHMETIC OPERATOR V4: FINITE-SIZE SCALING & FLUX MODELS")
    print("=========================================================")
    
    Ns = [500, 1000, 2000, 4000]
    flux_models = ['ordered', 'random', 'arithmetic']
    kappa = 2.0
    Phi = np.pi / 4
    
    results = {fm: {'N': [], 'r': [], 'pr': []} for fm in flux_models}
    
    print(f"\nRunning Scaling Test (kappa={kappa}, Phi=pi/4)...")
    print(f"{'Model':<12} | {'N':<5} | {'<r>':<8} | {'PR':<8} | {'PR/N (%)':<8}")
    print("-" * 50)
    
    for N in Ns:
        for fm in flux_models:
            H = construct_H_v4(N, kappa, Phi, fm)
            r, pr = analyze_spectrum(H)
            
            results[fm]['N'].append(N)
            results[fm]['r'].append(r)
            results[fm]['pr'].append(pr)
            
            pr_pct = (pr / N) * 100
            print(f"{fm:<12} | {N:<5} | {r:<8.4f} | {pr:<8.2f} | {pr_pct:<8.2f}")
            
    # Plotting
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    for fm in flux_models:
        axes[0].plot(results[fm]['N'], results[fm]['r'], 'o-', label=fm)
        axes[1].plot(results[fm]['N'], results[fm]['pr'], 'o-', label=fm)
        
    axes[0].axhline(0.386, color='k', linestyle='--', label='Poisson (0.386)')
    axes[0].axhline(0.536, color='b', linestyle='-.', label='GOE (0.536)')
    axes[0].axhline(0.603, color='r', linestyle='-', label='GUE (0.603)')
    axes[0].set_xlabel('Matrix Size (N)')
    axes[0].set_ylabel('Mean Adjacent Gap Ratio <r>')
    axes[0].set_title('Spectral Chaos vs N')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    axes[1].set_xlabel('Matrix Size (N)')
    axes[1].set_ylabel('Participation Ratio (PR)')
    axes[1].set_title('Eigenstate Delocalization vs N')
    axes[1].legend()
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig("Results_Quantum_Chaos/prime_v4_scaling.png")
    plt.close()
    
    print("\n--- Zero Flux Baseline ---")
    H_zero = construct_H_v4(4000, kappa, 0.0, 'ordered')
    r_z, pr_z = analyze_spectrum(H_zero)
    print(f"Phi=0, N=4000  -> <r> = {r_z:.4f}, PR = {pr_z:.2f}, PR/N = {(pr_z/4000)*100:.2f}%")

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    run_v4()
    print("\nAll experiments complete. Saved to prime_v4_scaling.png")
