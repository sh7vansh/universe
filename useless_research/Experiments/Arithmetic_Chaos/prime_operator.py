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

def construct_H_N(N, weight_func, eta=0.0):
    """
    Constructs the N x N Hamiltonian matrix H_N = S + i*eta*D
    where T_p |n> = |pn>.
    """
    primes = get_primes(N)
    H = np.zeros((N, N), dtype=np.complex128)
    
    for p in primes:
        w_p = weight_func(p)
        for n in range(1, N//p + 1):
            m = p * n
            idx_m = m - 1
            idx_n = n - 1
            
            # H_{m, n} = w_p * (1 + i*eta)
            # H_{n, m} = w_p * (1 - i*eta)
            H[idx_m, idx_n] += w_p * (1 + 1j * eta)
            H[idx_n, idx_m] += w_p * (1 - 1j * eta)
            
    return H

def analyze_spectrum(H, title="Spectrum"):
    """
    Computes eigenvalues, separates outliers algorithmically,
    unfolds the bulk spectrum, and computes the adjacent gap ratio <r>.
    """
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
    # Filter negative/zero spacings from polynomial artifacts
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

def run_prime_experiments():
    N = 3000
    print(f"\n--- Constructing Prime Arithmetic Operators (N={N}) ---")
    
    weight_schemes = {
        "Uniform (w_p = 1)": lambda p: 1.0,
        "Prime-suppressed (w_p = 1/p)": lambda p: 1.0 / p,
        "Prime-suppressed (w_p = 1/sqrt(p))": lambda p: 1.0 / np.sqrt(p),
        "Logarithmic (w_p = log p)": lambda p: np.log(p),
        "Sqrt-Log (w_p = log p / sqrt(p))": lambda p: np.log(p) / np.sqrt(p)
    }
    
    etas = [0.0, 0.25, 0.5, 1.0]
    
    for w_name, w_func in weight_schemes.items():
        print(f"\nWeight Scheme: {w_name}")
        for eta in etas:
            H = construct_H_N(N, w_func, eta=eta)
            res = analyze_spectrum(H)
            r = res['r_mean']
            print(f"  eta = {eta:.2f} -> <r> = {r:.4f}")

            # Plot histogram for eta=0.0 and eta=1.0
            if eta == 1.0 or eta == 0.0:
                s = res['s']
                if len(s) > 0:
                    normalized_s = s / np.mean(s)
                    plt.figure(figsize=(6, 4))
                    plt.hist(normalized_s, bins=min(100, int(len(normalized_s)/10)), 
                             density=True, alpha=0.6, color='cyan', edgecolor='black')
                    
                    x = np.linspace(0, 4, 100)
                    plt.plot(x, np.exp(-x), 'k--', alpha=0.5, label='Poisson (0.386)')
                    plt.plot(x, (np.pi/2)*x*np.exp(-np.pi/4*x**2), 'b-', alpha=0.7, label='GOE (0.536)')
                    plt.plot(x, (32/np.pi**2)*(x**2)*np.exp(-(4/np.pi)*x**2), 'r-', linewidth=2, label='GUE (0.603)')
                    
                    plt.title(f"{w_name} | eta={eta:.2f}\n<r> = {r:.4f}")
                    plt.xlabel("Normalized Spacing (s)")
                    plt.ylabel("P(s)")
                    plt.legend()
                    plt.grid(True, alpha=0.3)
                    
                    safe_name = w_name.split('(')[0].strip().replace(' ', '_').lower()
                    plt.savefig(f"Results_Quantum_Chaos/prime_{safe_name}_eta_{eta:.2f}.png")
                    plt.close()

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    print("=========================================================")
    print("ARITHMETIC OPERATOR: SPECTRAL STATISTICS OF PRIMES")
    print("=========================================================")
    run_prime_experiments()
    print("\nAll experiments complete. Results saved in Results_Quantum_Chaos/")
