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
        np.random.seed(42) 
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

def construct_H_trace(N, kappa, Phi, flux_type, use_potential=True):
    primes = get_primes(N)
    B = get_B_matrix(primes, flux_type)
    p_idx = {p: i for i, p in enumerate(primes)}
    H = np.zeros((N, N), dtype=np.complex128)
    
    for n in range(1, N+1):
        idx_n = n - 1
        if use_potential:
            H[idx_n, idx_n] = np.log(n)
            
        for p in primes:
            m = n * p
            if m > N:
                break
            w_p = 1.0 / np.sqrt(p)
            H[m-1, idx_n] += w_p
            H[idx_n, m-1] += w_p
            
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
                    
                    J_pq = 1.0 / np.sqrt(p * q)
                    val = kappa * J_pq * np.exp(1j * Phi * B[p_idx[p], i_q])
                    H[m-1, idx_n] += val
                    H[idx_n, m-1] += np.conj(val)
    return H

def compute_SFF(evals, t_array):
    """ Computes the Spectral Form Factor K(t) = |Z(t)|^2 """
    Z_t = np.array([np.sum(np.exp(-1j * t * evals)) for t in t_array])
    K_t = np.abs(Z_t)**2
    return Z_t, K_t

def run_trace_experiment():
    N = 2000
    kappa = 2.0
    Phi = np.pi / 4
    flux_models = ['ordered', 'random', 'arithmetic']
    
    print(f"\n=========================================================")
    print(f"ARITHMETIC TRACE: PERIODIC ORBITS & SFF (N={N})")
    print(f"=========================================================\n")
    
    t_array = np.linspace(0, 50, 1000)
    
    for use_pot in [False, True]:
        pot_label = "V=log(n)" if use_pot else "V=0"
        print(f"\n--- Running Potential: {pot_label} ---")
        
        plt.figure(figsize=(15, 10))
        
        for i, fm in enumerate(flux_models):
            print(f"Processing flux model: {fm}...")
            H = construct_H_trace(N, kappa, Phi, fm, use_potential=use_pot)
            evals = np.linalg.eigvalsh(H)
            
            # Density of States
            plt.subplot(2, 3, i+1)
            plt.hist(evals, bins=50, color='teal', alpha=0.7, density=True)
            plt.title(f"Density of States\n{fm} flux ({pot_label})")
            
            # Spectral Form Factor K(t)
            Z_t, K_t = compute_SFF(evals, t_array)
            plt.subplot(2, 3, i+4)
            plt.semilogy(t_array, K_t, color='purple', alpha=0.8)
            plt.title(f"Spectral Form Factor K(t)\n{fm} flux")
            plt.xlabel("Time t")
            
            # Moments (Closed walks of length L)
            print(f"  Closed walk amplitudes Tr(H^L) for {fm}:")
            for L in range(2, 7): # up to 6
                Tr_L = np.sum(evals**L)
                print(f"    L={L}: {Tr_L.real:.2f}")
                
        plt.tight_layout()
        safe_pot = "v_log" if use_pot else "v_0"
        plt.savefig(f"Results_Quantum_Chaos/prime_trace_{safe_pot}.png")
        plt.close()

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    run_trace_experiment()
    print("\nAll experiments complete.")
