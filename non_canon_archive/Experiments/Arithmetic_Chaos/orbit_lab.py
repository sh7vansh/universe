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

def get_arithmetic_B(primes):
    num_p = len(primes)
    B = np.zeros((num_p, num_p))
    for i in range(num_p):
        for j in range(i+1, num_p):
            val = legendre(primes[i], primes[j])
            if val == 0: val = 1
            B[i, j] = val
            B[j, i] = -val
    return B

def get_random_B(num_p):
    B = np.zeros((num_p, num_p))
    for i in range(num_p):
        for j in range(i+1, num_p):
            val = np.random.choice([-1, 1])
            B[i, j] = val
            B[j, i] = -val
    return B

def compute_Tr_H3(N, primes, B, kappa, Phi):
    num_p = len(primes)
    tr = 0
    
    # Type A (2 T edges, 1 R edge)
    for i in range(num_p):
        for j in range(i+1, num_p):
            p = primes[i]
            q = primes[j]
            N_nodes = int(min(N/p, N/q))
            tr += 6 * (kappa / (p * q)) * np.cos(Phi * B[j, i]) * N_nodes
            
    # Type B (3 R edges)
    for i in range(num_p):
        for j in range(i+1, num_p):
            for k in range(j+1, num_p):
                p = primes[i]
                q = primes[j]
                r = primes[k]
                N_nodes = int(N / max(q*r, p*r, p*q))
                if N_nodes > 0:
                    flux = B[i, j] + B[j, k] + B[k, i]
                    tr += 6 * (kappa**3 / (p * q * r)) * np.cos(Phi * flux) * N_nodes
                
    return tr

def compute_Cp_L3_vec(primes, B_ensemble, kappa, Phi):
    P = len(primes)
    K = B_ensemble.shape[0]
    
    inv_p = 1.0 / primes
    pq_mat = np.outer(inv_p, inv_p)
    np.fill_diagonal(pq_mat, 0)
    
    cos_A = np.cos(Phi * B_ensemble) 
    term_A = 2 * kappa * pq_mat[np.newaxis, :, :] * cos_A
    Cp_A = np.sum(term_A, axis=2)
    
    idx_j, idx_k = np.triu_indices(P, k=1)
    inv_qr = inv_p[idx_j] * inv_p[idx_k]
    B_jk = B_ensemble[:, idx_j, idx_k]
    
    Cp_B = np.zeros((K, P))
    
    for i in range(P):
        valid_mask = (idx_j != i) & (idx_k != i)
        
        v_j = idx_j[valid_mask]
        v_k = idx_k[valid_mask]
        v_inv_qr = inv_qr[valid_mask]
        
        B_ij = B_ensemble[:, i, v_j]
        B_ki = B_ensemble[:, v_k, i]
        v_B_jk = B_jk[:, valid_mask]
        
        flux = B_ij + v_B_jk + B_ki
        cos_B = np.cos(Phi * flux) 
        
        term = 2 * (kappa**3) * inv_p[i] * v_inv_qr 
        Cp_B[:, i] = np.sum(cos_B * term, axis=1)
        
    return Cp_A + Cp_B

def run_orbit_lab():
    print("=========================================================")
    print("ORBIT LAB: PRIMITIVE CYCLE AMPLITUDES (VECTORIZED)")
    print("=========================================================\n")
    
    kappa = 2.0
    Phi = np.pi / 4
    primes = get_primes(500)
    num_p = len(primes)
    
    print("\n--- Computing Random Flux Ensemble (1000 realizations) ---")
    num_realizations = 1000
    B_rand_ensemble = np.zeros((num_realizations, num_p, num_p))
    for r in range(num_realizations):
        B_rand_ensemble[r] = get_random_B(num_p)
        
    Cp_rand_ensemble = compute_Cp_L3_vec(primes, B_rand_ensemble, kappa, Phi)
    Cp_rand_mean = np.mean(Cp_rand_ensemble, axis=0)
    Cp_rand_std = np.std(Cp_rand_ensemble, axis=0)
    
    print("--- Computing Arithmetic Flux ---")
    B_arith = get_arithmetic_B(primes)
    Cp_arith = compute_Cp_L3_vec(primes, B_arith[np.newaxis, :, :], kappa, Phi)[0]
    
    plt.figure(figsize=(14, 6))
    
    plt.subplot(1, 2, 1)
    plt.plot(primes, Cp_arith, 'ro', markersize=4, label='Arithmetic (Legendre)')
    plt.fill_between(primes, Cp_rand_mean - 2*Cp_rand_std, Cp_rand_mean + 2*Cp_rand_std, 
                     color='gray', alpha=0.3, label='Random Ensemble (95%)')
    plt.plot(primes, Cp_rand_mean, 'k--', label='Random Mean')
    plt.xlabel('Prime p')
    plt.ylabel('Primitive Orbit Amplitude C_p(L=3)')
    plt.title('C_p vs p (Linear Scale)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 2, 2)
    plt.loglog(primes, np.abs(Cp_arith), 'ro', markersize=4, label='Arithmetic')
    plt.loglog(primes, np.abs(Cp_rand_mean), 'k--', label='Random Mean')
    
    ref_1_p = 50 * kappa / primes
    ref_1_p2 = 50 * kappa / primes**2
    ref_log_p_sqrt = 5 * kappa * np.log(primes) / np.sqrt(primes)
    
    plt.loglog(primes, ref_1_p, 'b:', label='~ 1/p')
    plt.loglog(primes, ref_1_p2, 'g:', label='~ 1/p^2')
    plt.loglog(primes, ref_log_p_sqrt, 'm:', label='~ log(p)/sqrt(p)')
    
    plt.xlabel('Prime p')
    plt.ylabel('|C_p|')
    plt.title('Scaling of Orbit Amplitude (Log-Log)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('Results_Quantum_Chaos/orbit_lab_L3.png')
    plt.close()
    
    print("\nDone. Saved to orbit_lab_L3.png")

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    run_orbit_lab()
