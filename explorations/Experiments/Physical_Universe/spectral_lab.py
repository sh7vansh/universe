import torch
import numpy as np
import matplotlib.pyplot as plt
import os

device = "cuda" if torch.cuda.is_available() else "cpu"
print(f"Spectral Lab running on: {device.upper()}")

# =========================================================
#      PART 1: THE MODEL (FROZEN PHYSICS)
# =========================================================

class UniverseModel:
    def __init__(self, num_nodes=120, power_law=1.05, thermal_noise_std=0.05, 
                 phase_coupling=True, node_birth=True, symmetric_network=False):
        self.num_nodes = num_nodes
        self.power_law = power_law
        self.thermal_noise_std = thermal_noise_std
        self.phase_coupling = phase_coupling
        self.node_birth = node_birth
        self.symmetric_network = symmetric_network
        self.t = 0
        self.birth_interval = 12
        
        self.phases = torch.rand(num_nodes, device=device) * 2 * torch.pi
        raw_weights = torch.rand(num_nodes, num_nodes, device=device)
        if self.symmetric_network:
            raw_weights = (raw_weights + raw_weights.T) / 2.0
            
        row_sums = raw_weights.sum(dim=1, keepdim=True)
        self.entanglement = raw_weights / row_sums

    def step_physics(self):
        # A: Resonance
        if self.phase_coupling:
            p_i = self.phases.view(-1, 1)
            p_j = self.phases.view(1, -1)
            delta_phi = torch.abs(p_i - p_j)
            desire = (torch.cos(delta_phi) + 1) / 2.0
        else:
            desire = torch.ones((self.num_nodes, self.num_nodes), device=device)

        # B: Memory
        growth = self.entanglement * desire
        new_weights = self.entanglement + (growth * 0.2)
        
        if self.thermal_noise_std > 0:
            thermal_noise = torch.rand(self.num_nodes, self.num_nodes, device=device) * self.thermal_noise_std
            if self.symmetric_network:
                thermal_noise = (thermal_noise + thermal_noise.T) / 2.0
            new_weights = new_weights + thermal_noise

        # C: Selection
        if self.symmetric_network:
            new_weights = (new_weights + new_weights.T) / 2.0
            
        sharpened = torch.pow(new_weights, self.power_law)
        row_sums = sharpened.sum(dim=1, keepdim=True)
        self.entanglement = sharpened / (row_sums + 1e-9)

        # D: Time Evolution
        if self.phase_coupling:
            phasors = torch.exp(1j * self.phases)
            weighted_sum = torch.matmul(self.entanglement.to(torch.complex64), phasors)
            noise = torch.randn(self.num_nodes, device=device) * 0.05
            self.phases = torch.angle(weighted_sum) + noise

    def birth_node(self):
        activity = self.entanglement.mean(dim=1)
        probs = activity / activity.sum()
        parents = torch.multinomial(probs, 5, replacement=True)
        parent_rows = self.entanglement[parents]

        w = torch.rand(5, device=device)
        w = w / w.sum()
        inherited = (w.view(-1,1) * parent_rows).sum(dim=0)

        epsilon = 0.25 
        noise = torch.rand_like(inherited)
        child = (1 - epsilon) * inherited + epsilon * noise
        
        if self.phase_coupling:
            parent_phases = self.phases[parents]
            phasor = torch.sum(w * torch.exp(1j * parent_phases))
            new_phase = torch.angle(phasor).view(1)
        else:
            new_phase = torch.rand(1, device=device) * 2 * torch.pi

        new_col = child.view(-1,1)
        new_row = child.view(1,-1)
        E = self.entanglement
        
        top = torch.cat([E, new_col], dim=1)
        bottom = torch.cat([new_row, torch.zeros(1,1, device=device)], dim=1)
        E2 = torch.cat([top, bottom], dim=0)

        self.entanglement = E2 / (E2.sum(dim=1, keepdim=True) + 1e-9)
        self.phases = torch.cat([self.phases, new_phase])
        self.num_nodes += 1
        
        if self.symmetric_network:
            self.entanglement = (self.entanglement + self.entanglement.T) / 2.0
            row_sums = self.entanglement.sum(dim=1, keepdim=True)
            self.entanglement = self.entanglement / (row_sums + 1e-9)

    def step(self):
        self.step_physics()
        if self.node_birth and self.t % self.birth_interval == 0:
            self.birth_node()
        self.t += 1

# =========================================================
#      PART 2: SPECTRAL DIAGNOSTICS
# =========================================================

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
        p = np.polyfit(bulk_evals, N_E, 5)
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

def construct_controls(E):
    S = (E + E.T) / 2.0
    A = (E - E.T) / 2.0
    
    H1 = S
    H2 = S + 1j * A
    
    E_flat = E.flatten()
    np.random.shuffle(E_flat)
    E_rand = E_flat.reshape(E.shape)
    S_rand = (E_rand + E_rand.T) / 2.0
    A_rand = (E_rand - E_rand.T) / 2.0
    H3 = S_rand + 1j * A_rand
    
    return H1, H2, H3

# =========================================================
#      PART 3: EXPERIMENTAL PROTOCOLS
# =========================================================

def run_control_matrix_experiment():
    print("\n--- EXPERIMENT 1: Control Matrix ---")
    uni = UniverseModel()
    for _ in range(200):
        uni.step()
        
    E = uni.entanglement.detach().cpu().numpy()
    H1, H2, H3 = construct_controls(E)
    
    res1 = analyze_spectrum(H1, "H1 = S (Expected: GOE ~0.536)")
    res2 = analyze_spectrum(H2, "H2 = S + iA (Expected: GUE ~0.603)")
    res3 = analyze_spectrum(H3, "H3 = Randomized (Expected: Poisson ~0.386 or GOE/GUE)")
    
    for res in [res1, res2, res3]:
        print(f"{res['title']}: <r> = {res['r_mean']:.4f}")
        
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    axes[0].hist(res2['evals'], bins=50, color='blue', alpha=0.7)
    axes[0].set_title("Full Spectrum")
    axes[1].hist(res2['bulk'], bins=50, color='green', alpha=0.7)
    axes[1].set_title("Bulk Spectrum")
    axes[2].hist(res2['outliers'], bins=max(1, len(res2['outliers'])), color='red', alpha=0.7)
    axes[2].set_title("Outliers")
    plt.suptitle("Spectrum of H2 = S + iA")
    plt.tight_layout()
    plt.savefig("Results_Quantum_Chaos/control_spectra.png")
    plt.close()

def run_time_evolution_experiment(num_runs=10):
    print(f"\n--- EXPERIMENT 2: Time Evolution (Averaged over {num_runs} runs) ---")
    timepoints = [0, 1, 2, 5, 10, 20, 50, 100, 200, 500]
    
    r_means = {t: [] for t in timepoints}
    
    for run in range(num_runs):
        uni = UniverseModel()
        for t in range(501):
            if t in timepoints:
                E = uni.entanglement.detach().cpu().numpy()
                _, H2, _ = construct_controls(E)
                res = analyze_spectrum(H2)
                if not np.isnan(res['r_mean']):
                    r_means[t].append(res['r_mean'])
            uni.step()
            
    avg_r = [np.mean(r_means[t]) if len(r_means[t]) > 0 else np.nan for t in timepoints]
    std_r = [np.std(r_means[t]) if len(r_means[t]) > 0 else 0 for t in timepoints]
    
    for t, r in zip(timepoints, avg_r):
        print(f"t={t}: <r> = {r:.4f}")
        
    plt.figure(figsize=(8, 5))
    plt.errorbar(timepoints, avg_r, yerr=std_r, fmt='-o', color='purple', capsize=5)
    plt.axhline(0.386, color='k', linestyle='--', label='Poisson (0.386)')
    plt.axhline(0.603, color='r', linestyle='-', label='GUE (0.603)')
    plt.axhline(0.536, color='b', linestyle='-.', label='GOE (0.536)')
    plt.xscale('symlog', linthresh=5)
    plt.xlabel('Time Step')
    plt.ylabel('Mean Adjacent Gap Ratio <r>')
    plt.title('Dynamical Transition of Spectral Statistics')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig("Results_Quantum_Chaos/time_evolution.png")
    plt.close()

def run_ablation_study():
    print("\n--- EXPERIMENT 3: Ablation Study (at t=200) ---")
    
    ablations = {
        "Baseline": {},
        "No phase coupling": {"phase_coupling": False},
        "No thermal noise": {"thermal_noise_std": 0.0},
        "No nonlinear selection": {"power_law": 1.0},
        "Symmetric network": {"symmetric_network": True},
        "No node birth": {"node_birth": False}
    }
    
    results = {}
    
    for name, kwargs in ablations.items():
        print(f"Running ablation: {name}")
        r_vals = []
        for _ in range(5): 
            uni = UniverseModel(**kwargs)
            for _ in range(200):
                uni.step()
            E = uni.entanglement.detach().cpu().numpy()
            _, H2, _ = construct_controls(E)
            res = analyze_spectrum(H2)
            if not np.isnan(res['r_mean']):
                r_vals.append(res['r_mean'])
        
        mean_r = np.mean(r_vals) if len(r_vals) > 0 else np.nan
        results[name] = mean_r
        print(f"  -> <r> = {mean_r:.4f}")
        
    plt.figure(figsize=(10, 6))
    names = list(results.keys())
    vals = list(results.values())
    plt.barh(names, vals, color='teal', alpha=0.7)
    plt.axvline(0.386, color='k', linestyle='--', label='Poisson (0.386)')
    plt.axvline(0.603, color='r', linestyle='-', label='GUE (0.603)')
    plt.xlabel('Mean Adjacent Gap Ratio <r>')
    plt.title('Ablation Study: Which ingredient causes GUE?')
    plt.legend()
    plt.tight_layout()
    plt.savefig("Results_Quantum_Chaos/ablation_study.png")
    plt.close()

if __name__ == "__main__":
    os.makedirs("Results_Quantum_Chaos", exist_ok=True)
    print("=========================================================")
    print("SPECTRAL LABORATORY: RIGOROUS TESTING OF GUE UNIVERSALITY")
    print("=========================================================")
    run_control_matrix_experiment()
    run_time_evolution_experiment(num_runs=10) 
    run_ablation_study()
    print("\nAll experiments complete. Results saved in Results_Quantum_Chaos/")
