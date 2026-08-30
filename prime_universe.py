import torch
import numpy as np
import matplotlib.pyplot as plt
import networkx as nx
from sklearn.manifold import MDS
from sympy import primerange
import time

device = "cuda" if torch.cuda.is_available() else "cpu"
print(f"Simulation running on: {device.upper()}")

# =========================================================
#      PART 1: THE PRIME "NOISE" GENERATOR
# =========================================================
# We replace all true randomness with deterministic prime sequences.
class PrimeSource:
    def __init__(self):
        # Precompute a large bank of primes
        self.primes = list(primerange(2, 2000000))
        self.cursor = 0
        
    def get_primes(self, count):
        batch = []
        while count > 0:
            available = len(self.primes) - self.cursor
            take = min(count, available)
            batch.extend(self.primes[self.cursor : self.cursor + take])
            self.cursor = (self.cursor + take) % len(self.primes)
            count -= take
        return torch.tensor(batch, dtype=torch.float32, device=device)

    def prime_rand(self, shape):
        """Generates uniform [0, 1) using the fractional part of p * log(p)"""
        count = np.prod(shape)
        p = self.get_primes(count)
        # The chaotic sequence: frac(p * log(p))
        chaos = (p * torch.log(p)) % 1.0
        return chaos.view(shape)

    def prime_randn(self, shape):
        """Generates normal distribution using Box-Muller on prime_rand"""
        count = np.prod(shape)
        # Need 2 uniform numbers for every 1 normal
        u1 = self.prime_rand((count,))
        u2 = self.prime_rand((count,))
        
        # Box-Muller transform
        z0 = torch.sqrt(-2.0 * torch.log(u1 + 1e-9)) * torch.cos(2.0 * torch.pi * u2)
        return z0.view(shape)

prime_source = PrimeSource()

# =========================================================
#      PART 2: THE PRIME UNIVERSE ENGINE
# =========================================================

class PrimeQuantumUniverse:
    """
    Identical to the ThermalQuantumUniverse, but 100% deterministic.
    Every "random" event is actually just the next prime number in the sequence.
    """
    def __init__(self, num_nodes=120, birth_interval=12):
        self.num_nodes = num_nodes
        self.birth_interval = birth_interval
        self.t = 0
        self.power_law = 1.05 
        
        # 1. INITIAL PHASES (Derived from Primes)
        self.phases = prime_source.prime_rand(num_nodes) * 2 * torch.pi
        
        # 2. INITIAL ENTANGLEMENT (Derived from Primes)
        raw_weights = prime_source.prime_rand((num_nodes, num_nodes))
        row_sums = raw_weights.sum(dim=1, keepdim=True)
        self.entanglement = raw_weights / row_sums

    def step_physics(self):
        p_i = self.phases.view(-1, 1)
        p_j = self.phases.view(1, -1)
        delta_phi = torch.abs(p_i - p_j)
        desire = (torch.cos(delta_phi) + 1) / 2.0

        growth = self.entanglement * desire
        new_weights = self.entanglement + (growth * 0.2) 
        
        # INJECT PRIME NOISE (Instead of torch.rand)
        prime_jitter = prime_source.prime_rand((self.num_nodes, self.num_nodes)) * 0.05
        new_weights = torch.relu(new_weights + prime_jitter)

        sharpened = torch.pow(new_weights, self.power_law)
        row_sums = sharpened.sum(dim=1, keepdim=True)
        self.entanglement = sharpened / (row_sums + 1e-9)
        self.entanglement = torch.nan_to_num(self.entanglement, 0.0)

        phasors = torch.exp(1j * self.phases)
        weighted_sum = torch.matmul(self.entanglement.to(torch.complex64), phasors)
        
        # INJECT PRIME NOISE (Instead of torch.randn)
        phase_noise = prime_source.prime_randn((self.num_nodes,)) * 0.05
        self.phases = torch.angle(weighted_sum) + phase_noise
        self.phases = torch.nan_to_num(self.phases, 0.0)

    def birth_node(self):
        activity = self.entanglement.mean(dim=1)
        probs = (activity + 1e-9) / (activity.sum() + 1e-9)
        parents = torch.multinomial(probs, 5, replacement=True)
        parent_rows = self.entanglement[parents]

        w = prime_source.prime_rand((5,))
        w = w / w.sum()
        inherited = (w.view(-1,1) * parent_rows).sum(dim=0)

        epsilon = 0.25 
        noise = prime_source.prime_rand_like(inherited) if hasattr(prime_source, 'prime_rand_like') else prime_source.prime_rand(inherited.shape)
        child = (1 - epsilon) * inherited + epsilon * noise

        parent_phases = self.phases[parents]
        phasor = torch.sum(w * torch.exp(1j * parent_phases))
        new_phase = torch.angle(phasor).view(1)

        new_col = child.view(-1,1)
        new_row = child.view(1,-1)
        E = self.entanglement
        
        top = torch.cat([E, new_col], dim=1)
        bottom = torch.cat([new_row, torch.zeros(1,1, device=device)], dim=1)
        E2 = torch.cat([top, bottom], dim=0)

        self.entanglement = E2 / (E2.sum(dim=1, keepdim=True) + 1e-9)
        self.phases = torch.cat([self.phases, new_phase])
        self.num_nodes += 1

    def step(self):
        self.step_physics()
        if self.t % self.birth_interval == 0:
            self.birth_node()
        self.t += 1

# =========================================================
#      PART 3: THE OBSERVER
# =========================================================

def run_riemann_gue_test(entanglement_tensor, step_num):
    print(f"\n--- Running Quantum Chaos Diagnostic at Step {step_num} ---")
    E = entanglement_tensor.detach().cpu().numpy()
    S = (E + E.T) / 2.0
    A = (E - E.T) / 2.0
    H = S + 1j * A
    
    evals = np.linalg.eigvalsh(H)
    evals = evals[:-1]
    spacings = np.diff(evals)
    
    valid_spacings = spacings[spacings > 1e-5] 
    spacings = valid_spacings
    normalized_spacings = spacings / np.mean(spacings)
    
    s = np.linspace(0, 4, 100)
    poisson = np.exp(-s)
    goe = (np.pi / 2.0) * s * np.exp(-(np.pi / 4.0) * s**2)
    gue = (32.0 / np.pi**2) * (s**2) * np.exp(-(4.0 / np.pi) * s**2)
    
    plt.figure(figsize=(10, 6))
    plt.hist(normalized_spacings, bins=max(10, int(len(normalized_spacings)/5)), 
             density=True, alpha=0.6, color='magenta', edgecolor='black', 
             label=f'Prime Universe (N={len(evals)})')
    
    plt.plot(s, poisson, 'k--', alpha=0.5, label='Poisson')
    plt.plot(s, gue, 'r-', linewidth=2, label='GUE (Riemann Zeta Chaos)')
    
    plt.title(f"Prime Operator Spectrum Analysis (Step {step_num})")
    plt.xlabel("Normalized Energy Level Spacing ($s$)")
    plt.ylabel("Probability Density $P(s)$")
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig(f"prime_gue_diagnostic.png")
    print("Graph saved as prime_gue_diagnostic.png")

def get_vitals(uni):
    E_np = uni.entanglement.detach().cpu().numpy()
    dynamic_threshold = 0.5 * (1.0 / uni.num_nodes)
    adjacency = (E_np > dynamic_threshold).astype(int) 
    G = nx.from_numpy_array(adjacency)
    degrees = [d for n, d in G.degree()]
    avg_degree = np.mean(degrees) if degrees else 0
    clustering = nx.average_clustering(G) if uni.num_nodes <= 100 else nx.average_clustering(G, nodes=np.random.choice(G.nodes(), 100))
    return avg_degree, clustering

def plot_vitals_and_geometry(uni, history):
    fig = plt.figure(figsize=(14, 6))
    
    # Plot Vitals
    ax_vitals = fig.add_subplot(1, 2, 1)
    ax_vitals.plot(history['t'], history['degree'], label='Connectivity', color='blue', linewidth=2)
    ax_vitals.axhline(y=6, color='r', linestyle='--', alpha=0.5, label='Target (6)')
    ax_vitals.set_title("Cosmic Vitals (Prime Universe)")
    ax_vitals.set_ylim(bottom=0) 
    ax_vitals.legend()
    ax_vitals.grid(True, alpha=0.3)
    
    # Plot Geometry
    ax_3d = fig.add_subplot(1, 2, 2, projection='3d')
    E_np = uni.entanglement.detach().cpu().numpy()
    dist = 1.0 / (E_np + 1e-9)
    np.fill_diagonal(dist, 0)
    dist = (dist + dist.T) / 2.0
    mds = MDS(n_components=3, dissimilarity="precomputed", max_iter=30, n_init=1)
    coords = mds.fit_transform(dist)
    ax_3d.scatter(coords[:,0], coords[:,1], coords[:,2], c=coords[:,2], cmap='plasma', s=40, alpha=0.8)
    ax_3d.set_title("Emergent Geometry (Prime Universe)")
    ax_3d.axis('off')
    
    plt.savefig("prime_vitals_geometry.png")
    print("Graph saved as prime_vitals_geometry.png")

# =========================================================
#      PART 4: EXECUTION
# =========================================================

if __name__ == "__main__":
    print("Initializing the Prime Universe...")
    uni = PrimeQuantumUniverse(num_nodes=120, birth_interval=12)
    
    history = {'t': [], 'degree': []}
    
    print("Running deterministic prime evolution for 500 steps...")
    for step in range(501):
        uni.step()
        if step % 10 == 0:
            deg, _ = get_vitals(uni)
            history['t'].append(step)
            history['degree'].append(deg)
        if step % 100 == 0:
            print(f"Step {step} completed...")
            
    run_riemann_gue_test(uni.entanglement, 500)
    plot_vitals_and_geometry(uni, history)
    print("Finished.")
