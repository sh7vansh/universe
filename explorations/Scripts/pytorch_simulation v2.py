import torch
import numpy as np
import matplotlib.pyplot as plt
import networkx as nx
from sklearn.manifold import MDS
import time

# =========================================================
#      PART 1: LABORATORY CONFIGURATION
# =========================================================

# Check for GPU (CUDA). 
# In your theory, the universe processes all events simultaneously (Parallelism).
# Using a GPU simulates this "Massively Parallel" nature of reality.
device = "cuda" if torch.cuda.is_available() else "cpu"
print(f"Simulation running on: {device.upper()}")

# =========================================================
#      PART 2: THE ENGINE OF REALITY
# =========================================================

class ThermalQuantumUniverse:
    """
    A simulation of a universe built from a network of indivisible events.
    
    Theory Compliance:
    1. INDIVISIBLE: Nodes are discrete integer units (1, 2, 3...), not continuous fields.
    2. NON-MARKOVIAN: The network builds upon its own history (Hebbian Memory).
    3. STOCHASTIC: Random noise is injected at every step (Quantum Jitter).
    """

    def __init__(self, num_nodes=150, birth_interval=12):
        
        self.num_nodes = num_nodes
        self.birth_interval = birth_interval # Rate of Cosmic Expansion (New events per tick)
        self.t = 0
        
        # --- THE FINE-TUNING CONSTANT ---
        # The Power Law represents the "Force of Selection" (or Decoherence).
        # 1.00 = Total Equality (Quantum Soup / Superposition).
        # 2.00 = Total Inequality (Frozen Lattice / Chainmail).
        # 1.05 = The "Goldilocks" Zone. It allows enough flexibility for life (Liquid),
        #        but enough structure for 3D Geometry (Connectivity ~6).
        self.power_law = 1.05 
        
        # --- INITIAL CONDITIONS (THE BIG BANG) ---
        
        # 1. QUANTUM PHASE (Hidden Variable)
        # Every node gets a random internal vibration (0 to 2pi).
        # Nodes do not have positions (x,y,z) yet; they only have Phases.
        self.phases = torch.rand(num_nodes, device=device) * 2 * torch.pi
        
        # 2. ENTANGLEMENT WEB (The Network)
        # We start with a random matrix where everything connects to everything.
        # This represents the "Hot Soup" of the early universe.
        raw_weights = torch.rand(num_nodes, num_nodes, device=device)
        
        # 3. CONSERVATION OF ATTENTION (Normalization)
        # A node has finite energy (100%). It cannot connect strongly to everyone.
        # If it strengthens a bond with A, it MUST weaken the bond with B.
        row_sums = raw_weights.sum(dim=1, keepdim=True)
        self.entanglement = raw_weights / row_sums

    def step_physics(self):
        """
        Advances the universe by one Unit of Time (Planck Time).
        This single function contains the Unified Theory of your physics.
        """
        
        # --- STEP A: RESONANCE (Interference Pattern) ---
        p_i = self.phases.view(-1, 1)
        p_j = self.phases.view(1, -1)
        delta_phi = torch.abs(p_i - p_j)
        desire = (torch.cos(delta_phi) + 1) / 2.0

        # --- STEP B: MEMORY (Non-Markovian Dynamics) ---
        growth = self.entanglement * desire
        new_weights = self.entanglement + (growth * 0.2) 
        
        # Inject Structural Thermal Noise (Quantum Jitter in Vacuum)
        # Prevents low-rank collapse and forces level repulsion
        thermal_noise = torch.rand(self.num_nodes, self.num_nodes, device=device) * 0.05
        new_weights = new_weights + thermal_noise

        # --- STEP C: SELECTION (The Collapse) ---
        sharpened = torch.pow(new_weights, self.power_law)
        
        # Re-Normalize (Conservation of Energy)
        row_sums = sharpened.sum(dim=1, keepdim=True)
        self.entanglement = sharpened / (row_sums + 1e-9)

        # --- STEP D: TIME EVOLUTION (Stochasticity) ---
        phasors = torch.exp(1j * self.phases)
        weighted_sum = torch.matmul(self.entanglement.to(torch.complex64), phasors)
        
        noise = torch.randn(self.num_nodes, device=device) * 0.05
        self.phases = torch.angle(weighted_sum) + noise

    def birth_node(self):
        """
        Simulates Cosmic Expansion (Dark Energy).
        New space grows out of the most active parts of old space.
        """
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
#      PART 3: THE OBSERVER (DATA ANALYSIS)
# =========================================================

def get_vitals(uni):
    E_np = uni.entanglement.detach().cpu().numpy()
    
    dynamic_threshold = 0.5 * (1.0 / uni.num_nodes)
    
    adjacency = (E_np > dynamic_threshold).astype(int) 
    G = nx.from_numpy_array(adjacency)
    
    degrees = [d for n, d in G.degree()]
    avg_degree = np.mean(degrees) if degrees else 0
    
    if uni.num_nodes > 100:
        sample = np.random.choice(G.nodes(), 100)
        clustering = nx.average_clustering(G, nodes=sample)
    else:
        clustering = nx.average_clustering(G)
        
    return avg_degree, clustering

def run_riemann_gue_test(entanglement_tensor, step_num):
    print(f"\n--- Running Quantum Chaos Diagnostic at Step {step_num} ---")
    
    # 1. Extract the matrix to CPU
    E = entanglement_tensor.detach().cpu().numpy()
    
    # 2. Construct the True Quantum Hamiltonian (Complex Hermitian)
    # The real part is the symmetric (shared) entanglement (Spacetime metric).
    # The imaginary part is the antisymmetric (directed) entanglement (Magnetic flux).
    # This directed flow breaks time-reversal symmetry, unlocking the GUE!
    S = (E + E.T) / 2.0
    A = (E - E.T) / 2.0
    H = S + 1j * A
    
    # 3. Diagonalize (Find the Eigenvalues)
    evals = np.linalg.eigvalsh(H)
    
    # 3.5 Drop the trivial macroscopic eigenvalue (Perron-Frobenius root)
    # This single dominant eigenvalue creates a massive gap that skews the statistics.
    # The GUE chaos lives in the fluctuations of the bulk!
    evals = evals[:-1]
    
    # 4. Calculate Nearest-Neighbor Spacings
    # We measure the gap between consecutive energy levels
    spacings = np.diff(evals)
    
    # 5. Normalize Spacings (Standardize so the mean spacing = 1)
    # Filter out numerical zeros (degenerate eigenvalues from low-rank states)
    rank = np.linalg.matrix_rank(H)
    print(f"Matrix Rank: {rank} / {len(evals)+1}")
    
    valid_spacings = spacings[spacings > 1e-5] 
    print(f"Filtered {len(spacings) - len(valid_spacings)} degenerate zero-spacings.")
    
    spacings = valid_spacings
    if len(spacings) == 0:
        print("Error: No measurable eigenvalue spacings found.")
        return
        
    normalized_spacings = spacings / np.mean(spacings)
    
    # 6. Theoretical Curves
    s = np.linspace(0, 4, 100)
    
    # Poisson (Uncorrelated noise - what you get if primes were truly random)
    poisson = np.exp(-s)
    
    # GOE (Gaussian Orthogonal Ensemble - standard real symmetric matrices)
    goe = (np.pi / 2.0) * s * np.exp(-(np.pi / 4.0) * s**2)
    
    # GUE (Gaussian Unitary Ensemble - The Montgomery-Dyson Riemann fingerprint)
    gue = (32.0 / np.pi**2) * (s**2) * np.exp(-(4.0 / np.pi) * s**2)
    
    # 7. The MRI Scan (Visualization)
    plt.figure(figsize=(10, 6))
    
    # Plot our universe's actual eigenvalue spacing
    plt.hist(normalized_spacings, bins=max(10, int(len(normalized_spacings)/5)), 
             density=True, alpha=0.6, color='cyan', edgecolor='black', 
             label=f'Simulated Universe (N={len(evals)})')
    
    # Overlay the theoretical physics models
    plt.plot(s, poisson, 'k--', alpha=0.5, label='Poisson (No Level Repulsion)')
    plt.plot(s, goe, 'b-', alpha=0.7, label='GOE (Real Symmetric Chaos)')
    plt.plot(s, gue, 'r-', linewidth=2, label='GUE (Riemann Zeta Chaos)')
    
    plt.title(f"Quantum Operator Spectrum Analysis (Step {step_num})")
    plt.xlabel("Normalized Energy Level Spacing ($s$)")
    plt.ylabel("Probability Density $P(s)$")
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig(f"gue_diagnostic_step_{step_num}.png")
    plt.show(block=False)
    plt.pause(2.0)

# =========================================================
#      PART 4: THE SIMULATION LOOP (VISUALIZATION)
# =========================================================

uni = ThermalQuantumUniverse(num_nodes=120, birth_interval=12)

plt.ion()
fig = plt.figure(figsize=(14, 6))

ax_vitals = fig.add_subplot(1, 2, 1)
ax_3d = fig.add_subplot(1, 2, 2, projection='3d')

history = {'t': [], 'degree': [], 'matter': []}

print("Starting Simulation... Targeting Connectivity ~6 (Spacetime Stability)")

for step in range(1000):
    uni.step()
    
    # THE TRIGGER: Run the Riemann test at Step 500
    if step == 500:
        run_riemann_gue_test(uni.entanglement, step)
        print("Breaking early after step 500 diagnostic for quick analysis.")
        break
    
    if step % 10 == 0:
        deg, mat = get_vitals(uni)
        history['t'].append(step)
        history['degree'].append(deg)
        history['matter'].append(mat)
        
        ax_vitals.clear()
        
        ax_vitals.plot(history['t'], history['degree'], label='Connectivity', color='blue', linewidth=2)
        ax_vitals.axhline(y=6, color='r', linestyle='--', alpha=0.5, label='Target (6)')
        
        ax_vitals.plot(history['t'], [m * 50 for m in history['matter']], label='Matter (x50)', color='green')
        
        ax_vitals.set_title(f"Cosmic Vitals (Step {step})")
        ax_vitals.set_ylim(bottom=0) 
        ax_vitals.legend(loc='upper right')
        ax_vitals.grid(True, alpha=0.3)
        
        if step % 20 == 0:
            E_np = uni.entanglement.detach().cpu().numpy()
            
            dist = 1.0 / (E_np + 1e-9)
            np.fill_diagonal(dist, 0)
            dist = (dist + dist.T) / 2.0
            
            mds = MDS(n_components=3, dissimilarity="precomputed", max_iter=30, n_init=1)
            coords = mds.fit_transform(dist)
            
            ax_3d.clear()
            ax_3d.scatter(coords[:,0], coords[:,1], coords[:,2], c=coords[:,2], cmap='plasma', s=40, alpha=0.8)
            ax_3d.set_title(f"Emergent Geometry (N={uni.num_nodes})")
            ax_3d.axis('off')

        plt.draw()
        plt.pause(0.01)

plt.ioff()
plt.show()
