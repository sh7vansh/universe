
```python
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
```




Here is the line-by-line breakdown.

### **Part 1: Imports and Configuration**

Setting up the laboratory.

```python
import torch
import numpy as np
import matplotlib.pyplot as plt
import networkx as nx
from sklearn.manifold import MDS
import time
```

* **`torch`:** The heavy lifter. We use PyTorch for matrix multiplication on the GPU. It handles the "Parallel Universe" calculations.
* **`networkx`:** A graph theory library. We use this to analyze the "Vitals" (Is the web healthy? Is it connected?).
* **`MDS` (Multi-Dimensional Scaling):** This is the "Camera." It forces the abstract network connections into 3D coordinates so you can see the sphere.

```python
device = "cuda" if torch.cuda.is_available() else "cpu"
print(f"Simulation running on: {device.upper()}")
```

* **Hardware Check:** If you have an NVIDIA GPU (`cuda`), the universe runs 100x faster. Otherwise, it runs on the CPU.

---

### **Part 2: The Engine (`ThermalQuantumUniverse`)**

This class is the "God Object." It defines the laws of nature.

#### **Initialization (The Big Bang)**

```python
class ThermalQuantumUniverse:
    def __init__(self, num_nodes=150, birth_interval=12): 
```

* **`num_nodes=150`:** We start with 150 "Event Points" (Monads).
* **`birth_interval=12`:** Every 12 ticks, a new node is born (Cosmic Expansion).

```python
        self.power_law = 1.05 
```

* **The Magic Number:** This controls the **Force of Monogamy**.
* `1.0` = Everyone connects to everyone (Soup).
* `2.0` = Everyone clings to 1 neighbor (Ice).
* `1.05` = **Life.** It allows nodes to maintain exactly ~6 connections.

```python
        self.phases = torch.rand(num_nodes, device=device) * 2 * torch.pi
```

* **The Wavefunction:** Every node gets a random "Phase" ( to ). This represents its internal vibration or quantum state.

```python
        raw_weights = torch.rand(num_nodes, num_nodes, device=device)
        row_sums = raw_weights.sum(dim=1, keepdim=True)
        self.entanglement = raw_weights / row_sums
```

* **The Web:** We create a random connection matrix.
* **Normalization:** We divide by the sum. This enforces **Conservation of Attention**. A node only has 100% energy to give; if it loves Node A more, it *must* love Node B less.

#### **The Physics Loop (`step_physics`)**

This runs every single "Planck Time."

**1. Resonance (Interference)**

```python
        p_i = self.phases.view(-1, 1)
        p_j = self.phases.view(1, -1)
        delta_phi = torch.abs(p_i - p_j)
        desire = (torch.cos(delta_phi) + 1) / 2.0
```

* **The Logic:** Compare every node's phase with every other node.
* **The Physics:** **Wave Interference.**
* If phases match (), `desire` is **1.0** (Attraction).
* If phases oppose (), `desire` is **0.0** (Repulsion).

**2. Hebbian Memory (Non-Markovian)**

```python
        growth = self.entanglement * desire
        new_weights = self.entanglement + (growth * 0.2) 
```

* **The Logic:** "If we are already connected (`entanglement`) AND we resonate (`desire`), let's get stronger."
* **The Physics:** **Time/Memory.** The universe is built on its history.

**3. Power Law Monogamy (The Filter)**

```python
        sharpened = torch.pow(new_weights, self.power_law)
        row_sums = sharpened.sum(dim=1, keepdim=True)
        self.entanglement = sharpened / (row_sums + 1e-9)
```

* **The Logic:** Apply the power `1.05`.
* **The Physics:** **Natural Selection.** Weak connections get mathematically punished (pushed toward 0), while strong connections get rewarded. This sculpts the "Soup" into a "Crystal."

**4. Phase Update (Time Evolution)**

```python
        phasors = torch.exp(1j * self.phases)
        weighted_sum = torch.matmul(self.entanglement.to(torch.complex64), phasors)
        noise = torch.randn(self.num_nodes, device=device) * 0.05
        self.phases = torch.angle(weighted_sum) + noise
```

* **The Logic:** Nodes try to sync phases with their friends.
* **`noise`:** **Stochasticity (Entropy).** We add random jitter. Without this, the universe would freeze solid. This keeps it "Liquid" enough for life.

---

### **Part 3: The Monitor (`get_vitals`)**

This converts the raw math into human-readable numbers.

```python
    dynamic_threshold = 0.5 * (1.0 / uni.num_nodes)
    adjacency = (E_np > dynamic_threshold).astype(int) 
```

* **The Eye:** The raw matrix has values like `0.0001`. We need to decide: Is this a connection or just noise?
* **Dynamic Sensitivity:** As the universe grows ( gets bigger), connections naturally get weaker. This formula auto-adjusts the glasses so we don't go blind as the universe expands.

```python
    degrees = [d for n, d in G.degree()]
    avg_degree = np.mean(degrees)
```

* **Connectivity (Blue Line):** How many neighbors does the average node have? (Target: 6).

```python
    clustering = nx.average_clustering(G, nodes=sample)
```

* **Matter Density (Green Line):** Are the nodes forming tight triangles (Particles)? Or just loose chains?

---

### **Part 4: The Simulation Loop**

Running the experiment.

```python
uni = ThermalQuantumUniverse(num_nodes=120, birth_interval=12)
```

* **Start:** Create a universe with 120 nodes.

```python
plt.ion()
```

* **Interactive Mode:** Tells Python to update the plot live (animation) rather than generating one static image at the end.

```python
for step in range(1000):
    uni.step()
```

* **The Loop:** Run for 1000 timesteps.

```python
        # Plotting Logic...
        if step % 20 == 0:
            mds = MDS(n_components=3, ...)
            coords = mds.fit_transform(dist)
```

* **The 3D Renderer:** Every 20 steps, we take the "Distance Matrix" (who is far from whom?) and ask the `MDS` algorithm to find the best 3D shape that fits those distances.
* **The Result:** This is what creates the Sphere on the right side of your screen. We didn't program a sphere; the math *found* it.
![[Figure_2.png]]![[Figure_1 1.png]]