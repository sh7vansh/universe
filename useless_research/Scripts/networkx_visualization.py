import networkx as nx
import matplotlib.pyplot as plt
import numpy as np
from sklearn.manifold import MDS

# --- STEP 1: REBUILD THE UNIVERSE (The Physics) ---
print("Re-simulating to get fresh data...")

num_nodes = 300
phases = np.random.uniform(0, 2*np.pi, num_nodes)

# Initialize with 'Legal' Monogamy rules (Conservation of Info)
raw_weights = np.random.rand(num_nodes, num_nodes)
row_sums = raw_weights.sum(axis=1, keepdims=True)
entanglement = raw_weights / row_sums 

# Fast evolution (30 steps is enough to see the structure form)
for t in range(30):
    # Calculate Phase Resonance
    p_i = phases[:, np.newaxis]
    p_j = phases[np.newaxis, :]
    delta_phi = np.abs(p_i - p_j)
    desire = (np.cos(delta_phi) + 1) / 2.0
    
    # Hebbian Growth + Normalization (Monogamy)
    growth = entanglement * desire
    new_weights = entanglement + (growth * 0.2)
    sharpened = np.power(new_weights, 2) 
    row_sums = sharpened.sum(axis=1, keepdims=True)
    entanglement = sharpened / (row_sums + 1e-9)
    
    # Phase Update
    phasors = np.exp(1j * phases)
    weighted_sum = np.dot(entanglement, phasors)
    phases = np.angle(weighted_sum) + np.random.normal(0, 0.05, num_nodes)

# --- STEP 2: OBSERVATION (The Geometry) ---
print("Collapsing wavefunction to 3D...")
dist_matrix = 1.0 / (entanglement + 1e-9)
np.fill_diagonal(dist_matrix, 0)
dist_matrix = (dist_matrix + dist_matrix.T) / 2.0

mds = MDS(n_components=3, dissimilarity="precomputed", random_state=42, max_iter=100)
coords = mds.fit_transform(dist_matrix)

# --- STEP 3: THE MRI SLICE (The Proof) ---
print("performing MRI Scan...")

# We take a slice of the universe at Z=0 (+/- a small margin)
z_margin = (np.max(coords[:, 2]) - np.min(coords[:, 2])) * 0.1 # 10% slice
mask = np.abs(coords[:, 2]) < z_margin
slice_points = coords[mask]

# --- VISUALIZATION ---
plt.figure(figsize=(10, 5))

# Plot 1: The Full 3D View (Projection)
ax1 = plt.subplot(1, 2, 1, projection='3d')
ax1.scatter(coords[:,0], coords[:,1], coords[:,2], c='purple', alpha=0.3, s=20)
ax1.set_title("Full Universe (3D View)")
ax1.set_xticks([])
ax1.set_yticks([])
ax1.set_zticks([])

# Plot 2: The MRI Slice (2D Cross-section)
ax2 = plt.subplot(1, 2, 2)
ax2.scatter(slice_points[:, 0], slice_points[:, 1], c='cyan', edgecolors='black', s=60)
ax2.set_title(f"MRI Slice (Z=0)\n(If ring-like -> Closed Manifold)")
ax2.grid(True, alpha=0.3)
ax2.axis('equal')

plt.tight_layout()
plt.show()
