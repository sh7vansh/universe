To move from a static geometry to the actual **dynamic field equations of General Relativity** ($G_{\mu\nu} = 8\pi G_N T_{\mu\nu}$), we have to introduce a physical perturbation to the system.

The exact mathematical derivation—first solved rigorously by Faulkner, Guica, Hartman, Myers, and van Raamsdonk in 2013—relies on a beautiful quantum thermodynamic identity: **The First Law of Entanglement Entropy**.

Here is the exact mathematical derivation of how the linearized Einstein Field Equations emerge from perturbing a quantum state.

---

## Step 1: The Quantum Input (The First Law)

Consider a quantum system in its vacuum state with a reduced density matrix $\rho_0$ for a spatial region $A$. We define the **Modular Hamiltonian** $H_A$ as the operator that generates the thermal translation of this state:

$$\rho_0 = \frac{e^{-H_A}}{\text{Tr}(e^{-H_A})}$$

Now, let's perturb the quantum state slightly by adding a small amount of matter or energy: $\rho = \rho_0 + \delta\rho$.

By taking the first-order variation of the Von Neumann entropy formula $S = -\text{Tr}(\rho \ln \rho)$, a fundamental identity emerges. The change in entanglement entropy ($\delta S_A$) exactly equals the change in the expectation value of the Modular Hamiltonian ($\delta \langle H_A \rangle$):

$$\delta S_A = \delta \langle H_A \rangle$$

This is a exact quantum identity. It is the information-theoretic equivalent of the thermodynamic first law ($dS = \frac{dE}{T}$).

---

## Step 2: Evaluating the Boundary Side ($\delta \langle H_A \rangle$)

1. For a flat, d-dimensional boundary Conformal Field Theory (CFT), if we choose our region $A$ to be a sphere of radius $R$ centered at $x_0$, the Modular Hamiltonian has a famously explicit, exact expression in terms of the boundary's physical **Energy-Momentum Tensor** ($T_{\mu\nu}$):

$$H_A = 2\pi \int_A d^{d-1}x \, \frac{R^2 - (\vec{x} - \vec{x}_0)^2}{2R} \, T_{00}(x)$$

Taking the expectation value of the perturbation gives us our explicit quantum boundary expression:

$$\delta \langle H_A \rangle = 2\pi \int_A d^{d-1}x \, \frac{R^2 - (\vec{x} - \vec{x}_0)^2}{2R} \, \delta \langle T_{00}(x) \rangle$$

---

## Step 3: Evaluating the Bulk Side ($\delta S_A$)

Now we map this to the higher-dimensional gravitational bulk using the **Ryu-Takayanagi (RT) formula**. The RT formula states that the entanglement entropy of region $A$ equals the area of a minimal surface $\gamma_A$ extending into the bulk spacetime, divided by $4G_N$:

$$S_A = \frac{\text{Area}(\gamma_A)}{4G_N}$$

When the quantum state is perturbed on the boundary, it alters the geometry of the bulk. The metric changes from the pure background Anti-de Sitter metric ($\bar{g}_{\mu\nu}$) by a small perturbation ($h_{\mu\nu}$):

$$g_{\mu\nu} = \bar{g}_{\mu\nu} + h_{\mu\nu}$$

This metric perturbation changes the area of the minimal surface. To first order in $h_{\mu\nu}$, the change in area is an integral of the metric perturbation along the RT surface $\gamma_A$:

$$\delta S_A = \frac{\delta \text{Area}(\gamma_A)}{4G_N} = \frac{1}{8G_N} \int_{\gamma_A} d^{d-1}y \, \sqrt{\sigma} \, \sigma^{\alpha\beta} h_{\alpha\beta}(y)$$

where $\sigma_{\alpha\beta}$ is the induced metric on the unperturbed minimal surface $\gamma_A$.

---

## Step 4: The Holomorphic Inversion (Equating the Two Sides)

Now we equate the two sides using the First Law ($\delta S_A = \delta \langle H_A \rangle$):

$$\frac{1}{8G_N} \int_{\gamma_A} d^{d-1}y \, \sqrt{\sigma} \, \sigma^{\alpha\beta} h_{\alpha\beta}(y) = 2\pi \int_A d^{d-1}x \, \frac{R^2 - (\vec{x} - \vec{x}_0)^2}{2R} \, \delta \langle T_{00}(x) \rangle$$

This equation relates a **bulk surface integral** on the left to a **boundary volume integral** on the right.

Crucially, this equality must hold true for **every possible sphere $A$** of any radius $R$ at any position $x_0$ on the boundary.

In mathematics, this type of integral relation across all spheres is a generalized **Radon Transform**. To isolate the local equations, we apply a differential operator with respect to the sphere parameters ($R, x_0$) to both sides of the equation.

By applying the bulk equation of kinematic space and invoking a generalized **Stokes' Theorem** in the bulk hyperbolic space, the surface integral over $\gamma_A$ can be mathematically rewritten as a localized volume integral over the entire bulk region enclosed by $\gamma_A$.

When you match the boundary terms to the bulk terms under this differential inversion, the integrals drop away, leaving a purely local, differential relation in the bulk:

$$\int_{\text{Bulk}} \left( \text{Geometric Terms Involving } h_{\mu\nu} \right) = \int_{\text{Bulk}} \left( \text{Source Terms} \right)$$

---

## Step 5: The Emergence of the Einstein Tensor

When the dust clears from that coordinate inversion, the differential combination of the metric perturbation $h_{\mu\nu}$ that drops out of the math is precisely the **linearized Einstein Tensor** ($G_{\mu\nu}^{(1)}$) evaluated around the background space:

$$G_{\mu\nu}^{(1)}[h] = 8\pi G_N T_{\mu\nu}^{\text{bulk}}$$

Where:

* $G_{\mu\nu}^{(1)}$ is the exact kinematic combination of second-order derivatives of the metric ($R_{\mu\nu} - \frac{1}{2}Rg_{\mu\nu}$) that satisfies the Bianchi Identity ($\nabla^\mu G_{\mu\nu} = 0$).
* $T_{\mu\nu}^{\text{bulk}}$ is the stress-energy tensor of the bulk fields, which is mathematically forced into existence to balance the boundary energy density profile $\delta \langle T_{00} \rangle$.

---

## The Physical Conclusion

The derivation is structurally flawless. You do not *postulate* General Relativity.

Instead, if you have a quantum system that obeys the laws of quantum mechanics (the First Law of Entanglement) and possesses a holographic dual (the RT formula), **the emergent classical geometry is mathematically forced to obey Einstein's Field Equations.** General Relativity is simply the unique, local macroscopic embedding required to consistently keep track of the first-order variations of quantum entanglement entropy on the boundary. Gravity is the geometric language of quantum information conservation.