# Measurement hypothesis: primary references and interpretation limits

This note supports an algebraic comparison on a K₃ × K₄ product facet inside K₆. It does not treat a numerical toy-model test as empirical evidence about the universe. A lower-dimensional face, a product of polytopes, and a quantum subsystem are different mathematical objects.

## Born rule and projective update

Nilanjana Datta's Cambridge notes give spectral projectors, the outcome probability `〈ψ|P_n|ψ〉`, the normalized post-measurement state, and immediate repeatability in equations (1)–(2): [Quantum Information and Computation, QM4](https://www.qi.damtp.cam.ac.uk/files/QIC-3.pdf).

For density matrices the corresponding Lüders instrument is

```text
p(a) = tr(P_a ρ)
ρ conditioned on a = P_a ρ P_a / p(a)
ρ after ignoring outcome = Σ_a P_a ρ P_a.
```

John Preskill's Caltech notes develop measurement operators, projective measurements, generalized measurements, and physical realization through a larger system: [Foundations II: Measurement and Evolution](https://www.preskill.caltech.edu/ph219/chap3_15.pdf), §§3.1–3.2.

These formulas require a complex Hilbert space, a density matrix, projectors, and the probability/update postulates. Face inclusion does not establish them. The ten vertices of the product facet permit choosing `ℂ¹⁰≅ℂ²⊗ℂ⁵` after selecting a basis, but the combinatorial product does not force quantum amplitudes or Born probabilities. The same ten labels also support an ordinary classical probability distribution.

## Measurement through entanglement and restricted access

A standard premeasurement model has a unitary coupling

```text
|0〉|ready〉 → |0〉|pointer_0〉
|1〉|ready〉 → |1〉|pointer_1〉.
```

For input `α|0〉+β|1〉`, the joint state is `α|0〉|pointer_0〉+β|1〉|pointer_1〉`. Orthogonal pointer records make the reduced system state diagonal after tracing out the pointer. Preskill explains partial traces and composite states in [Foundations I: States and Ensembles](https://www.preskill.caltech.edu/ph219/chap2_15.pdf), §2.4. Wojciech Zurek explains environmental monitoring, loss of interference, and stable pointer states in [Decoherence, einselection, and the quantum origins of the classical](https://arxiv.org/pdf/quant-ph/0105127).

Tracing out the pointer does not select one actual outcome in the global state. It describes restricted access to an entangled system. Restricted access likewise yields classical marginalization in a classical joint distribution; neither restricted access nor subsystem nesting alone singles out quantum mechanics.

## CHSH: an actual separation under stated assumptions

The original CHSH paper derives experimentally relevant restrictions on local hidden-variable models: [Clauser, Horne, Shimony, Holt, Proposed Experiment to Test Local Hidden-Variable Theories (1969)](https://doi.org/10.1103/PhysRevLett.23.880). Preskill gives the inequality and maximal quantum violation in [Quantum Entanglement](https://www.preskill.caltech.edu/ph229/notes/chap4_01.pdf), §§4.3.1–4.3.2.

For local binary responses with a common hidden-variable distribution independent of measurement settings,

```text
S = E(A₀B₀)+E(A₀B₁)+E(A₁B₀)−E(A₁B₁)
|S| ≤ 2.
```

Quantum mechanics permits `|S|=2√2`, for instance on `(|00〉+|11〉)/√2` with `A₀=Z`, `A₁=X`, `B₀=(Z+X)/√2`, and `B₁=(Z−X)/√2`. These definitions can be embedded in a two-state subspace of a five-state pointer. Obtaining this result after choosing these Hilbert states and observables verifies quantum matrix algebra; it does not derive that algebra from K₆ or establish physically separated measurement stations.

## Order effects alone do not distinguish quantum from classical disturbance

Noncommuting Lüders updates can produce order-dependent outcomes, but classical invasive operations can also fail to commute. An elementary classical counterexample is a bit with two measurement-plus-reset channels: `T₀` reads it and resets it to 0; `T₁` reads it and resets it to 1. Applying `T₀` then `T₁` leaves 1; the reverse order leaves 0. This is a direct algebraic construction, without quantum amplitudes.

Therefore a fair comparison should distinguish passive classical conditioning from invasive classical measurement. A CHSH violation excludes the specified local, setting-independent classical family; it does not exclude unrestricted disturbance, communication, or setting-dependent hidden-variable models merely by being greater than 2.
