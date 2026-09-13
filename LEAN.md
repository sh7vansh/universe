# Lean 4 Formalization: Basis Discovery and Decoupling Algorithms

This directory contains the machine-checked proofs for the mathematical frameworks specified in `ontologicalmachine.md`, `categoricalmachine.md`, and `friction.md`. The code is located in `math_project/MathProject/` and verified with Lean 4 and Mathlib.

Every theorem in the repository compiles with zero `sorry` placeholders and depends solely on the standard Lean 4 core axioms: `propext`, `Classical.choice`, and `Quot.sound`.

---

## 1. Purpose

The formalization verifies the mechanics, optimality conditions, and friction limits of two greedy extraction algorithms:

1. **Basis Discovery Algorithm (Discrete Track)**: Evaluates greedy generator extraction on closure spaces $(U, \mathrm{cl})$. It proves exact optimality in matroidal spaces, quantifies worst-case degradation in adversarial spaces, and proves the logarithmic approximation bound under submodular rank functions.
2. **Decoupling Algorithm (Categorical Track)**: Evaluates transfinite cellular filtrations of objects $U_0$ in abelian categories $\mathcal{A}$. It proves that successive pullbacks of simple socle subobjects strictly expand subobjects, that the resulting Loewy chain stabilizes at an ordinal Loewy length without custom axioms, and that the residual colimit vanishes upon convergence.

---

## 2. Architecture and Module Map

The formalization is organized into 9 modules under `math_project/MathProject/`:

```
math_project/
├── lakefile.toml
├── lean-toolchain
├── MathProject.lean
├── CheckAll.lean
└── MathProject/
    ├── Basic.lean
    ├── OntologicalMachine.lean
    ├── OntologicalFriction.lean
    ├── AdversarialTrap.lean
    ├── MatroidFriction.lean
    ├── SubmodularFriction.lean
    ├── CategoricalMachine.lean
    ├── CategoricalColimits.lean
    ├── LoewyLength.lean
    ├── CheckAxioms.lean
    └── CheckAll.lean
```

### Module Descriptions

| Module | Purpose | Key Definitions and Theorems |
| :--- | :--- | :--- |
| `Basic.lean` | General utility infrastructure. | Foundational helpers and order lemmas. |
| `OntologicalMachine.lean` | Discrete sieve mechanics and operators. | `ClosureSystem`, `DiscoveryOperator`, `fixedPriorityPhi`, `adaptiveGreedyPhi`, `B_seq`, `sieve_output`. |
| `OntologicalFriction.lean` | Friction metrics for discrete discovery. | `IsGeneratingSet`, `IsOptimalGenerator`, `cardinalityBloat`, `searchWork`, `searchWork_perfect_alignment`, `searchWork_limit`. |
| `AdversarialTrap.lean` | Worst-case non-matroidal construction. | `advCl`, `optimal_e_star`, `searchWork_adv_trap_limit`. |
| `MatroidFriction.lean` | Optimality under Steinitz exchange. | `MacLaneSteinitz`, `UnivMatroid`, `matroid_maclane`, `matroid_optimality_bound`. |
| `SubmodularFriction.lean` | Submodular greedy bounds and finite bridge. | `B_nat`, `terminationIndex`, `submodular_opt_step_le`, `greedy_submodular_bound`, `advCl_greedy_size_worst_case`, `fixed_priority_violates_submodular_bound`, `randomized_expected_bound`. |
| `CategoricalMachine.lean` | Ambient object and cellular step definitions. | `IsSimple`, `residual`, `IsSemiArtinian`, `cellularStep`, `cellularSubobject`. |
| `CategoricalColimits.lean` | Colimit convergence and length friction. | `transfiniteRecursionStep`, `loewyObj`, `loewyFunctor_map_mono`, `residual_colimit_vanishes`, `categorical_friction_bound`. |
| `LoewyLength.lean` | Cardinal bound and stabilization proof. | `nextLoewy`, `lt_cellular`, `loewySequence_strict_mono`, `loewy_length_exists`. |

---

## 3. Discrete Track Mechanics

The discrete formalization centers on a ground set $U$ equipped with a closure operator $\mathrm{cl} : \mathcal{P}(U) \to \mathcal{P}(U)$ satisfying extensivity, monotonicity, and idempotence (`ClosureSystem`).

### Transfinite Sieve and the Finite Bridge
The sieve builds a set sequence $B_\alpha$ by applying a discovery operator $\Phi$:
- At successor steps, $B_{\alpha+1} = B_\alpha \cup \{\Phi(\mathrm{cl}(B_\alpha))\}$.
- At limit steps, $B_\lambda = \bigcup_{\beta < \lambda} B_\beta$.

In finite universes (`[Fintype U]`), `SubmodularFriction.lean` proves that $B_\alpha$ strictly increases until closure coverage. By pigeonhole on cardinality, the sequence stabilizes at index `terminationIndex cl phi <= Fintype.card U`. The theorem `sieve_output_eq_B_nat_termination` collapses the transfinite union directly to this finite stage.

### The Three Friction Regimes
1. **Matroid Regime (`MatroidFriction.lean`)**:
   If $\mathrm{cl}$ satisfies the Mac Lane-Steinitz exchange property, the closure system is a matroid (`matroid_maclane`). Every greedy independent sieve output is a matroid base. Since all bases share the same cardinality, the cardinality bloat ratio $|B_{\text{greedy}}| / |B_{\text{opt}}|$ is exactly 1 (`matroid_optimality_bound`).
2. **Adversarial Regime (`AdversarialTrap.lean` and `SubmodularFriction.lean`)**:
   For the adversarial closure $\mathrm{advCl}(S) = U \text{ if } e^* \in S \text{ else } S$, the optimal generator is $\{e^*\}$, having size 1. A fixed priority order that evaluates $e^*$ last forces the sieve to select all $|U|$ elements (`advCl_greedy_size_worst_case`). This yields cardinality bloat of $|U|$ and drives the discard rate $W$ to 1 (`searchWork_adv_trap_limit`), violating logarithmic bounds (`fixed_priority_violates_submodular_bound`).
3. **Submodular Regime (`SubmodularFriction.lean`)**:
   When the rank function $f(S) = |\mathrm{cl}(S)|$ is submodular (`IsSubmodularClosure`), the adaptive greedy operator chooses the element maximizing marginal rank gain. The formalization establishes:
   - Deficit monotonicity (`greedyDeficit_mono`) and positivity (`greedyDeficit_pos`).
   - The submodular step bound (`greedyDeficit_step_le`), proving each greedy step captures at least a $1/|B_{\text{opt}}|$ fraction of the remaining rank gap.
   - Telescoping log sum bounding, yielding the verified approximation bound:
     $$|B_{\text{greedy}}| \le (\ln \Delta + 1) |B_{\text{opt}}|$$
     where $\Delta = \max_{x} |\mathrm{cl}(\{x\})|$ is the maximum single-element marginal gain (`greedy_submodular_bound`).

---

## 4. Categorical Track Mechanics

The categorical formalization translates the extraction process to an ambient object $U_0$ in an abelian category $\mathcal{A}$.

### Residuals and Socle Pullbacks
For any subobject $C \hookrightarrow U_0$, the residual is defined as the cokernel of the monic inclusion arrow:
$$\mathrm{residual}(C) = \mathrm{coker}(C \hookrightarrow U_0)$$

Under the semi-Artinian property (`IsSemiArtinian`), every non-zero residual contains a simple subobject $a \hookrightarrow \mathrm{residual}(C)$. The cellular step pulls back $a$ along the projection $\pi : U_0 \twoheadrightarrow \mathrm{residual}(C)$.

The lemma `lt_cellular` in `LoewyLength.lean` proves that this pullback produces a strictly larger subobject:
$$C < \mathrm{cellularSubobject}(C, a, i)$$

### Stabilization and Colimit Reconstruction
By tracking cardinal bounds on the well-powered lattice $\mathrm{Subobject}(U_0)$, `loewy_length_exists` proves that the strictly increasing sequence cannot grow indefinitely. It must stabilize at an ordinal $\Omega$.

At index $\Omega$:
1. The step cannot strictly increase, forcing $\mathrm{residual}(C_\Omega) \cong 0$.
2. Because the cokernel vanishes, the inclusion is an isomorphism, meaning $C_\Omega = \top \cong U_0$.
3. The directed colimit of the residual diagram vanishes completely (`residual_colimit_vanishes`), reconstructing the ambient object.

---

## 5. Building and Verifying

To compile and verify the proofs locally:

```bash
# Navigate to the project directory
cd math_project

# Build the complete Lean 4 library
lake build

# Run the core theorem axiom audit
lake env lean MathProject/CheckAxioms.lean

# Run the comprehensive 64-theorem axiom audit
lake env lean MathProject/CheckAll.lean
```

Both audit scripts output dependencies only on foundational Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).
