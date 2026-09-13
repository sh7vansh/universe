# Lean 4 formalization of basis discovery and decoupling algorithms

This repository formalizes the algorithms and bounds from `ontologicalmachine.md`, `categoricalmachine.md`, and `friction.md`. Lean 4 and Mathlib check every proof in `math_project/MathProject/`.

Every theorem compiles with zero `sorry` placeholders. Proofs depend only on standard Lean 4 core axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## 1. Purpose

The project formalizes two greedy extraction algorithms across discrete and categorical settings.

**Discrete basis discovery.** Runs greedy generator extraction on closure spaces $(U, \mathrm{cl})$. The proofs verify exact optimality in matroid spaces, calculate worst-case loss in adversarial spaces, and prove a logarithmic approximation ratio for submodular rank functions.

**Categorical decoupling.** Builds transfinite cellular filtrations of an object $U_0$ in an abelian category $\mathcal{A}$. The proofs show that pulling back simple socle subobjects strictly grows each subobject, that the Loewy chain reaches stability at an ordinal length without extra axioms, and that the residual colimit vanishes at the terminal stage.

## 2. Architecture and module map

The formalization contains 9 modules in `math_project/MathProject/`:

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

### Module descriptions

| Module | Scope | Key declarations |
| :--- | :--- | :--- |
| `Basic.lean` | General utilities and order lemmas. | `Finset` helpers. |
| `OntologicalMachine.lean` | Discrete sieve mechanics and operators. | `ClosureSystem`, `DiscoveryOperator`, `fixedPriorityPhi`, `adaptiveGreedyPhi`, `B_seq`, `sieve_output`. |
| `OntologicalFriction.lean` | Friction metrics for discrete discovery. | `IsGeneratingSet`, `IsOptimalGenerator`, `cardinalityBloat`, `searchWork`, `searchWork_perfect_alignment`, `searchWork_limit`. |
| `AdversarialTrap.lean` | Worst-case non-matroid construction. | `advCl`, `optimal_e_star`, `searchWork_adv_trap_limit`. |
| `MatroidFriction.lean` | Optimality under Steinitz exchange. | `MacLaneSteinitz`, `UnivMatroid`, `matroid_maclane`, `matroid_optimality_bound`. |
| `SubmodularFriction.lean` | Submodular greedy bounds and finite bridge. | `B_nat`, `terminationIndex`, `submodular_opt_step_le`, `greedy_submodular_bound`, `advCl_greedy_size_worst_case`, `fixed_priority_violates_submodular_bound`, `randomized_expected_bound`. |
| `CategoricalMachine.lean` | Ambient object and cellular step definitions. | `IsSimple`, `residual`, `IsSemiArtinian`, `cellularStep`, `cellularSubobject`. |
| `CategoricalColimits.lean` | Colimit convergence and length friction. | `transfiniteRecursionStep`, `loewyObj`, `loewyFunctor_map_mono`, `residual_colimit_vanishes`, `categorical_friction_bound`. |
| `LoewyLength.lean` | Cardinal bound and stabilization proof. | `nextLoewy`, `lt_cellular`, `loewySequence_strict_mono`, `loewy_length_exists`. |

## 3. Discrete track mechanics

The discrete track starts with a ground set $U$ and a closure operator $\mathrm{cl} : \mathcal{P}(U) \to \mathcal{P}(U)$. The `ClosureSystem` class enforces extensivity, monotonicity, and idempotence.

### Transfinite sieve and finite bridge

The sieve builds a set sequence $B_\alpha$ by applying a discovery operator $\Phi$:
- At successor steps, $B_{\alpha+1} = B_\alpha \cup \{\Phi(\mathrm{cl}(B_\alpha))\}$.
- At limit steps, $B_\lambda = \bigcup_{\beta < \lambda} B_\beta$.

When $U$ is finite via `Fintype U`, `SubmodularFriction.lean` proves that $B_\alpha$ grows strictly until it reaches full closure. By the pigeonhole principle on set cardinality, the sequence stabilizes at index `terminationIndex cl phi <= Fintype.card U`. Theorem `sieve_output_eq_B_nat_termination` collapses the transfinite union directly down to this finite index.

### Three friction regimes

**Matroid regime in `MatroidFriction.lean`.** When $\mathrm{cl}$ satisfies Mac Lane-Steinitz exchange, the closure system forms a matroid via `matroid_maclane`. Every greedy independent sieve output is a matroid base. Because all bases share equal cardinality, the cardinality bloat ratio $|B_{\text{greedy}}| / |B_{\text{opt}}|$ equals 1 in `matroid_optimality_bound`.

**Adversarial regime in `AdversarialTrap.lean` and `SubmodularFriction.lean`.** Define the trap closure by $\mathrm{advCl}(S) = U$ if $e^* \in S$ and $\mathrm{advCl}(S) = S$ otherwise. The optimal generator $\{e^*\}$ has size 1. If a fixed priority order checks $e^*$ last, the sieve takes every element in $U$, proved in `advCl_greedy_size_worst_case`. Bloat expands to $|U|$, pushing the discard rate $W$ to 1 in `searchWork_adv_trap_limit` and breaking the submodular bound in `fixed_priority_violates_submodular_bound`.

**Submodular regime in `SubmodularFriction.lean`.** Assume the rank function $f(S) = |\mathrm{cl}(S)|$ satisfies `IsSubmodularClosure`. The adaptive greedy operator selects an element that maximizes marginal rank gain. The module proves three key properties:
- Deficit monotonicity in `greedyDeficit_mono` and positivity in `greedyDeficit_pos`.
- The per-step contractive bound in `greedyDeficit_step_le`, where each step removes at least a $1/|B_{\text{opt}}|$ fraction of the remaining rank deficit.
- The finite logarithmic approximation bound in `greedy_submodular_bound`:
  $$|B_{\text{greedy}}| \le (\ln \Delta + 1) |B_{\text{opt}}|$$
  Here $\Delta = \max_{x} |\mathrm{cl}(\{x\})|$ is the maximum single-element marginal gain.

## 4. Categorical track mechanics

The categorical formalization translates the extraction process to an ambient object $U_0$ in an abelian category $\mathcal{A}$.

### Residuals and socle pullbacks

For any subobject $C \hookrightarrow U_0$, the residual is the cokernel of the monic inclusion:
$$\mathrm{residual}(C) = \mathrm{coker}(C \hookrightarrow U_0)$$

Under `IsSemiArtinian`, every non-zero residual contains a simple subobject $a \hookrightarrow \mathrm{residual}(C)$. The cellular step pulls back $a$ along the projection $\pi : U_0 \twoheadrightarrow \mathrm{residual}(C)$.

Lemma `lt_cellular` in `LoewyLength.lean` proves this pullback strictly expands the subobject:
$$C < \mathrm{cellularSubobject}(C, a, i)$$

### Stabilization and colimit reconstruction

Because $\mathrm{Subobject}(U_0)$ is a small lattice, a strictly increasing chain cannot run past its cardinal bound. Theorem `loewy_length_exists` proves the sequence stabilizes at an ordinal index $\Omega$.

At index $\Omega$:
1. The cellular step halts strict expansion, so $\mathrm{residual}(C_\Omega) \cong 0$.
2. Vanishing cokernel makes the inclusion an isomorphism, so $C_\Omega = \top \cong U_0$.
3. The directed colimit of the residual diagram vanishes in `residual_colimit_vanishes`, which recovers the ambient object.

## 5. Build and verification

Run verification locally:

```bash
cd math_project

# Build the Lean 4 library
lake build

# Core theorem axiom audit
lake env lean MathProject/CheckAxioms.lean

# Full 64-theorem axiom audit
lake env lean MathProject/CheckAll.lean
```

Both audit scripts report dependencies only on the three standard Lean 4 core axioms: `propext`, `Classical.choice`, and `Quot.sound`.
