# Testing the higher-level observer / lower-level subsystem hypothesis

## Question and verdict

Does a larger relational structure observing a smaller associahedral subsystem force quantum measurement rules?

The test establishes a limitation: the nesting admits a classical recorder as well as a chosen quantum model. Thus nesting alone does not force quantum measurement. It can accommodate quantum measurement once quantum state, evolution and probability rules are added. This is a test of a mathematical implication under our finite model, not an experimental test that humans or real particles are associahedra.

## A real subsystem decomposition inside K6

Fix the bracket `[0,3)` in six inputs. Grafting a three-input tree into the first leaf of a four-input tree gives the ten vertices of a genuine K3 × K4 facet:

```text
K3: subsystem with two bracketings, dimension one
K4: observer/pointer with five bracketings, dimension two
K6: larger containing system with 42 bracketings, dimension four.
```

The script verifies this vertex embedding exactly. Its induced adjacency is the Cartesian-product adjacency. The tensor representation `C² ⊗ C⁵` is a chosen linearization of those ten labels, not a quantum postulate forced by face inclusion. The same labels support classical probabilities.

In the vertex-basis representation, K1 and K2 each have only one basis state. Neither alone gives a two-level quantum system without additional internal or path degrees of freedom.

## Test 1: construct a classical countermodel

Use ordinary probabilities on the ten product configurations. Give the observer five pointer states and let a reversible controlled permutation copy the subsystem's binary configuration into pointer states 0 and 1.

The observer records the subsystem with accuracy one. A 50–50 unknown subsystem produces two correlated joint configurations with probabilities one half each. All probabilities are nonnegative and normalized. No complex amplitudes, quantum update or interference is needed.

This countermodel has the same actual nesting and observer/subsystem state labels. Its existence disproves the implication that these geometric facts alone require quantum measurement.

We also represent each of K6's 14 elementary bracket requirements as a diagonal presence-test projector. All 91 projector pairs commute exactly. A non-distributive face lattice does not automatically become the noncommuting lattice of quantum observables: a face join is geometric closure, whereas a classical event union is a different operation.

## Test 2: inspect the previously chosen graph Hamiltonian

On the isolated product facet the negative-link Hamiltonian has the form

```text
H_local = H_subsystem ⊗ I + I ⊗ H_observer.
```

Consequently its evolution factorizes. A product initial state remains unentangled, and the pointer dynamics do not depend on the subsystem's input. The script verifies factorization, subsystem purity one, and equal pointer outputs at four times.

The full K6 Hamiltonian has external couplings. After adding quantum evolution and conditioning on return to the product facet, it can generate entanglement between the two factors. For the chosen initial product basis state:

| Time | Probability of the facet | Conditional subsystem purity |
|---|---:|---:|
| 0.2 | 0.961047397 | 0.999999964 |
| 0.7 | 0.639753022 | 0.999053754 |
| 1.4 | 0.307821286 | 0.883315644 |

Purity below one certifies entanglement for this conditional pure joint state. Both unitary evolution and Born postselection are already assumed. These values match an ordinary-link quantum control: on this regular graph `H_negative = 8I − L_ordinary`, giving conjugate evolution up to a global phase for a real initial state. The correlations in this experiment are therefore not a special consequence of the parity links.

## Test 3: add a standard quantum recorder and track the assumptions

Use complex amplitudes, tensor-product states, Born probabilities, and a chosen controlled recording interaction. A coherent equal superposition is mapped to

```text
(|0,pointer0> + |1,pointer1>)/sqrt(2).
```

The joint state has purity one; both reduced states have purity one half. Its visible basis probabilities exactly match the classical recorder, but it has off-diagonal coherence. A phase-sensitive measurement distinguishes equal-probability input states with opposite relative phases. Ignoring an orthogonal pointer record removes this local interference. Reversing the controlled interaction restores it.

These are the standard premeasurement/partial-trace structures described in [Preskill's composite-state notes](https://www.preskill.caltech.edu/ph219/chap2_15.pdf) and [measurement notes](https://www.preskill.caltech.edu/ph219/chap3_15.pdf). Partial trace describes restricted access; it does not choose a single actual global outcome.

Vary pointer-record overlap without changing the geometry:

```text
pointer0 = |0>
pointer1 = cos(α)|0> + sin(α)|1>

interference visibility V = |cos(α)|
record distinguishability D = |sin(α)|
V² + D² = 1.
```

All nine tested record strengths satisfy the tradeoff. The continuous free parameter demonstrates that the geometry alone does not choose a measurement strength.

## Test 4: stronger quantum diagnostics

After adding standard projective instruments, selective Z-then-X and X-then-Z joint outcome probabilities are respectively one half and one quarter for the selected initial state. This verifies incompatibility of those added observables. Order effects alone are insufficient: two ordinary classical read-and-reset operations also fail to commute, and the script constructs that counterexample.

For an added entangled state and the standard CHSH observables, the script obtains `2sqrt(2) ≈ 2.828427125`. All sixteen deterministic local response assignments give absolute values at most two. A dephased correlated state gives approximately 1.414213562 with the same observables. It also verifies the no-signalling identity for nonselective local projective measurements.

The original [CHSH paper](https://doi.org/10.1103/PhysRevLett.23.880) supplies the physical distinction under locality and measurement-setting independence. Our matrix calculation adds the relevant quantum state and measurements; it is neither a physical Bell experiment nor evidence that face nesting produces them. No spatially separated stations are supplied by this facet construction.

## What would make the hypothesis stronger

The remaining task is to supply observer–subsystem interaction rules from the relational theory itself. They would need to constrain the state space, coherent composition, admissible observables, outcome probabilities and recording dynamics. Recovering quantum phenomena after inserting quantum rules establishes compatibility. Deriving those rules from additional independently motivated relational axioms would establish something stronger.

## Reproduce

Run `python3 math_project/experiments/nested_measurement.py` with NumPy installed. All 163 assertions passed, including exact embedding/commutation tests, numerical factorization, partial traces, interference, gauge-connection controls, Bell correlations and no-signalling identities. No new Lean proof or empirical experiment was performed.

- [Test script](nested_measurement.py)
- [Recorded results](nested_measurement_results.json)
- [Primary references and interpretation limits](measurement_sources.md)
