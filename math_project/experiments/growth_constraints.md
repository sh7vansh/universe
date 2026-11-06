# Does completion-driven growth select physics?

## Tested verdict

Under the current formalization, no: completion selects the growth trigger, not a unique field equation, rate, mass, exploration order, or clock. This is demonstrated by explicit countermodels rather than an unsuccessful parameter search.

We define a completed record as all vertices and elementary rotation edges having been explored. This is the finite completion convention previously adopted, not a statement about visiting all paths. Arbitrarily repeated cycles make the collection of paths infinite.

## Countermodels

Two frontier-based exploration orders complete K6's same 42 vertices and 84 edges, but list the edges in different orders. Every proper prefix is incomplete; both final records satisfy the trigger. Durations of one versus 2.5 per record event give completion times 84 versus 210 with identical final structure.

Keep this completion record fixed and choose each of the following field laws:

```text
u̇ = −Lu
u̇ = −2Lu
iψ̇ = H₋ψ.
```

Starting at the same vertex, their probabilities at time one differ. The first two distributions differ by about 0.428 in L1 norm; the first and the quantum probabilities differ by about 0.810. All remain normalized. Thus the record rule does not distinguish these dynamics, and does not fix even the diffusion rate. Mass-squared choices 0.25 and 2.25 likewise satisfy the same trigger but shift the wave spectrum by 2.

This uses the current product of a completion record and a field state. No rule linking an exploration event to field evolution has yet been supplied. Defining such a coupling would change the model and could impose further constraints.

## Genuine constraints

Appending x embeds K6 isometrically into K7's configuration space and preserves its internal edges. For either ordinary or all-negative-link operators, the larger operator restricted to old vertices is the old intrinsic operator plus identity. However, the full operator does not preserve the old subspace: new relations couple it to new configurations.

With unit negative links and zero initial amplitude outside the old facet, short-time quantum probability outside it is `t² + O(t³)`; the leading coefficient is exactly one for any normalized old state. The script checks the exterior coupling matrix algebra exactly and checks convergence of the probability/time-squared ratio to one numerically. This conclusion depends on unit coupling and this initial-state extension.

If each event completes exactly one new relation, no work is repeated, completed work is inherited and events take unit time, the stage work is fixed:

```text
Finish K7 before adding x8:     246 new relations
Finish K8 before adding x9:     957
Finish K9 before adding x10:  3,718
Finish K10 before adding x11: 14,443.
```

For arity n, edge count is `(n−2) Catalan(n−1)/2`. With those additional timing assumptions, accumulated work grows proportionally to `4^n/sqrt(n)`. Parallel completion, revisits, or varying costs change the duration. No cosmological expansion rate follows without such assumptions.

## Completion is a separate mathematical layer

Two vertices can already have the whole K6 as their face join, while 40 configurations and most relations remain unexplored. Reaching the face-lattice top is therefore insufficient.

The record of completed edges is a subset of 84 edges. These records form a Boolean lattice, and their cardinality valuation has identically zero modular defect by inclusion–exclusion. This is distinct from the paper's nonzero signed face-rank defect. A physical energy for this enlarged history state must be defined explicitly; the two rank functions cannot be silently identified.

## Reproduce

Run `python3 math_project/experiments/growth_constraints.py` with NumPy installed. All assertions passed. See [recorded results](growth_constraints_results.json) and [test code](growth_constraints.py). Checks concern this finite mathematical model, not experimental physics or new Lean theorems.
