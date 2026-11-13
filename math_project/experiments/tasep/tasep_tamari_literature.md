# TASEP, tree canopies, and Tamari rotations

Primary-source check, 2026-11-11. This distinguishes known constructions from deductions and the separate finite-size experiment.

## Known tree projection and dynamics

**Cao (2014), §§I–II, Propositions 1–2 and Lemmas 3–5:** use full planar binary trees with `N+2` leaves (`C_{N+1}` trees). Read interior leaves from left to right: left child = particle `1`, right child = hole `0`; discard extreme leaves. The uniform tree measure projects to the stationary open TASEP measure at `α=β=1`. This is a surjection, not a bijection to the `2^N` configurations. [Paper](https://arxiv.org/pdf/1404.3915).

His marked-tree permutation gives a dynamical lift. Mark a cherry (two leaf children). If it is a right child, remove its left leaf edge, suppress the now unary cherry, and reattach that edge at the next right-child leaf to its right, making a new cherry. If there is no such endpoint, use the rightmost left-child leaf and reverse the moved edge's orientation. Mirror this recipe for a left-child cherry. Mark the new cherry. Each cherry corresponds to one active TASEP bond; give each event rate `1`. The marked-tree map is bijective. [Same paper, §II](https://arxiv.org/pdf/1404.3915).

**Duchi–Schaeffer:** their original lift uses complete configurations with two rows of particles. The first row follows TASEP; the second supplies return circulation. At equal unit rates the lifted stationary distribution is uniform. Their discrete-time convention selects one of `N+1` walls uniformly, including inactive attempts. Continuous-time rate-one clocks recover the usual TASEP; changing the overall time scale does not change stationarity. This should not be described as a theorem identifying hops with ordinary binary-tree rotations. [Paper, §§1.1–1.4](https://arxiv.org/pdf/math/0407519).

## Exact obstruction for ordinary rotations under the canopy map

Préville-Ratelle–Viennot, **Lemma 7**, show that the rotation

```text
((A,B),C) → (A,(B,C))
```

preserves the interior canopy when `B` is nontrivial. If `B` is a leaf, it changes exactly one canopy entry. **Proposition 9** says each fixed-canopy fiber is an interval of the ordinary Tamari lattice; Proposition 11 identifies it with a generalized `Tam(v)`. The conventions identifying letters with north/east steps vary, but the one-bit statement is independent of that choice. [Paper, §§2, 4–5](https://arxiv.org/pdf/1406.3787).

**Deduction here:** a bulk hop `10→01` changes two bits, so no single ordinary rotation realizes a bulk hop under this canopy map. A rotation can be an invisible rearrangement within a fiber, or a one-bit change. Some boundary events can therefore be single rotations. This obstruction permits multi-rotation realizations and does not exclude an unrelated assignment of configurations to trees.

**Further deduction:** right rotations alone form an acyclic directed graph, so they cannot provide an irreducible lift of recurrent open TASEP. Allowing both rotation directions removes this particular acyclicity obstruction, but the canopy obstruction remains.

## Tableaux literature and what is already known

Corteel–Williams construct a Markov chain on permutation tableaux which projects to PASEP, then transfer it to permutations. Thus exact dynamical lifts were already known, not merely matching stationary counts. [2006 preprint / 2007 paper](https://arxiv.org/abs/math/0609188).

Their later staircase tableaux encode the stationary distribution for general open ASEP parameters. This is broader than the unit-rate TASEP specialization; it does not by itself identify its dynamics with ordinary Tamari edges. [Paper](https://arxiv.org/pdf/0910.1858).

Viennot explicitly discusses both TASEP/Catalan tableaux and Tamari rotations; that shared combinatorial framework does not eliminate the distinction between the two dynamics. [Author's SLC79 talk description](https://viennot.org/abstractslc79.html).

## Implementation consequences

1. Enumerate `N+2`-leaf trees and use the explicit canopy projection before searching arbitrary partitions.
2. Check fiber cardinalities against independently computed TASEP stationary weights.
3. Classify every ordinary rotation by its canopy change; bulk-hop support must be absent.
4. For an exact lift, implement Cao's leaf transfer, then verify the marked-tree permutation, balance of unmarked tree event counts, and generator intertwining `L_tree(f∘R)=(L_TASEP f)∘R`.
5. Do not infer that a projection of stationary measures also projects Markov dynamics: the generator identity is the stronger condition.

The natural-map question has a known analytic obstruction. Any arbitrary-fiber search needs its own precisely stated support, rate, and stationarity assumptions; success or failure under the canopy map cannot settle that larger question.
