# TASEP versus Tamari: the stationary map works; single rotations fail

2026-11-11. Continues [rotation thermodynamics](../rotation_thermodynamics/rotation_thermodynamics.md).
Code: [tasep_tamari.py](tasep_tamari.py). Raw checks and search statuses:
[tasep_tamari_results.json](tasep_tamari_results.json).
Primary-source review: [tasep_tamari_literature.md](tasep_tamari_literature.md).

**Proof update:** the user's capacity argument settles the single-rotation
question for every N>=2 under the prescribed fiber-size assumption. The
mean-distance formula is now proved by a constructive geodesic argument
and generating functions, together with the full distance law. The limiting
mean is 4, variance is 6, and the limiting distribution has a geometric
tail. See [the distance theorem](tasep_rotation_distances.md) and its
[geometric proof audit](tasep_rotation_distance_audit.md).
The subsequent [temporal-noise experiment](tasep_rotation_noise.md) studies
correlations of these costs using Cao's original continuous-time generator.

## What is already known

The Catalan correspondence is stronger than a matching partition function.
For full planar binary trees with `N+2` leaves, remove the two extreme leaves
and read the remaining leaf orientations: left child = `1`, right child = `0`.
This canopy map sends the **uniform tree distribution** to the stationary
open TASEP distribution at injection, hopping and extraction rates all equal
to one. It is a surjection with stationary-weight-sized fibers, not a
bijection between configurations and trees. Cao gives an exact tree Markov
process projecting to TASEP using marked-cherry leaf transfers.
[Cao 2014, §§I–II](https://arxiv.org/pdf/1404.3915).

This experiment reproduces that known process rather than proposing it as
a new model. The move detaches a leaf from a cherry, suppresses the unary
node, and regrafts the leaf at another suitable leaf. Both mirror cases and
the boundary wrap cases are implemented directly from Cao's recipe.

## Exact checks for N = 2, 3, 4, 5

All tree and macrostate enumeration is exact integer arithmetic. Each of
these checks passes independently of the numerical optimization below:

* Fiber cardinalities equal matrix-ansatz weights computed using `DE=D+E`,
  `<W|E=<W|`, `D|V>=|V>`; these weights satisfy the exact TASEP stationary
  master equation.
* The marked-cherry transformation permutes the marked-tree set.
* At every tree, each allowed TASEP event has exactly one rate-one lift and
  there are no other projected events. This is strong lumpability: the
  particle process has the correct generator for every initial tree state,
  not only in stationarity.
* Each tree's incoming event count equals its outgoing event count, giving
  the uniform stationary tree measure.
* Every ordinary rotation changes zero or one canopy bits. No rotation
  realizes a bulk `10 → 01` hop under this projection.

| Sites N | Trees | Rotation edges | Cao events | Events that are one rotation | Maximum rotation distance of a Cao event |
|---|---:|---:|---:|---:|---:|
| 2 | 5 | 5 | 6 | 4 | 2 |
| 3 | 14 | 21 | 20 | 8 | 3 |
| 4 | 42 | 84 | 70 | 18 | 4 |
| 5 | 132 | 330 | 252 | 46 | 5 |

Rotation distances use both directions and were computed here by exact
graph BFS. The later distance theorem proves the maximum is N at every size.

The one-bit obstruction holds at every size: in `((A,B),C) → (A,(B,C))`,
only the middle subtree B changes which side of a parent it occupies. If B
is internal, its leaves retain their immediate parent orientations. If B
is a leaf, exactly its bit flips. It is an interior leaf. This is also the
content of Lemma 7 of
[Préville-Ratelle–Viennot](https://arxiv.org/pdf/1406.3787).
Their Proposition 9 identifies fixed-canopy fibers as Tamari intervals.

## Can arbitrary assignments rescue single rotations?

We also allow a completely different assignment of configurations to trees.
The requirements are explicit:

1. Each tree gets one configuration c.
2. Exactly w(c) trees receive c, where w is the integer TASEP stationary
   weight normalized by w(empty)=1.
3. From **every** tree labeled c, each allowed rate-one TASEP successor d
   must be available through some single undirected rotation edge.
4. Edge rates may depend arbitrarily on the tree; unused edges may have
   rate zero. Uniform tree stationarity is **not** required in this search.

For binary variables x[v,c], the constraints are

```text
sum_c x[v,c] = 1
sum_v x[v,c] = w(c)
x[v,c] <= sum_{u adjacent to v} x[u,d]    for each allowed c → d.
```

These are necessary and sufficient for some rotation-supported strongly
lumpable rate-one TASEP lift with those fiber sizes: if feasible, choose
one neighboring tree per required successor, put rate one on those chosen
edges, and zero elsewhere. Different outgoing TASEP events have distinct
destination configurations. The conditions do not guarantee that the tree
stationary measure is uniform, making this search more permissive than
the original uniform-microstate question.

The historical SciPy/HiGHS integer runs report **infeasible for N=2,3,4**. For N=2,
an independent exhaustive check of all 60 label assignments agrees.
These solver results are finite computational evidence, not Lean proofs
or externally checked infeasibility certificates. The N=5 solver reached
its 60-second limit without a feasible assignment or an infeasibility result.
That computational limitation is now superseded by the all-N proof below.
A separate N=1 positive control returns a valid assignment, as expected.

### General impossibility theorem, N>=2

**Theorem.** For unit-rate open TASEP, no surjection from the N+2-leaf tree
rotation graph, with fiber cardinalities equal to the stationary weights
w(c), strongly projects a rotation-supported Markov generator to TASEP,
for any N>=2. Microstate-dependent nonnegative rates, both rotation
directions, and unused edges of rate zero are allowed. Uniform microscopic
stationarity need not be assumed.

The fiber-cardinality assumption is essential to this proof. We do not
assert this stronger conclusion for arbitrary fiber cardinalities with
nonuniform microscopic stationary measures.

**Proof (user's capacity argument, simplified by stationary balance).**
Write r(c) for the number of outgoing TASEP events from c. Every tree in
its fiber needs r(c) distinct outgoing neighbor slots. No allowed TASEP
transition has an allowed reverse when N>=2: reversing a hop would require
01->10, and reversing a boundary flip would require the opposite flip at
that same boundary, which is absent. Therefore the slots used for incoming
and outgoing cross-fiber transitions are disjoint. This last observation
is required to justify subtracting outgoing slots from incoming capacity.

Every source tree in every predecessor fiber s->c requires at least one
edge into the c-fiber. Distinct source trees require distinct edges.
Consequently, for any supporting graph of maximum degree Delta,

```text
sum_{s->c} w(s) <= w(c) * (Delta - r(c)).
```

The exact unit-rate stationary master equation gives

```text
sum_{s->c} w(s) = w(c) * r(c).
```

Since w(c)>0, feasibility requires `2*r(c) <= Delta` for every c.
For alternating c=0101..., `r(c)=floor(N/2)+1`, and

```text
2*r(c) = N+2  if N is even,
         N+1  if N is odd.
```

The tree rotation graph has degree Delta=N, giving the contradiction for
every N>=2. This is a mathematical proof; the finite checks merely verify
examples. It also gives a lower bound on maximum supporting degree for
any graph with these fiber cardinalities, not only tree graphs.

Corrected capacity witnesses (the user's N=6 and N=7 capacities and demands
were numerically incorrect):

| N | Alternating c | w(c) | r(c) | Incoming capacity | Incoming demand | Slack |
|---|---|---:|---:|---:|---:|---:|
| 2 | 01 | 1 | 2 | 0 | 2 | -2 |
| 3 | 010 | 2 | 2 | 2 | 4 | -2 |
| 4 | 0101 | 2 | 3 | 2 | 6 | -4 |
| 5 | 01010 | 5 | 3 | 10 | 15 | -5 |
| 6 | 010101 | 5 | 4 | 10 | 20 | -10 |
| 7 | 0101010 | 14 | 4 | 42 | 56 | -14 |

The executable `capacity_witness` checks the stationary balance and
violation directly; it was run through N=30. The proof does not depend on
the Catalan formula for the alternating weight.

### Short analytic impossibility proof for N=2 and N=3

Let d=`0^(N−1)1`. Its weight is one, so it has a unique tree v. The unique
predecessor c=`0^(N−2)10` has weight two. Each of the two c-trees must be
adjacent to v to realize the hop c→d. Meanwhile v must have neighbors for
both its injection and extraction events, with distinct labels
`10^(N−2)1` and `0^N`. These labels also differ from c.

Thus v needs at least four distinct neighbors. The rotation graph on
`N+2`-leaf trees is N-regular. This is impossible for N=2 or 3, independent
of any solver and without assuming uniform tree stationarity. It does not
settle N≥4 by itself; the preceding capacity proof does.

## Distance scaling audit

Extended raw enumeration: [tasep_tamari_extended_results.json](tasep_tamari_extended_results.json).
All distances below are exact shortest paths in the undirected rotation
graph, computed by BFS, not lengths of a chosen rotation decomposition.

| N | Trees | Rate-one events | Sum of event distances | Mean distance | Maximum event distance |
|---|---:|---:|---:|---:|---:|
| 2 | 5 | 6 | 8 | 1.333333 | 2 |
| 3 | 14 | 20 | 34 | 1.700000 | 3 |
| 4 | 42 | 70 | 140 | 2.000000 | 4 |
| 5 | 132 | 252 | 564 | 2.238095 | 5 |
| 6 | 429 | 924 | 2244 | 2.428571 | 6 |
| 7 | 1430 | 3432 | 8866 | 2.583333 | 7 |
| 8 | 4862 | 12870 | 34892 | 2.711111 | 8 |
| 9 | 16796 | 48620 | 137020 | 2.818182 | 9 |
| 10 | 58786 | 184756 | 537472 | 2.909091 | 10 |

Sampling convention: P_N(d) describes an event sampled from the stationary
flux. Each tree has the same stationary probability, and each cherry has
rate one, so counting all tree/cherry pairs equally gives this distribution.
Choosing a uniform tree first and then a uniform cherry would give a
different distribution.

The user's percentage table through N=7 is reproduced, up to rounding.
The subsequent proof resolves several questions that were initially only
numerical hypotheses:

* **Mean:** the former rational conjecture
  `(4*N^2 - 2*N + 4)/((N+1)*(N+2))` is now proved for all N>=1 by
  matching a constructive path with the missing-interval lower bound and
  extracting generating-function coefficients. It is strictly below 4
  and converges to 4. The earlier logarithmic fit was misleading.
* **Maximum:** d_max=N is now proved, attained by exactly two events
  for N>=2. It is the maximum distance of a Cao event, not the diameter
  of the whole associahedron graph. For example, an independent all-pairs
  BFS at N=6 gives graph diameter 9, whereas Cao event distances stop at 6.
* **Mode:** d=2 is the mode for N=3..10; the full limiting law also has
  mode 2. No all-N finite-size mode theorem is supplied.
* **Single rotations:** the positive P_N(1) counts boundary events.
  Bulk hops have P_N(1)=0 exactly by the canopy obstruction. Event-kind
  histograms through N=7 verify this directly. The total event count is
  `(N+1)*C_N`, of which `2*C_N` are boundary events, so their frequency
  already decreases as `2/(N+1)`. A decreasing unconditional single-rotation
  fraction does not by itself imply a divergent typical bulk-hop distance.

For reference, the single-rotation event counts through N=10 are
`4,8,18,46,130,394,1252,4112,13836`. The identity
`2*sum(C_k, k=0..N-1)` and `P_N(1) ~ 2/(3N)` are now consequences of
the full distance generating function in the distance theorem.

## Physics interpretation

The tree supplies microscopic degeneracy. The occupation string is a
coarse-grained observable; its nonuniform stationary probabilities are
fiber volumes in a uniform microscopic stationary measure. But uniform
stationarity is not detailed balance: the leaf-transfer process supports
a directed exclusion-gas current.

Every bond has the same exact stationary current, checked separately for
injection, each bulk hop and extraction:

```text
J_N = C_N / C_(N+1) = (N+2)/(4N+2).
N=2: 2/5; N=3: 5/14; N=4: 1/3; N=5: 7/22.
```

The dynamics is discrete and finite; no hydrodynamic PDE is needed for
these statements. Nevertheless the microscopic moves are generally
nonlocal in rotation distance. Replacing a Cao jump by a path of rotations
with additional waiting times is a different stochastic process unless
one proves an appropriate elimination or time-change result.

The theorem establishes an obstruction to single-rotation lifts with the
specified fiber sizes. It does not prove that every possible lift has an
unbounded typical rotation distance. Rotation distance also does not
automatically measure subtree depth, number of obligations, physical time,
or work. In Cao's generator the leaf transfer is an atomic jump; a temporal
cascade of rotations is an additional model choice.

No economic debt-network dynamics, map from obligations to trees, or
empirical observations enter this calculation. Reassociation of financial
obligations is a possible analogy, not a consequence of this theorem;
in particular logarithmic debt-network reorganization has not been shown.

This is therefore **not an identification of TASEP current with the earlier
biased-rotation J_sigma**. They use different microscopic generators. Nor
does an endpoint-to-endpoint rotation path define an unambiguous sigma
increment: alternative paths can differ by pentagon circulation.

## Reproduce and next questions

```sh
python3 math_project/experiments/tasep/tasep_tamari.py
python3 math_project/experiments/tasep/tasep_tamari.py --min-sites 6 --max-sites 10 --output math_project/experiments/tasep/tasep_tamari_extended_results.json
uv run --python 3.12 --with scipy python math_project/experiments/tasep/tasep_tamari.py --search --seconds 60
```

The first command runs exact enumeration without external dependencies;
the second reproduces the extended dataset in a separate file (about a
minute on the machine used here). The third also runs the historical
bounded integer searches; these are now unnecessary for the existence
question because of the capacity proof. Running without --search omits
historical solver statuses from the selected output JSON.

The rotation-only existence question with these fiber sizes is settled by
the capacity theorem. The distance law is now settled as well, with exact
bulk/boundary counts, bounded mean and variance, exponential tail bounds,
and an exact probability for maximum-distance events. See the standalone
distance proof and executable certificates linked above. A subsequent
question is whether an explicitly timed local rotation process can recover
the same projected dynamics after eliminating intermediate states; the
geometric distance theorem alone does not provide such a process.
