# Exact rotation-distance law for Cao's TASEP lift

2026-11-11. Continues [TASEP versus Tamari](tasep_tamari.md).
Executable: [tasep_rotation_distances.py](tasep_rotation_distances.py).
Checks: [tasep_rotation_distances_results.json](tasep_rotation_distances_results.json).
Expanded geometric proof: [independent audit](tasep_rotation_distance_audit.md).

The tree process is Cao's known unit-rate lift of open TASEP; the distance
results here are derived from its explicit construction, not attributed
to Cao as preexisting theorems. See [Cao, §II](https://arxiv.org/pdf/1404.3915).
No claim of priority for these derived distance formulas is made.

## Results and sampling convention

An N-site system uses trees with N+2 leaves and N+1 internal vertices.
Every marked cherry is one rate-one event. Sample events from stationary
jump flux: all tree/cherry pairs have equal weight. This differs from
sampling a uniform tree followed by a uniform choice among its cherries.
Distance always means the shortest undirected ordinary rotation distance
between the event's source and target tree, with leaves labeled by inorder
position. It is not elapsed time in the original jump process.

For every N>=1,

\[
\boxed{\mathbb E_N[d]=\frac{4N^2-2N+4}{(N+1)(N+2)}<4.}
\]

As N grows, the entire event-distance distribution converges:

\[
\boxed{\Pr_N(d=j)\longrightarrow\frac13\left(\frac23\right)^{j-2},\qquad j\ge2.}
\]

The limiting mean is 4, variance is 6, mode is 2, and median is 3.
The maximum distance at finite N is N. For N>=2 exactly two events attain
that maximum, with probability

\[
\boxed{\Pr_N(d=N)=\frac{2}{\binom{2N}{N}}
\sim\frac{2\sqrt{\pi N}}{4^N}.}
\]

These are mathematical consequences of the geodesic construction and
generating functions below, not extrapolations of the finite BFS data.
They have not been formalized in Lean.

## 1. Why the distance statistic is exact

Write a tree as `(L,R)` and let a cherry be two leaf children `(a,b)`.
For a subtree Y define

```text
f(leaf)=0
f((L,R))=f(R)       if L is a leaf
         1+f(L)     otherwise.
```

This counts left decisions on the search for the first right-child leaf.
Inserting an extra left end leaf into that search requires f(Y) rotations:
at a left decision rotate `(x,(L,R))` to `((x,L),R)` and recurse into
`(x,L)`; at a right decision the current root needs no rotation and one
recurses into the right child. Inorder relabeling is essential: the leaves
are positions in an ordered tree, not persistent material identifiers.

An internal subtree gives an interval of inorder leaf positions. A single
rotation removes one such proper interval and adds one. Therefore the
number of source intervals absent from the target is a lower bound on
rotation distance. The insertion recursion loses exactly one interval
at each left decision and none at each right decision, by induction.
Thus the constructed insertion path meets the lower bound.

By reflection, it suffices to consider a cherry that is a right child.
Its root path has exactly one of two forms:

* **Bulk:** `v L R^k`, k>=1, using the last L. At the pivot the subtree is
  `(X,Y)`, with `X=(A1,(A2,...(Ak,(a,b))))`. Bottom-up left rotations along
  the k right-spine ancestors turn X into `(X0,b)`. One right rotation at
  the pivot gives `(X0,(b,Y))`; insertion then costs f(Y). The k+1 source
  spine intervals disappear, in addition to the f(Y) insertion intervals.
  Therefore the exact distance is `k+1+f(Y)`.
* **Boundary:** the path is entirely right steps. At the cherry's parent
  rotate `(A,(a,b))` to `((A,a),b)` and perform reflected insertion into A.
  Exactly `1+f(mirror(A))` intervals disappear, so that is the exact distance.

The source intervals counted above are disjoint from the unchanged
context/sibling intervals. Hence these are matching upper and lower
bounds at every size. The audit expands the interval induction and
explicitly identifies the target subtree after Cao's relabeling.

## 2. Complete bivariate generating function

Let z count internal vertices and u mark distance. Define

\[
C(z)=1+zC(z)^2,\quad r=zC,\quad s=\sqrt{1-4z}=1-2r.
\]

Let `H(z,u)=sum_Y z^{|Y|} u^{f(Y)}`. The recursion for f gives

\[
H=1+zH+zuC(H-1)=\frac{1-ur}{1-z-ur}.
\]

The context above a marked pivot has generating function `1/(1-2zC)=1/s`.
The pure boundary spine has generating function `1/(1-zC)=C`.
Counting right-child events and their reflections gives

\[
\begin{aligned}
\mathcal B(z,u)&=2z^2uCH &&\text{(boundary events)},\\
\mathcal U(z,u)&=\frac{2z^3Cu^2}{(1-z-ur)s} &&\text{(bulk events)},\\
\mathcal A(z,u)&=\mathcal B+\mathcal U
=\boxed{\frac{2z^2uC(s+ur^2)}{(1-z-ur)s}}.
\end{aligned}
\]

The N-site distance-counting polynomial is `[z^{N+1}] A(z,u)`.
At u=1,

\[
E(z)=\mathcal A(z,1)=z(1/s-1),\qquad
E_N=\binom{2N}{N}=(N+1)C_N.
\]

There are `2*C_N` boundary events and `(N-1)*C_N` bulk events.

## 3. Exact finite-size law

The probability of a distance d is its event count divided by E_N.
For d>=2 the counts are

\[
\begin{aligned}
U_{N,d}&=2[z^{N-d}]\frac{C^{d-1}}{s(1-z)^{d-1}},\\
B_{N,d}&=2[z^{N-d-1}]\frac{C^d}{(1-z)^d}.
\end{aligned}
\]

A coefficient at a negative degree is zero. At d=1,

\[
U_{N,1}=0,\qquad B_{N,1}=2\sum_{j=0}^{N-1}C_j.
\]

These formulas explicitly separate bulk hops from boundary transitions.
They also prove that d<=N and that exactly two bulk events attain d=N
for N>=2: the bulk coefficient is then its constant term, equal to 2;
the boundary term is zero. For N=1 the two events both have distance one.

Using

\[
[z^j]C^h/s=\binom{2j+h}{j},\qquad
[z^j]C^h=\frac{h}{2j+h}\binom{2j+h}{j},
\]

the coefficient formulas become finite binomial sums, implemented as
`finite_distance_counts`. They require no tree enumeration or graph search.

## 4. Mean and variance from coefficient extraction

Differentiating A at u=1 gives

\[
\partial_u\mathcal A(z,1)=E(z)(2C^2-3C+2).
\]

For N>=1 define

\[
M_k(N)=\frac{2N}{2N+k}\frac{\binom{2N+k}{N}}{\binom{2N}{N}},\qquad M_0=1.
\]

Then exact extraction yields

\[
\begin{aligned}
\mathbb E_N[d]&=2M_2-3M_1+2
=\frac{4N^2-2N+4}{(N+1)(N+2)},\\
\mathbb E_N[d^2]&=4M_4-10M_3+14M_2-11M_1+4,\\
\operatorname{Var}_N(d)&=\mathbb E_N[d^2]-\mathbb E_N[d]^2.
\end{aligned}
\]

For verification, the second factorial derivative is
`E(z)*(4C^4-10C^3+12C^2-8C+2)`.
As N grows, `M_k -> 2^k`, giving mean 4, second moment 22, and variance 6.
The exact mean deficit is `(14N+4)/((N+1)(N+2))`, of order 1/N.

| N | Mean distance | Variance |
|---|---:|---:|
| 5 | 2.238095 | 0.736961 |
| 10 | 2.909091 | 1.621106 |
| 20 | 3.385281 | 2.918187 |
| 50 | 3.734540 | 4.429292 |
| 100 | 3.863716 | 5.142465 |
| limit | 4 | 6 |

## 5. Limiting distribution and rare events

Near z=1/4, the coefficient of `1/s` in A is `u^2/[4(3-2u)]`.
Dividing its singular amplitude by that of E, equal to 1/4, gives

\[
G(u)=\lim_{N\to\infty}\mathbb E_N[u^d]=\frac{u^2}{3-2u}.
\]

Expanding G proves the shifted geometric law above and
`Pr_infinity(d>=j)=(2/3)^(j-2)` for j>=2.
The denominator `1-z-u zC` stays nonzero at and within the positive
dominant disk for fixed 0<u<3/2. The square-root expansion is locally
uniform near u=1, justifying convergence of moments as well as probabilities.
For each fixed a with 1<a<3/2, exponential moments are bounded uniformly
in N. Thus there is a finite K_a such that

\[
\Pr_N(d\ge j)\le K_a a^{-j}.
\]

In particular system-scale distances d>=epsilon*N have exponentially
small probability for every fixed epsilon>0. This is a uniform bound,
not an unjustified substitution of growing j into a fixed-j limit.
For the precise maximum d=N, the exact `2/binom(2N,N)` probability is
stronger and gives the explicit `4^{-N}` asymptotic.

### Conditional boundary events

Boundary events vanish as a fraction `2/(N+1)` of all events, so the bulk
conditional limiting law equals G. Boundaries have a different conditional
limit. Expanding B to first order in s (its leading term is analytic)
and normalizing by the same coefficient at u=1 gives

\[
G_B(u)=\frac{u(u^2-3u+3)}{(3-2u)^2}.
\]

Its mean is also 4 but its variance is 12. Its probabilities are
`p_B(1)=1/3` and `p_B(j)=(j/8)*(2/3)^j` for j>=2.
Consequently `Pr_N(d=1) ~ 2/(3N)`. These single-rotation events are all
boundary events; bulk single-rotation probability is identically zero.

## Verification and limits of interpretation

Run from the repository root:

```sh
python3 math_project/experiments/tasep/tasep_rotation_distances.py --geometry-sites 8 --series-sites 100
```

The script checks every marked event through N=8: endpoint equals Cao's
move, every path step is an ordinary rotation, and every step reduces the
missing-interval lower bound by exactly one. It independently compares
the generating-function histograms with the earlier full-graph BFS data
through N=10. Polynomial recurrence, closed binomial counts, exact moments,
single-rotation counts, and maximum-distance counts agree through N=100.
These are meaningful independent checks of the all-size arguments above.

The result is bounded average geometric rearrangement cost, with a controlled
exponential tail, for this particular stationary lift and distance metric.
It supplies no clock for a rotation cascade, no universal result about
every TASEP lift, and no financial network model.

The [temporal-noise follow-up](tasep_rotation_noise.md) keeps Cao's original
clock and studies accumulated cost. It finds correlated marks and excess
physical-time noise at the larger computed sizes through N=10, and proves
that ordinary particle current cannot account for all cost noise for any
N>=3. These dynamical results are separate from the one-event law here.
