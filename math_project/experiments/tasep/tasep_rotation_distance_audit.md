# Audit: exact rotation distances of Cao's unit-rate tree events

Date: 2026-11-11. This is an independent proof audit, not a claim that the distance formulas occur in the cited literature. The event construction and canopy projection are from [Cao, 2014, §II](https://arxiv.org/pdf/1404.3915). The distance results below are derived here.

## Conventions and claim

An ordered full binary tree has `M=N+1` internal vertices and `N+2` leaves. Label leaves by their current left-to-right positions. An event means a tree together with a marked cherry (an internal vertex with two leaf children); each event has rate one. Rotation distance is undirected ordinary binary-tree rotation distance, allowing both association directions.

The sampling convention is uniform over **events**, not uniform over trees followed by uniform choice of one of that tree's cherries. Uniform stationary trees and unit rate per cherry induce the former distribution when sampling actual jump times.

For `N≥1`, the exact event-average distance is

\[
\mathbb E_N[d]=\frac{4N^2-2N+4}{(N+1)(N+2)}.
\]

Consequently it tends to `4`, rather than growing logarithmically. In fact its limiting probability generating function is

\[
G(u)=\frac{u^2}{3-2u}.
\]

The proof below establishes these statements for all sizes, without extrapolating a finite numerical fit.

## 1. A leaf-insertion subproblem with a matching lower bound

Let `x` be a leaf preceding all the leaves of `Y`. Define the ordered tree `P(x,Y)` recursively:

```text
P(x,leaf y) = (x,y)
P(x,(leaf y,R)) = (x,P(y,R))
P(x,(L,R)) = (P(x,L),R)          when L is nontrivial.
```

The labels in this definition maintain the order of the input leaves. Combinatorially, the shape is obtained by inserting a leaf immediately before the first right-child leaf of `Y`, then assigning the ordered input labels. This is exactly the renumbered local insertion needed for a rightward Cao move. The same observation follows recursively: if the left child is a leaf, the search continues in the right subtree; otherwise it continues in the left subtree.

Define

```text
f(leaf)=0
f((leaf,R))=f(R)
f((L,R))=1+f(L)                when L is nontrivial.
```

Then

\[
d\big((x,Y),P(x,Y)\big)=f(Y).
\]

**Upper bound.** In the second case recurse inside the right subtree, making no rotation at the current root. In the third case first rotate `(x,(L,R)) → ((x,L),R)`, then recurse on `(x,L)`. This constructs exactly `f(Y)` rotations.

**Lower bound.** An internal vertex corresponds to the interval of ordered leaf positions below it. A rotation removes one internal interval and adds one. Therefore the number of source internal intervals absent from the target is a lower bound on distance.

Induction shows that this number is exactly `f(Y)`. For the second case, the source right-subtree interval `[y,last(R)]` remains the interval of the target right subtree `P(y,R)`; all interval changes are those of the recursive comparison `(y,R)` with `P(y,R)`. For the third case, the source interval of `Y`, `[first(L),last(R)]`, is absent: target subtrees lie either inside `P(x,L)` or inside `R`, while the target root starts at `x`. The source intervals in `R` remain; changes among intervals in `L` are exactly the recursive comparison `(x,L)` with `P(x,L)`. The artificial root interval of `(x,L)` is common in that recursive comparison and hence does not contribute. This adds precisely one lost interval to `f(L)`.

Reflection gives the corresponding right-leaf insertion statement, with cost `f(mirror(Y))`.

## 2. Classification of a marked-cherry event

Use `L,R` for edge directions in the path from root to the marked cherry. By reflection it suffices to consider paths ending in `R`.

### Bulk case: path `v L R^k`, with `k≥1`

Take the **last** `L` in the path. At its parent the source subtree is `(X,Y)`, where

```text
X = (A1,(A2,...(Ak,(a,b))...)).
```

All `Ai` are arbitrary trees and `(a,b)` is the marked cherry. The surrounding context `v` is unchanged by the event. The next right-child leaf to the cherry's right lies in `Y`.

After Cao's transfer and left-to-right renumbering, the target subtree is

```text
(X0,P(b,Y)),    X0=(A1,(A2,...(Ak,a)...)).
```

The symbols `a,b` here are the original **positions**, not persistent material labels for the moved edge. Renumbering is essential: the retained old leaf `b` takes position `a`, and the right-side input order starts at position `b`.

There is a path of `k+1+f(Y)` rotations: rotate left along the `k` right-spine ancestors of the cherry to turn `X` into `(X0,b)`; rotate `((X0,b),Y) → (X0,(b,Y))`; then apply the insertion path from §1.

The same number is a lower bound. The cherry and its `k` ancestors inside `X` give `k+1` source intervals ending at position `b` and starting at or before `a`. None occurs in the target: `X0` ends at `a`, the right subtree starts at `b`, and a target interval crossing that split includes all of `Y` and thus ends after `b`. Intervals inside `Ai` and in the surrounding context persist. Among source intervals of `Y`, exactly `f(Y)` disappear by §1. Thus

\[
\boxed{d=k+1+f(Y).}
\]

### Boundary case: path `R^k`, with `k≥1`

At the marked cherry's parent the source is `(A,(a,b))`. There is no right-child leaf to its right. The rightmost left-child leaf lies in `A` (including the case that `A` itself is a leaf). Cao's boundary regraft gives the reflected insertion into `A`, with `b` remaining the extreme right leaf.

Rotate once to `((A,a),b)`, then use the reflected insertion path on `(A,a)`. The source cherry interval `[a,b]` is absent in the target, and §1 counts exactly `f(mirror(A))` other lost intervals inside `A`. All upper right-spine intervals are unchanged. Therefore

\[
\boxed{d=1+f(\operatorname{mirror}(A)).}
\]

These two cases exhaust right-child cherries; reflection exhausts the remaining events. The constructed paths attain the universal interval lower bound, so they are geodesics.

## 3. Full bivariate generating function

Let `z` count internal vertices and `u` count distance. Set

\[
C=1+zC^2,\qquad r=zC,\qquad s=\sqrt{1-4z}=1-2r.
\]

An arbitrary outer context with one hole has generating function `1/(1−2zC)=1/s`: each ancestor contributes one internal vertex, one arbitrary sibling, and two choices of hole direction.

Let `H(z,u)=Σ_Y z^{|Y|}u^{f(Y)}`. The recursion in §1 gives

\[
H=1+zH+zuC(H-1)
 =\frac{1-uzC}{1-z-uzC}.
\]

For right-child cherries, the boundary contribution is `z²uCH`. The bulk contribution is `z²H/s` times `Σ_{k≥1}(zC)^k u^{k+1}`, hence `z³CHu²/[(1-uzC)s]`. Reflection doubles both. Consequently the exact bivariate event generating function is

\[
\boxed{\mathcal A(z,u)
 =2z^2uH\left(C+\frac{uzC}{(1-uzC)s}\right)
 =\frac{2z^2uC\,[s+u(zC)^2]}{(1-z-uzC)s}.}
\]

`[z^{N+1}u^d] A` is the number of size-`N` TASEP lift events with rotation distance `d`.

At `u=1`,

\[
E(z)=\mathcal A(z,1)=z\left(\frac1{\sqrt{1-4z}}-1\right),
\qquad [z^{N+1}]E=\binom{2N}{N}=(N+1)C_N.
\]

Differentiating at `u=1` yields the total distance generating function

\[
D(z)=\partial_u\mathcal A(z,1)=E(z)(2C^2-3C+2).
\]

Using `[z^N]C^j/√(1−4z)=binom(2N+j,N)`, its coefficient is

\[
2\binom{2N+2}{N}-3\binom{2N+1}{N}+2\binom{2N}{N}
 -2C_{N+1}+3C_N
=\binom{2N}{N}\frac{4N^2-2N+4}{(N+1)(N+2)}.
\]

Dividing by the event count proves the mean formula.

## 4. Limiting law, tails, and finite-size extremes

Near `z=1/4`, the coefficient of `1/√(1−4z)` in `A(z,u)` is `u²/[4(3−2u)]`. At `u=1` it is `1/4`. Singularity coefficient comparison therefore gives

\[
\lim_{N\to\infty}\mathbb E_N[u^d]=\frac{u^2}{3-2u},
\qquad
\Pr_\infty(d=j)=\frac13\left(\frac23\right)^{j-2},\quad j\ge2.
\]

Thus limiting mean is `4`, limiting variance is `6`, and `Pr∞(d≥j)=(2/3)^{j−2}` for `j≥2`. The formulas hold analytically in a neighborhood of `u=1` (indeed for positive `u<3/2`), so this also gives convergence of moments and bounded exponential moments in that range; weak convergence alone would not suffice for the variance claim. These are limiting tails, not an assertion of an identical geometric distribution at every finite `N`.

Two useful exact checks are

\[
[u]\mathcal A(z,u)=\frac{2z^2C}{1-z},
\qquad
\#\{d=1\}=2\sum_{j=0}^{N-1}C_j.
\]

Only boundary events have distance one. Their overall event fraction tends to zero. The maximum distance is `N`, attained by exactly two events for `N≥2`. To attain it in the bulk node budget `M=k+2+|Y|+Σ|Ai|+|context|`, every `Ai` and `Y` must be leaves and the context must be empty, since `f(Y)<|Y|` for nontrivial `Y`. This leaves one right-child event and its reflection. Boundary events do not attain `N≥2`.

The average is bounded while the worst case grows linearly. They measure different aspects of the same event distribution.

## Audit status and scope

The recursive paths, missing-interval argument, generating functions, and coefficient extraction above are all-size arguments. Separate checks performed during this audit found the structural interval count correct for every right-child event through `N=8`, and interval lower-bound equality with independently computed BFS distances for every event through `N=6`. The parent computation extends exact BFS further.

This says how Cao's established microscopic lift sits in the rotation graph. It does not establish an economic interpretation, identify the lift with a single-rotation TASEP model, or assert a continuum scaling law for markets.
