# Temporal noise of Cao rotation costs: theory and source audit

Date: 2026-11-11. This note fixes conventions and derives finite-state formulas independently of the numerical experiment. The observable is the **unsigned geodesic rotation distance** of each Cao jump. It is not a signed rotation current.

## 1. Physical-time generator and additive observables

Use a row generator acting on column functions:

```text
(Lf)(x) = Σ_{e:x→y} q_e [f(y)−f(x)],   πL=0,   L1=0.
```

For the unit-rate lift each marked cherry is an event with `q_e=1`; retain event multiplicities if several events have identical endpoints. Let `a_e` be its distance, `1` for event count, or an injection indicator. Define the accumulated observable `A_t=Σ_{jumps≤t}a_e` and

\[
(B_af)(x)=\sum_{e:x\to y}q_e a_e f(y),\quad
b_a=B_a1,\quad \mu_a=\pi b_a,\quad
c_{ab}(x)=\sum_{e:x\to y}q_e a_e b_e.
\]

Here the `b_e` inside `c_ab` denotes the second **edge observable**, not its local drift. Centering the local drift alone does not replace centering the full jump observable.

The row formulation of the tilted generator is

\[
(L_{\theta}f)(x)=\sum_{e:x\to y}q_e e^{\theta a_e}f(y)-r(x)f(x),
\qquad r(x)=\sum_{e:x\to y}q_e.
\]

Keep the original escape diagonal: recomputing it from the tilted off-diagonal entries would make a Markov generator with zero principal eigenvalue and destroy the generating function. The principal eigenvalue gives the scaled cumulant generating function; its first two derivatives are drift and variance rate. This is the jump-process construction in [Chetrite–Touchette, equations 46–47 and 56](https://arxiv.org/pdf/1405.5157). An explicit finite-state perturbation treatment, with the alternative convention `D=Var/(2t)`, appears in [Antal–Krapivsky–Mallick, Appendix A](https://arxiv.org/pdf/0705.2594).

## 2. Poisson corrector, covariance, and two validation formulas

For each observable solve

\[
Lh_a=\mu_a1-b_a,\qquad \pi h_a=0.
\]

The corrected process

\[
M_a(t)=A_t-\mu_at+h_a(X_t)-h_a(X_0)
\]

is a martingale: the drift of its jump part is `b_a+Lh_a=μ_a`. Its predictable bracket gives

\[
\boxed{V_{ab}=\lim_{t\to\infty}\frac{\operatorname{Cov}(A_t,B_t)}t
=\pi\sum_{e:x\to y}q_e
\big(a_e+h_a(y)-h_a(x)\big)
\big(b_e+h_b(y)-h_b(x)\big).}
\]

Stationarity and the Poisson equations simplify this to

\[
\boxed{V_{ab}=\pi c_{ab}+\pi B_a h_b+\pi B_b h_a.}
\]

For one observable, `V=πc_aa+2πB_a h_a`. The first term is the local shot-noise contribution. The second captures temporal correlations; it can be negative. These expressions agree with the Hessian of the principal eigenvalue of the multivariate tilt `exp(Σ θ_a a_e)`.

These identities follow by the martingale and stationarity calculation above; no reversibility is assumed. For general Poisson-equation background for nonreversible finite jump processes see [Khodabandehlou–Maes–Netočný, *On the Poisson equation for nonreversible Markov jump processes*](https://arxiv.org/abs/2310.19219).

For a stationary initial state, define the ordered positive-lag jump covariance density

\[
K_{ab}(s)=\pi B_a e^{sL}(b_b-\mu_b1),\qquad s>0.
\]

The edge insertion `B_a` is essential: an event changes the state before the later observable is evaluated. In general this is **not** the autocovariance of the local drift `b_a(X_t)`. Exact finite-time covariance is

\[
\operatorname{Cov}(A_t,B_t)
=t\,\pi c_{ab}
+\int_0^t(t-s)\big[K_{ab}(s)+K_{ba}(s)\big]ds.
\]

For `a=b` this has the usual factor `2`. Integrating the semigroup yields the corrector and recovers the variance formula. Thus there are three independent computational checks: the Poisson solve, the squared corrected increments, and eigenvalue curvature (with finite-difference convergence checked).

The fixed-size long-time limit is a finite-state central-limit regime. Inferring a large-`N` exponent from a short sequence of finite-state results requires separate evidence.

## 3. Exact mean and current-noise benchmarks

Write `J_N=(N+2)/(4N+2)` for the current through one bond. Stationary tree jump rate is `Λ_N=(N+1)J_N`. Multiplying by the proven event-average distance gives the exact physical-time cost drift

\[
\boxed{\mu_D=N-1+\frac3{2N+1}.}
\]

Let `Q_i(t)` count jumps across bond `i`, with injection `i=0` and extraction `i=N`. Particle conservation gives

\[
Q_i(t)=Q_0(t)-\Delta\sum_{j=1}^i\eta_j,
\qquad
K(t)=\sum_{i=0}^NQ_i(t)
=(N+1)Q_0(t)-\Delta\sum_{j=1}^N(N-j+1)\eta_j.
\]

The differences are bounded for fixed `N`. Hence all bond currents share one asymptotic variance rate `V_Q`, and `V_K=(N+1)^2V_Q`.

A useful closed benchmark follows from [Antal–Krapivsky–Mallick, equation 32 and the open-TASEP mapping in §III.A.2](https://arxiv.org/pdf/0705.2594). Their spider has `L=N+1` legs; its boundary displacement is a TASEP boundary current. They use half the variance rate. Thus, in the convention of this note,

\[
\boxed{V_Q(N)=\frac32
\frac{(4N+1)!\,[N!(N+2)!]^2}{[(2N+1)!]^3(2N+3)!},
\qquad
V_Q(N)\sim\frac{3\sqrt{2\pi}}{64}\,N^{-1/2}.}
\]

For `N=1,…,7` this is `1/4`, `18/125`, `143/1372`, `221/2646`, `2261/31944`, `148580/2392533`, `114057/2044900`. The original current-fluctuation calculation is [Derrida–Evans–Mallick, 1995, DOI 10.1007/BF02181206](https://doi.org/10.1007/BF02181206); its full original PDF was not accessible during this audit, so the explicit formula above was checked in the later primary mapping paper. This result concerns ordinary particle current, not rotation-cost noise.

## 4. Distance is not merely a particle current plus a bounded potential

An edge identity `d_e=c q_e+F(y)−F(x)` would imply equal ratios of total distance to total current around every directed cycle. Conversely such identities can be checked by a spanning-tree potential and exact rational consistency equations on the remaining edges.

For `N=1` and `N=2`, exact checks find `d=2·injection+ΔF` and `d=4·injection+ΔF`, respectively. In particular,

```text
N=1: V_D=1.
N=2: V_D=288/125, V_K=162/125, V_DK=216/125.
```

At `N=2`, the shot baseline is `12/5`, while the full variance rate is `288/125`; the correlation correction is `−12/125`.

Already `N=3` gives an exact counterexample. To make it reproducible, use `trees(0,5)` ordering from `tasep_tamari.py`. The directed cycle `0→1→2→5→0` has distances `(1,2,2,1)`, sum `6`; the directed cycle `2→5→6→3→2` has `(2,1,2,2)`, sum `7`. Each has one injection, one extraction, and one hop across each of the two bulk bonds. The trees involved are

```text
0 = (0,(1,(2,(3,4))))       canopy111
1 = (0,(1,((2,3),4)))       canopy110
2 = (0,((1,2),(3,4)))       canopy101
3 = (0,((1,(2,3)),4))       canopy110
5 = ((0,1),(2,(3,4)))       canopy011
6 = ((0,1),((2,3),4))       canopy010.
```

The bounded potential cancels around cycles. Therefore this witness proves failure of any fixed linear combination of bond/event-type counts plus a potential for `N=3`. Exact consistency checks also fail for `N=4,…,7`. The nonnegative-remainder argument below strengthens this to **every `N≥3`**; it still does not exclude more complicated canopy observables.

There is nevertheless a useful exact decomposition with a nonnegative geometric remainder. Set `r_e=d_e−2` on bulk hops and `r_e=d_e−1` on boundary events. The distance theorem implies `r_e≥0`. If `R_t=Σr_e` and `W(η)=Σ_{j=1}^N[2(N−j)+1]η_j`, conservation gives

\[
D_t=2NQ_0(t)+R_t-\Delta W,
\qquad
\mu_R=\mu_D-2NJ_N=\frac{(N-1)(N-2)}{2N+1}.
\]

For `N=1,2` the remainder is identically zero. For large `N` its mean rate is asymptotic to `N/2`, the same order as the baseline `2NJ_N`; it cannot be dropped on mean-scale grounds. Its own fluctuations and covariance with current remain dynamical quantities. Given a computed covariance matrix for distance and injection, its variance rate follows algebraically as `V_R=V_D+(2N)²V_Q−4N V_DQ`.

**All-size obstruction.** The right-comb cycle described in §5 has marks `(1,2,…,2,1)`, total distance `2N`, and exactly one injection. Thus an identity `d_e=c·injection_e+ΔF_e` would force `c=2N`. For `N≥3`, the strictly positive mean `μ_R` implies some positive-remainder edge. Irreducibility (§5) places that edge on a directed cycle. Every remainder is nonnegative, so this cycle has strictly positive total remainder, contradicting the forced coefficient `c=2N`. Each bond counter has the same value on every closed trajectory by conservation, so the same argument rules out every fixed linear combination of bond counters plus a potential.

**Strict noise beyond ordinary current.** The squared-increment expression in §2 proves that a finite irreducible CTMC jump observable has zero asymptotic variance only if its increment is a state potential difference: zero variance forces every corrected edge increment to vanish. Conversely a potential telescopes and has zero variance rate. Therefore the obstruction implies

\[
\boxed{V_{DD}-\frac{V_{DQ}^2}{V_{QQ}}>0\qquad(N\ge3).}
\]

This is the variance rate remaining after the best linear subtraction of particle current; equivalently the distance/current covariance matrix has strictly positive determinant. The result proves that particle current cannot account for all cost noise, but does not give a closed expression or large-size exponent for the remainder.

## 5. Irreducibility and the event-index phase

The unit-rate tree chain is irreducible for every `N≥1`. Indeed every canopy can be emptied by suppressing injection, moving particles right, and extracting them. The exact lift supplies such a path from every tree to the unique all-zero-canopy tree. Cao's marked-event bijection gives a strictly positive uniform stationary measure, so the finite chain has no transient states. Every state reaching the same tree therefore forces a single communicating class.

For the embedded jump chain, the phase

\[
\Phi(\eta)=\sum_{i=1}^N i\eta_i\pmod{N+1}
\]

advances by `+1` at every event: injection changes it by `1`, bulk motion by `1`, extraction by `−N`. Thus all directed cycle lengths are multiples of `N+1`. The all-right-comb tree has a cycle of length `N+1`: extract once, move the resulting hole all the way left, and inject. Its tree shape returns to the starting right comb. This gives period **exactly `N+1`**, not merely a lower bound. The explicit cycle was also checked for `N=1,…,9`.

For an explicit all-size description, let `R(i,…,j)` be a right comb on consecutive leaves, allowing one leaf. For `1≤h≤N`, let `T_h` be the tree with right-spine prefix leaves `0,…,h−2` followed by subtree `((h−1,h),R(h+1,…,N+1))`; the prefix is empty for `h=1`. Cao's rule gives `R(0,…,N+1)→T_N→T_{N−1}→…→T_1→R(0,…,N+1)`. The first and last steps have distance one, while each `T_h→T_{h−1}` has distance two by the geodesic formula. This also verifies the zero-excess cycle used in §4.

This periodicity does not obstruct physical-time relaxation of a finite irreducible CTMC. It does mean raw correlations indexed by event number may retain oscillations and should not be assumed to decay.

## 6. Embedded-chain noise and removal of phase oscillations

Let `P` be the embedded transition matrix. Its stationary measure is `ν_x=π_x r(x)/Λ`; with unit event rates it gives the uniform distribution over tree/cherry pairs when an edge is sampled. Let `m=E_ν[d]`, center edge marks `g_e=d_e−m`, and define

\[
(B_gf)(x)=\sum_{e:x\to y}p_e g_e f(y),\quad b=B_g1,
\qquad (I-P)h=b,\quad\nu h=0.
\]

Then the variance per event of the centered accumulated marks is

\[
\boxed{v=\nu\sum p_e(g_e+h(y)-h(x))^2
=\nu\sum p_e g_e^2+2\nu B_gh.}
\]

The discrete corrector equation remains valid for a periodic irreducible chain. The raw lag formula is `K(ℓ)=νB_g P^{ℓ−1}b` for `ℓ≥1`, but its infinite ordinary sum need not converge; the Poisson formula corresponds to the appropriate Abel/Cesàro treatment. At `N=2`, phase marks follow the deterministic repeating pattern `(1,2,1)` up to a phase shift, so the asymptotic centered-mark variance is zero despite positive instantaneous mark variance `2/9`.

For every `N≥3`, the centered event-mark variance is strictly positive. Otherwise `d−m` would be an embedded-chain potential difference by the same squared-increment argument, so every cycle would have mean distance `m`. The right-comb cycle has mean `2N/(N+1)`, whereas the proven stationary event mean differs from it by `2(N−1)(N−2)/[(N+1)(N+2)]>0`.

For interpretable decaying correlations, let `m_k=E[d | source phase k]`. Stationarity gives equal mass to all phase classes, so the mean of `m_k` over the `N+1` phases is `m`. Choose a cyclic potential `F` with `F(k+1)−F(k)=m_k−m`. Replacing `d−m` with `d−m_k` changes accumulated marks only by this bounded phase potential and therefore leaves their asymptotic variance unchanged. The residual local drift has zero conditional mean in every phase, removing all peripheral roots-of-unity modes. Its finite-chain correlations decay.

Physical-time variance rate, event-index centered-mark variance, and instantaneous event-mark variance are three different quantities. The previously proved limiting mark variance `6` alone determines none of the temporal-noise quantities.
