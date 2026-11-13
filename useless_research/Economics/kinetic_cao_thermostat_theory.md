# Variance-matched Cao thermostat: independent theory audit

2026-11-11. This note derives exact benchmarks for a zero-drift, full-relaxation (`tau=1`) extension of [kinetic_options_v2.py](kinetic_options_v2.py). The implementation adds shared equilibrium weights and temporal-bath support to the engine, while retaining its static pricing benchmark. The thermostat is an external stationary process, independent of the fresh velocity randomness conditional on its entire history.

## 1. Kernel, positivity, and the meaning of zero drift

Use velocities `c=(0,+1,−1,+2,−2)` and the v2 equilibrium at explicitly zero lattice drift:

\[
p_\theta(c)=W_c\left[1+\tfrac12(\theta-1)(c^2-1)\right],
\quad W=(1/2,1/6,1/6,1/12,1/12).
\]

Equivalently,

\[
p_\theta(0)=\frac{3-\theta}{4},\quad
p_\theta(\pm1)=\frac16,\quad
p_\theta(\pm2)=\frac{3\theta-1}{24}.
\]

Thus positivity requires `1/3≤theta≤3`; clipping negative populations is not a valid substitute. Direct finite sums give

\[
E[c\mid\theta]=0,\qquad E[c^2\mid\theta]=\theta,
\qquad E[c^4\mid\theta]=4\theta-1.
\]

The fourth moment is **not** `3 theta²`. This discrete kinetic kernel agrees with Gaussian second and fourth moments at `theta=1`, but its temperature deformation does not remain a Gaussian family.

In the existing pricing method, setting `r=0` does **not** set lattice drift to zero: it leaves the `−sigma²*m/2` log drift. The controlled innovation experiment must explicitly use `u=0`. A common constant `r` cannot cancel the temperature-dependent drift at every temperature. The experiment therefore tests centered innovations, not risk-neutral log-price dynamics or option prices.

At `tau=1` collisions reset the velocity distribution at each step. Given the external temperature history, the successive velocity draws are independent. This is what isolates thermostat memory from velocity persistence.

## 2. Identical one-step distributions and return variance

Assume `E theta_t=1`. Since every equilibrium probability is affine in `theta`, integrating over any stationary temperature law gives **exactly** `P(c)=W`. Consequently constant, correlated, and independent/shuffled thermostats have the same one-step velocity distribution, not merely the same variance:

\[
Ec=0,\quad Ec^2=1,\quad Ec^4=3,\quad\operatorname{Var}(c^2)=2.
\]

The one-step excess kurtosis is zero, although the distribution has five atoms and is not Gaussian. At distinct times `Ec_i c_j=0` by conditional centering, even when the temperatures are correlated. Thus for `R_H=Σ_{j=1}^H c_j`,

\[
\operatorname{Var}(R_H)=H
\]

in every control. Multiplication by the common v2 scale `dx=sigma sqrt(dt)` gives variance `H sigma² dt` without changing kurtosis or squared-return correlations.

## 3. Exact aggregate kurtosis: only nonzero-lag temperature covariance survives

Write `C_theta(ell)=Cov(theta_0,theta_ell)`. Conditional independence and symmetry imply

\[
E[R_H^4]
=\sum_iE[c_i^4]+6\sum_{i<j}E[c_i^2c_j^2]
=3H^2+6\sum_{\ell=1}^{H-1}(H-\ell)C_\theta(\ell).
\]

Therefore the exact excess kurtosis is

\[
\boxed{\kappa_H=\frac6{H^2}
\sum_{\ell=1}^{H-1}(H-\ell)C_\theta(\ell).}
\]

In particular:

- Constant `theta=1`: `kappa_H=0` for every horizon.
- Independent temperatures of mean one: the velocity draws are iid with law `W`, so `kappa_H=0` for every horizon, even if temperatures fluctuate strongly.
- A frozen random temperature: `kappa_H=3 Var(theta)(1−1/H)`.
- Correlated temperature: the weighted covariance sum determines the sign and magnitude. Temperature variation alone does not guarantee positive aggregate kurtosis; negative temperature correlations can produce a negative result.

For a path of temperatures define `V=Σtheta_j`. The useful conditional fourth-moment formula is

\[
E[R_H^4\mid\theta_{1:H}]
=3V^2+4V-H-3\sum_j\theta_j^2.
\]

This provides a Rao–Blackwellized validation without noisy velocity draws. A terminal density conditional on **one** global thermostat history is not the full stochastic-volatility ensemble. One must average across thermostat histories, propagate the joint thermostat/position law, or use justified stationary time-window averages. Many tracers sharing one prescribed history only estimate its conditional law.

For a stationary mean `mu` different from one, the general checkpoint is

\[
\kappa_H=
\frac{4\mu-1-3\mu^2}{H\mu^2}
+\frac6{H^2\mu^2}
\sum_{\ell=1}^{H-1}(H-\ell)C_\theta(\ell).
\]

This separates a normalization error from the intended memory effect.

Independent exact-rational enumeration checked all temperature histories and all five-velocity sequences for a two-state thermostat with temperatures `(1/2,3/2)` and probability `3/4` of retaining its state. Its covariance is `(1/4)(1/2)^ell`. Horizons `H=1,2,3` give variance `1,2,3` and excess kurtosis `0,3/16,5/24`, respectively, exactly matching the formula. This check is independent of the Cao generator and its joint-moment implementation.

## 4. Exact squared-return correlations

For any positive lag,

\[
E[c_0^2c_\ell^2]=E[\theta_0\theta_\ell],
\qquad
\boxed{\operatorname{Cov}(c_0^2,c_\ell^2)=C_\theta(\ell),
\quad\rho_{c^2}(\ell)=\frac{C_\theta(\ell)}2.}
\]

The last denominator is exactly `Var(c²)=2`, not `Var(theta)`. The identity is for individual step returns and positive lags; lag zero includes the conditional sampling noise. Aggregated or overlapping-window squared returns require different formulas.

The familiar distinction between uncorrelated centered returns and correlated squared returns predates this experiment; see [Engle's original ARCH paper](https://www.dpye.iimas.unam.mx/ramses/Engle1982.pdf). The present thermostat is an exogenous latent Markov process, not an ARCH feedback model. These exact D1Q5 formulas are derived above, not attributed to Engle.

## 5. Stationary Cao sampling and an exact semigroup benchmark

Let `X_t` be the physical-time Cao chain with row generator `L`, uniform stationary tree measure `pi`, and chosen bounded state observable `g`, centered by its **time-stationary** mean. Choose an affine temperature `theta(x)=1+a g(x)` whose entire range lies in `[1/3,3]`. For samples spaced by fixed physical time `Delta`,

\[
P=e^{\Delta L},\qquad
C_\theta(\ell)=a^2\pi\operatorname{diag}(g)P^\ell g.
\]

This gives a finite-state exact benchmark for both kurtosis and squared-return memory. Initialize from uniform trees to obtain stationarity immediately. A stationary record sampled at jump times instead has measure proportional to the escape rate, and also inherits the embedded chain's cyclic phase; it is a different experiment. A Gillespie simulation must record states at fixed clock times, including holding intervals.

The observable defining the thermostat must be named precisely:

- `g=#cherries−mean` measures escape activity. Cherry count equals the number of active canopy bonds, so this thermostat can already be described entirely within ordinary TASEP.
- `g=Σ_cherries distance−mean` measures local geometric-cost rate and can distinguish trees sharing the same canopy. It tests more of the geometric information established in the preceding experiments.
- `g=Σ_cherries(distance−baseline)−mean`, with baseline `2` for bulk and `1` for boundary events, measures geometric-excess activity. This is the activity selected for the comparison described below; it isolates the nonnegative excess established by the geodesic theorem.

These choices are legitimate bounded external thermostats, with different covariances. They should not be silently substituted for one another.

The implemented comparison was specified as `N=5` (132 trees), geometric-excess activity `a(T)` with uniform mean `12/11` and range `[0,5]`, and

\[
\theta(T)=1+\frac{88}{215}\left(a(T)-\frac{12}{11}\right).
\]

This has exact stationary mean one and range `[119/215,13/5]`, safely within the realizability interval. The physical generator is slowed to `0.05 L` per lattice step, so the benchmark sample matrix is `exp(0.05 L)`. Independent uniform initial trees per batch give exact stationarity without a burn-in approximation. The planned 16 records of length 262144 use separate thermostat/velocity randomness, common fresh velocity uniforms across the three controls, and a within-record temperature permutation for the shuffled control. Those common uniforms couple estimators but do not alter any control's law. These are design specifications, not a report that the main numerical run has passed validation.

If the finite-state sampled chain mixes and its covariance is summable, then `kappa_H` eventually falls as `1/H`, with coefficient `6 Σ_{ell≥1}C_theta(ell)` when that sum is nonzero. At finite horizons it can rise first, before the averaging regime. No persistent infinite-horizon excess or power-law tail follows from this construction. At each finite horizon the lattice return also has bounded support `[-2H,2H]`.

## 6. Controls, shuffling, and interpretation limits

The clean mathematical controls are constant temperature and fresh independent draws from the same stationary temperature marginal. The latter destroys memory while preserving the entire one-step law and temperature histogram.

Uniformly permuting a finite fixed record of length `M` is sampling without replacement. **Conditional on that record**, two distinct shuffled positions have covariance `−s_theta²/(M−1)`, where `s_theta²` is its population variance (divisor `M`) and the covariance is centered at its empirical mean. If that empirical mean is exactly one, the conditional permutation-averaged benchmark is

\[
\kappa_H^{\rm perm}
=-\frac{3s_\theta^2(H-1)}{H(M-1)},\qquad H\le M.
\]

For a general empirical mean `mu_bar`, its conditional kurtosis also contains the non-unit-mean correction from §3:

\[
\kappa_H^{\rm perm\mid record}
=\frac{4\bar\mu-1-3\bar\mu^2}{H\bar\mu^2}
-\frac{3s_\theta^2(H-1)}{H\bar\mu^2(M-1)}.
\]

This conditional negative-covariance statement must not be confused with the **unconditional** shuffled ensemble. The stationary original records have a random sample mean. Relative to the population mean one, two distinct permuted positions instead have common covariance

\[
C_{\rm perm}
=\frac{M\operatorname{Var}(\bar\theta)-C_\theta(0)}{M-1}
=\frac{2}{M(M-1)}\sum_{\ell=1}^{M-1}(M-\ell)C_\theta(\ell).
\]

For a persistent positively correlated bath this is positive, not negative: shuffling destroys temporal ordering but retains a small shared random record-mean component. Its unconditional kurtosis is `3(H−1) C_perm/H`. A valid bound is

\[
|C_{\rm perm}|\le\frac2{M-1}\sum_{\ell=1}^{M-1}|C_\theta(\ell)|,
\quad
|\kappa_H^{\rm perm}|\le
\frac{6(H-1)}{H(M-1)}\sum_{\ell=1}^{M-1}|C_\theta(\ell)|.
\]

Thus the unconditional artifact is of order the covariance sum divided by record length; the variance-only conditional bound is insufficient. Both effects vanish for long records with summable bath covariance, but a single realized permutation also has sampling fluctuations. Fresh iid draws from the stationary marginal give the clean exact analytic no-memory control. The actual within-record permutation remains a useful empirical control with its finite-record qualification. Overlapping windows are not independent replications when assigning uncertainty intervals.

Slow random temperature as a statistical-mechanics construction is established in [Beck–Cohen, *Superstatistics*](https://arxiv.org/abs/cond-mat/0205097). Their general fluctuating-environment framework is context, not a derivation of the affine D1Q5 fourth moment.

What this comparison can establish is a controlled mathematical mechanism: a stationary external temperature field transfers its memory to squared returns and finite-horizon kurtosis while holding variance and one-step law fixed. It does not show that the thermostat is endogenous to price moves, prove a market mechanism, calibrate financial data, test risk-neutrality, or produce an audited option-pricing comparison.
