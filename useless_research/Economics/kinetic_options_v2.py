"""
Kinetic (Lattice-Boltzmann) Option Pricing — v2, audited
=========================================================

Physics model
-------------
The log-price x = ln(S/S0) is a tracer particle in a 1D gas. Its velocity
distribution relaxes (BGK) towards a discrete Hermite approximation to a
local Maxwellian with temperature theta(x) and drift u(x). Unlike a fluid,
the price does NOT conserve momentum: collisions
relax velocity towards the prescribed risk-neutral drift, so the macroscopic
limit (Chapman-Enskog) is the Fokker-Planck equation

    d_t rho + d_x(mu rho) = d_x^2 (D rho),   D = theta (tau - 1/2) dx^2/dt

Lattice: D1Q5, c in {0, +-1, +-2}, weights {1/2, 1/6, 1/6, 1/12, 1/12}
(these match Gaussian moments up to 4th order at reference theta=1, c_s^2=1).

Fixes vs v1 (boltzmann_options_engine.py):
  1. vol is actually calibrated: dx is chosen so that D = sigma^2/2
  2. temperature gradient sign is correct (hotter on the downside)
  3. no momentum conservation (v1 was a sound-wave fluid, not diffusion)
  4. absorbing boundaries, mass loss is REPORTED, never renormalised away
  5. no positivity clipping; feq positivity is checked instead

Experiments
-----------
  E1  Validation      : flat theta  -> must reproduce Black-Scholes (flat IV)
  E2  Knudsen sweep   : few collisions before expiry -> non-Gaussian?
  E3  Temp. gradient  : theta(x) hotter on downside -> skew; cross-checked
                        against a Monte-Carlo local-vol SDE (hydrodynamic limit)
  E4  Superstatistics : fluctuating temperature (Beck-Cohen) -> smile, fat tails
"""

import numpy as np
import scipy.stats as st
from scipy.optimize import brentq
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

C = np.array([0.0, 1.0, -1.0, 2.0, -2.0])
W = np.array([1 / 2, 1 / 6, 1 / 6, 1 / 12, 1 / 12])
CI = C.astype(int)


def equilibrium_populations(theta, u=0.0):
    """D1Q5 equilibrium probabilities, shared by density and tracer solvers.

    At u=0, E[c^2]=theta and E[c^4]=4*theta-1. The fourth moment equals
    3*theta^2 only at special temperatures; this finite-velocity Hermite
    equilibrium is not an exact Maxwellian at arbitrary theta.
    """
    theta, u = np.broadcast_arrays(np.asarray(theta, dtype=float), np.asarray(u, dtype=float))
    if not np.all(np.isfinite(theta)) or not np.all(np.isfinite(u)):
        raise ValueError('nonfinite temperature or drift')
    if np.any(theta < 1/3) or np.any(theta > 3):
        raise ValueError(f'theta out of realisable range: [{theta.min():.2f},{theta.max():.2f}]')
    shape = (5,)+(1,)*theta.ndim
    cc, ww = C.reshape(shape), W.reshape(shape)
    populations = ww*(1+cc*u+0.5*((cc*u)**2-u**2)+0.5*(theta-1)*(cc**2-1))
    if np.any(populations < 0):
        raise ValueError('negative equilibrium population; temperature and drift are not jointly realisable')
    return populations


# ---------------------------------------------------------------------------
# Black-Scholes helpers (used only as a ruler: to express prices as implied vol)
# ---------------------------------------------------------------------------
def bs_call(S, K, T, r, s):
    d1 = (np.log(S / K) + (r + 0.5 * s * s) * T) / (s * np.sqrt(T))
    return S * st.norm.cdf(d1) - K * np.exp(-r * T) * st.norm.cdf(d1 - s * np.sqrt(T))


def implied_vol(price, S, K, T, r):
    lo = max(0.0, S - K * np.exp(-r * T))
    if price <= lo + 1e-8 or price >= S:
        return np.nan
    try:
        return brentq(lambda s: bs_call(S, K, T, r, s) - price, 1e-4, 5.0, xtol=1e-10)
    except ValueError:
        return np.nan


# ---------------------------------------------------------------------------
# Kinetic lattice
# ---------------------------------------------------------------------------
class KineticLattice:
    def __init__(self, sigma0, T, r, n_steps, tau=1.0, theta0=1.0, width=10.0):
        self.sigma0, self.T, self.r, self.N = sigma0, T, r, n_steps
        self.tau, self.theta0 = tau, theta0
        self.dt = T / n_steps
        # calibrate:  sigma0^2 / 2 = theta0 (tau - 1/2) dx^2 / dt
        self.dx = np.sqrt(sigma0**2 * self.dt / (2.0 * theta0 * (tau - 0.5)))
        # fastest particle moves 2 nodes/step -> domain of 2N+2 nodes means the
        # walls are causally unreachable: mass loss must be exactly zero
        half = max(int(np.ceil(width * sigma0 * np.sqrt(T) / self.dx)), 2 * n_steps + 2)
        self.x = (np.arange(-half, half + 1)) * self.dx
        self.c0 = half
        # Knudsen number: mean free path / diffusion length
        self.Kn = tau * self.dx / np.sqrt(sigma0**2 * T)

    def evolve(self, m=None, *, temperature_schedule=None):
        """Static multiplier m(x), or N absolute spatially uniform temperatures.

        temperature_schedule adds an exogenous global bath history. One call
        propagates the conditional density for that history; averaging over
        histories is required for the unconditional stochastic-bath density.
        """
        x = self.x
        if temperature_schedule is not None:
            if m is not None:
                raise ValueError('choose a static spatial multiplier or a temporal bath schedule')
            theta = np.asarray(temperature_schedule, dtype=float)
            if theta.shape != (self.N,):
                raise ValueError(f'temperature_schedule must have shape ({self.N},)')
            multiplier = theta/self.theta0
        else:
            multiplier = np.ones_like(x) if m is None else np.asarray(m)
            theta = self.theta0*multiplier
        u = (self.r - 0.5 * self.sigma0**2 * multiplier) * self.dt / self.dx
        feq_shape = equilibrium_populations(theta, u)
        f = np.zeros((5, x.size))
        f[:, self.c0] = W  # delta initial condition: all mass at S0
        if temperature_schedule is None and feq_shape.ndim == 1:
            feq_shape = feq_shape[:, None]
        for step in range(self.N):
            rho = f.sum(0)
            local_equilibrium = feq_shape[:, step, None] if temperature_schedule is not None else feq_shape
            f += (local_equilibrium * rho - f) / self.tau  # BGK collision
            g = np.zeros_like(f)  # streaming, absorbing walls
            for i, c in enumerate(CI):
                if c > 0:
                    g[i, c:] = f[i, :-c]
                elif c < 0:
                    g[i, :c] = f[i, -c:]
                else:
                    g[i] = f[i]
            f = g
        self.rho = f.sum(0)  # probability mass per node
        self.mass = self.rho.sum()
        return self.rho

    def calls(self, S0, strikes):
        S = S0 * np.exp(self.x)
        disc = np.exp(-self.r * self.T)
        return np.array([disc * np.sum(self.rho * np.maximum(S - K, 0)) for K in strikes])

    def forward_error(self, S0):
        S = S0 * np.exp(self.x)
        return np.sum(self.rho * S) / (S0 * np.exp(self.r * self.T)) - 1

    def excess_kurtosis(self):
        p = self.rho / self.rho.sum()
        mu = np.sum(p * self.x)
        v = np.sum(p * (self.x - mu) ** 2)
        return np.sum(p * (self.x - mu) ** 4) / v**2 - 3


def iv_curve(prices, S0, strikes, T, r):
    return np.array([implied_vol(p, S0, K, T, r) for p, K in zip(prices, strikes)])


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    S0, r, sig = 25000.0, 0.06, 0.14
    mny = np.linspace(0.85, 1.15, 31)
    K = S0 * mny
    out = {}

    # ---------------- E1: validation ----------------
    print("=" * 70 + "\nE1  VALIDATION  (flat temperature must give flat 14% IV)\n" + "=" * 70)
    T1 = 0.15
    e1 = {}
    for tau in (0.8, 1.0, 2.0):
        lat = KineticLattice(sig, T1, r, n_steps=600, tau=tau)
        lat.evolve()
        prices = lat.calls(S0, K)
        bs = bs_call(S0, K, T1, r, sig)
        ivs = iv_curve(prices, S0, K, T1, r)
        e1[tau] = ivs
        print(f"tau={tau:3.1f}  mass={lat.mass:.8f}  fwd err={lat.forward_error(S0):+.2e}  "
              f"max|C-BS|=Rs {np.max(np.abs(prices - bs)):.3f}  "
              f"IV range=[{np.nanmin(ivs)*100:.3f}%, {np.nanmax(ivs)*100:.3f}%]")
    out["e1"] = e1

    # ---------------- E2: Knudsen sweep ----------------
    print("\n" + "=" * 70 + "\nE2  KNUDSEN SWEEP  (T = 5 trading days; few collisions -> kinetic regime)\n" + "=" * 70)
    T2 = 5 / 252
    print(f"{'N steps':>8} {'tau':>5} {'Kn':>7} {'excess kurt':>12} {'IV 0.98':>8} {'IV ATM':>8} {'IV 1.02':>8}")
    e2 = []
    for tau in (1.0, 3.0):
        for N in (3, 6, 12, 25, 50, 200, 800):
            lat = KineticLattice(sig, T2, r, n_steps=N, tau=tau)
            lat.evolve()
            kz = lat.excess_kurtosis()
            Ks = S0 * np.array([0.98, 1.0, 1.02])
            ivs = iv_curve(lat.calls(S0, Ks), S0, Ks, T2, r)
            e2.append((tau, N, lat.Kn, kz))
            print(f"{N:8d} {tau:5.1f} {lat.Kn:7.3f} {kz:12.4f} {ivs[0]*100:7.2f}% {ivs[1]*100:7.2f}% {ivs[2]*100:7.2f}%")
    out["e2"] = e2

    # ---------------- E3: temperature gradient ----------------
    print("\n" + "=" * 70 + "\nE3  TEMPERATURE GRADIENT  (hotter on downside)  vs  Monte-Carlo local vol\n" + "=" * 70)
    T3 = 0.15
    a, w = 0.6, 0.05
    mfun = lambda x: 1.0 - a * np.tanh(x / w)  # m in [0.4, 1.6]: x<0 hotter
    lat = KineticLattice(sig, T3, r, n_steps=600, tau=1.0, width=14)
    lat.evolve(mfun(lat.x))
    p_kin = lat.calls(S0, K)
    iv_kin = iv_curve(p_kin, S0, K, T3, r)
    # Monte-Carlo of the hydrodynamic-limit SDE: dX = (r - s(X)^2/2)dt + s(X) dW
    rng = np.random.default_rng(7)
    n_paths, n_mc = 400_000, 600
    X = np.zeros(n_paths)
    dtm = T3 / n_mc
    for _ in range(n_mc):
        s2 = sig**2 * mfun(X)
        X += (r - 0.5 * s2) * dtm + np.sqrt(s2 * dtm) * rng.standard_normal(n_paths)
    ST = S0 * np.exp(X)
    p_mc = np.array([np.exp(-r * T3) * np.mean(np.maximum(ST - k, 0)) for k in K])
    iv_mc = iv_curve(p_mc, S0, K, T3, r)
    print(f"mass={lat.mass:.8f}   fwd err={lat.forward_error(S0):+.2e}")
    print(f"{'K/S0':>6} {'kinetic IV':>11} {'MC IV':>8} {'local vol':>10}")
    for i in range(0, 31, 3):
        print(f"{mny[i]:6.2f} {iv_kin[i]*100:10.2f}% {iv_mc[i]*100:7.2f}% "
              f"{sig*np.sqrt(mfun(np.log(mny[i])))*100:9.2f}%")
    out["e3"] = (iv_kin, iv_mc)

    # ---------------- E4: superstatistics ----------------
    print("\n" + "=" * 70 + "\nE4  SUPERSTATISTICS  (temperature itself fluctuates, Gamma-distributed)\n" + "=" * 70)
    T4 = 0.05
    e4 = {}
    for k_shape in (50.0, 8.0, 3.0):  # large k = nearly fixed temperature
        nodes = np.linspace(0.35, 2.9, 41)
        wts = st.gamma.pdf(nodes, a=k_shape, scale=1 / k_shape)
        wts /= wts.sum()
        prices = np.zeros_like(K)
        rho_mix = None
        for mm, ww in zip(nodes, wts):
            lat = KineticLattice(sig, T4, r, n_steps=400, tau=1.0, width=16)
            lat.evolve(np.full_like(lat.x, mm))
            prices += ww * lat.calls(S0, K)
            rho_mix = ww * lat.rho if rho_mix is None else rho_mix + ww * lat.rho
        lat.rho = rho_mix
        kz = lat.excess_kurtosis()
        ivs = iv_curve(prices, S0, K, T4, r)
        e4[k_shape] = (ivs, kz)
        print(f"Gamma shape k={k_shape:5.1f}  temp CV={1/np.sqrt(k_shape):.2f}  excess kurt={kz:6.3f}  "
              f"IV(0.90)={ivs[6]*100:.2f}%  IV(ATM)={ivs[15]*100:.2f}%  IV(1.10)={ivs[24]*100:.2f}%")
    out["e4"] = e4

    # ---------------- plots ----------------
    fig, ax = plt.subplots(2, 2, figsize=(14, 10))
    a1, a2, a3, a4 = ax.flat
    for tau, ivs in out["e1"].items():
        a1.plot(mny, ivs * 100, marker="o", ms=3, label=f"tau={tau}")
    a1.axhline(14, color="k", ls="--", lw=1, label="input 14%")
    a1.set_ylim(13, 15)
    a1.set_title("E1 Validation: flat temperature -> flat IV (BS recovered)")
    a1.set_xlabel("K/S0"); a1.set_ylabel("IV %"); a1.legend()

    for tau in (1.0, 3.0):
        rows = [e for e in out["e2"] if e[0] == tau]
        a2.semilogx([e[2] for e in rows], [e[3] for e in rows], marker="o", label=f"tau={tau}")
    a2.axhline(0, color="k", lw=1)
    a2.set_title("E2 Knudsen sweep: excess kurtosis of log-return")
    a2.set_xlabel("Knudsen number Kn"); a2.set_ylabel("excess kurtosis"); a2.legend()

    a3.plot(mny, out["e3"][0] * 100, lw=2, label="kinetic lattice")
    a3.plot(mny, out["e3"][1] * 100, "o", ms=4, label="Monte-Carlo local-vol SDE")
    a3.set_title("E3 Temperature gradient -> skew (= local vol in the hydro limit)")
    a3.set_xlabel("K/S0"); a3.set_ylabel("IV %"); a3.legend()

    for k_shape, (ivs, kz) in out["e4"].items():
        a4.plot(mny, ivs * 100, lw=2, label=f"k={k_shape:g}  (excess kurt {kz:.2f})")
    a4.set_title("E4 Superstatistics: fluctuating temperature -> smile")
    a4.set_xlabel("K/S0"); a4.set_ylabel("IV %"); a4.legend()
    for a_ in ax.flat:
        a_.grid(alpha=0.3)
    plt.tight_layout()
    path = "/home/shivansh/Github Repositories/universe/useless_research/Economics/kinetic_v2_experiments.png"
    plt.savefig(path, dpi=150)
    print(f"\nplot -> {path}")
