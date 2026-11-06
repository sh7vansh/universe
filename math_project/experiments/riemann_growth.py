"""Check arithmetic-growth and Cartan spectral bridges; no RH assumptions.

Run from any directory: python3 /path/to/riemann_growth.py
Requires the already installed numpy and mpmath. Writes only its own JSON report.
"""

from fractions import Fraction
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def factor(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def divisors(n):
    result = [1]
    for p, exponent in factor(n).items():
        result = [d * p**k for d in result for k in range(exponent + 1)]
    return sorted(result)


def least_missing(state, bound):
    return next((q for q in range(2, bound + 1) if state % q), None)


def arithmetic_checks(bound=1000):
    # Algorithm uses all integers; prime factorization is only an independent check.
    state = 1
    events = []
    while (q := least_missing(state, bound)) is not None:
        previous = state
        state = math.lcm(state, q)
        factors = factor(q)
        assert len(factors) == 1
        p, exponent = next(iter(factors.items()))
        assert state // previous == p
        events.append((q, p, exponent, state))

    expected = [n for n in range(2, bound + 1) if len(factor(n)) == 1]
    assert [event[0] for event in events] == expected
    event_states = {q: d for q, _, _, d in events}
    threshold_state = 1
    event_state = 1
    valuations = {}
    max_log_error = 0.0
    for n in range(1, bound + 1):
        previous = threshold_state
        threshold_state = math.lcm(threshold_state, n)
        if n in event_states:
            event_state = event_states[n]
        assert threshold_state == event_state
        factors = factor(n)
        if len(factors) == 1:
            p, exponent = next(iter(factors.items()))
            valuations[p] = exponent
            assert threshold_state // previous == p
        else:
            assert threshold_state == previous
        assert threshold_state == math.prod(p**k for p, k in valuations.items())
        psi = math.fsum(k * math.log(p) for p, k in valuations.items())
        max_log_error = max(max_log_error, abs(math.log(threshold_state) - psi))
    assert max_log_error < 1e-10
    return {
        "thresholds_checked": bound,
        "event_count": len(events),
        "first_events": [
            {"generator": q, "prime_multiplier": p, "state": d}
            for q, p, _, d in events[:12]
        ],
        "maximum_log_lcm_minus_psi_error": max_log_error,
    }


def finite_lattice_checks(bound=10):
    top = math.lcm(*range(1, bound + 1))
    states = divisors(top)
    index = {d: i for i, d in enumerate(states)}
    operator = np.zeros((len(states), len(states)), dtype=np.int64)
    for d in states:
        contained = [m for m in range(1, bound + 1) if d % m == 0]
        assert math.lcm(*contained) == d  # Join density, not only the chosen orbit.
        q = least_missing(d, bound)
        successor = d if q is None else math.lcm(d, q)
        if q is not None:
            assert len(factor(q)) == 1
            p = next(iter(factor(q)))
            assert successor // d == p
        operator[index[d], index[successor]] = 1
        for other in states:
            assert d * other == math.gcd(d, other) * math.lcm(d, other)

    depth = sum(factor(top).values())
    projection = np.zeros_like(operator)
    projection[:, index[top]] = 1
    assert np.array_equal(np.linalg.matrix_power(operator, depth), projection)
    assert not np.array_equal(np.linalg.matrix_power(operator, depth - 1), projection)
    transient = operator - projection
    assert np.count_nonzero(np.linalg.matrix_power(transient, depth)) == 0
    assert np.array_equal(np.diag(operator), [int(d == top) for d in states])
    return {
        "bound": bound,
        "top": top,
        "states": len(states),
        "join_density_states_checked": len(states),
        "modular_identity_pairs_checked": len(states) ** 2,
        "uniform_completion_depth": depth,
        "koopman_eigenvalues_exact_from_triangular_diagonal": {
            "zero_multiplicity": len(states) - 1,
            "one_multiplicity": 1,
        },
    }


def centered_energy_checks(bound=100):
    current = 1
    psi = [0.0]
    increments = []
    for n in range(1, bound + 1):
        successor = math.lcm(current, n)
        increments.append(math.log(successor // current))
        psi.append(math.log(successor))
        current = successor
    slope = psi[-1] / bound
    v = np.array([psi[j] - j * slope for j in range(1, bound)])
    cartan = 2 * np.eye(bound - 1) - np.eye(bound - 1, k=1) - np.eye(bound - 1, k=-1)
    energy = float(v @ cartan @ v)
    increment_energy = math.fsum((a - slope) ** 2 for a in increments)
    variance_formula = math.fsum(a * a for a in increments) - psi[-1] ** 2 / bound
    assert abs(energy - increment_energy) < 1e-9
    assert abs(energy - variance_formula) < 1e-9
    return {
        "threshold": bound,
        "cartan_rank": bound - 1,
        "energy": energy,
        "increment_variance_energy": variance_formula,
        "absolute_error": abs(energy - variance_formula),
    }


def spectral_checks():
    mp.mp.dps = 40
    checks = []
    for rank in [1, 2, 3, 8, 31]:
        matrix = 2 * np.eye(rank) - np.eye(rank, k=1) - np.eye(rank, k=-1)
        j = np.arange(1, rank + 1)[:, None]
        k = np.arange(1, rank + 1)[None, :]
        modes = np.sqrt(2 / (rank + 1)) * np.sin(np.pi * j * k / (rank + 1))
        eigenvalues = 4 * np.sin(np.pi * k.flatten() / (2 * (rank + 1))) ** 2
        error = float(np.max(np.abs(matrix @ modes - modes * eigenvalues)))
        assert error < 1e-12
        assert np.max(np.abs(modes.T @ modes - np.eye(rank))) < 1e-12
        inverse_trace = sum(Fraction(j * (rank + 1 - j), rank + 1) for j in range(1, rank + 1))
        assert inverse_trace == Fraction(rank * (rank + 2), 6)
        checks.append({"rank": rank, "eigenvector_residual": error})

    convergence = []
    for rank in [15, 63, 255, 1023]:
        scaled_eigenvalues = [
            4 * ((rank + 1) / mp.pi) ** 2 * mp.sin(mp.pi * k / (2 * (rank + 1))) ** 2
            for k in range(1, rank + 1)
        ]
        row = {"rank": rank}
        for s in [mp.mpf(1), mp.mpf(2), mp.mpc(1, 1)]:
            value = mp.fsum(mu ** (-s) for mu in scaled_eigenvalues)
            target = mp.zeta(2 * s)
            if s == 1:
                exact = mp.pi**2 / 6 * (1 - mp.mpf(1) / (rank + 1) ** 2)
                assert abs(value - exact) < mp.mpf("1e-30")
            row[str(s)] = {
                "value": str(value),
                "target_zeta_2s": str(target),
                "absolute_error": float(abs(value - target)),
            }
        convergence.append(row)
    for s in [mp.mpf(1), mp.mpf(2), mp.mpc(1, 1)]:
        errors = [row[str(s)]["absolute_error"] for row in convergence]
        assert all(b < a for a, b in zip(errors, errors[1:]))
    return {"mode_checks": checks, "spectral_zeta_convergence": convergence}


def mellin_checks(bound=10000):
    # Compare independently computed arithmetic coefficients with analytic zeta.
    coefficients = []
    for n in range(2, bound + 1):
        factors = factor(n)
        if len(factors) == 1:
            coefficients.append((n, mp.log(next(iter(factors)))))
    rows = []
    for s in [mp.mpf(2), mp.mpc(2, 1)]:
        target = -mp.diff(mp.zeta, s) / mp.zeta(s)
        partial = mp.fsum(weight * mp.power(n, -s) for n, weight in coefficients)
        # Since 0 <= Lambda(n) <= log n, the omitted tail has this integral bound.
        sigma = mp.re(s)
        tail_bound = bound ** (1 - sigma) * (
            mp.log(bound) / (sigma - 1) + 1 / (sigma - 1) ** 2
        )
        assert abs(partial - target) < tail_bound
        rows.append({
            "s": str(s),
            "arithmetic_partial_sum": str(partial),
            "analytic_log_derivative": str(target),
            "absolute_error": float(abs(partial - target)),
            "proved_tail_bound": float(tail_bound),
        })
    return {"bound": bound, "comparisons": rows}


def main():
    report = {
        "arithmetic_growth": arithmetic_checks(),
        "finite_lattice_and_koopman": finite_lattice_checks(),
        "centered_arithmetic_cartan_energy": centered_energy_checks(),
        "cartan_spectrum": spectral_checks(),
        "arithmetic_mellin_transform": mellin_checks(),
        "scope": "Finite arithmetic checks and numerical corroboration; analytic proofs are in riemann_growth.md. No Lean additions or claims about RH.",
    }
    path = Path(__file__).with_name("riemann_growth_results.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"All checks passed. Results: {path}")
    print(json.dumps({
        "growth_events_through_1000": report["arithmetic_growth"]["event_count"],
        "finite_lattice": report["finite_lattice_and_koopman"],
        "centered_energy": report["centered_arithmetic_cartan_energy"],
        "spectral_zeta_at_rank_1023": report["cartan_spectrum"]["spectral_zeta_convergence"][-1],
    }, indent=2))


if __name__ == "__main__":
    main()
