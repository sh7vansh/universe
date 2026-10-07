"""Exact checks for the structural laws in new_frontiers/experiments/proposed_universe/README.md.

The base theory is a discrete unitary walk with a located-graph parity phase.
The Cartan source field is a SEPARATE static extension, not its derived dynamics.
Run: python3 -m new_frontiers.experiments.proposed_universe.run --output PATH
Standard library only; all reported probabilities and field values are rational.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from .._shared.k4_graph import EDGES, mass
from .._shared.exact import times, plus, conjugate
from ..mobile_defects.run import CLOSING, OPEN, initial_state, evolve, snapshot


COIN = (((1, 1), (1, -1)), ((1, -1), (1, 1)))
VELOCITY = (1, -1)


def mask(edges):
    return sum(1 << EDGES.index(edge) for edge in edges)


def single_step(state, structural_mass, inverse=False):
    """Integer amplitude numerators; denominator doubles at each step."""
    result = {}
    phase = (-1)**structural_mass
    for (x, direction), value in state.items():
        if inverse:
            x -= VELOCITY[direction]
        for out in range(2):
            coefficient = conjugate(COIN[direction][out]) if inverse else COIN[out][direction]
            key = (x if inverse else x + VELOCITY[out], out)
            contribution = times(coefficient, tuple(phase * z for z in value))
            result[key] = plus(result.get(key, (0, 0)), contribution)
    return {key: value for key, value in result.items() if value != (0, 0)}


def single_mass_checks(steps):
    examples = [("tree", mask(((0, 1), (1, 2)))),
                ("triangle", mask(((0, 1), (1, 2), (0, 2)))),
                ("two_cycles", mask(((0, 1), (0, 2), (0, 3), (1, 2), (1, 3)))),
                ("complete_K4", (1 << len(EDGES)) - 1)]
    assert [mass(s) for _, s in examples] == [0, 1, 2, 3]
    states = [{(0, 0): (1, 0)} for _ in examples]
    for t in range(steps + 1):
        for (_, subset), state in zip(examples, states):
            assert sum(a*a + b*b for a, b in state.values()) == 4**t
            phase = (-1)**(mass(subset) * t)
            assert state == {key: tuple(phase * z for z in v) for key, v in states[0].items()}
            assert all(abs(x) <= t for x, _ in state)
        if t < steps:
            states = [single_step(state, mass(subset))
                      for (_, subset), state in zip(examples, states)]
    rows = []
    for (name, subset), state in zip(examples, states):
        mean = sum(x * (a*a + b*b) for (x, _), (a, b) in state.items())
        second = sum(x*x * (a*a + b*b) for (x, _), (a, b) in state.items())
        rows.append({"object": name, "structural_mass": mass(subset), "step": steps,
                     "mean_position": str(F(mean, 4**steps)),
                     "second_moment": str(F(second, 4**steps)),
                     "same_position_probabilities_as_tree": True})
        for _ in range(steps):
            state = single_step(state, mass(subset), inverse=True)
        assert state == {(0, 0): (4**steps, 0)}
    return rows


def clock_step(state, count, inverse=False):
    """Separate clock extension, count>0. Common denominator doubles per tick.

    Ordinary clock advances have numerator factor 2 and no spatial move.
    At wraparound apply the base single-object travel operator.
    """
    result = {}
    for (x, direction, clock), value in state.items():
        wrap = clock == (0 if inverse else count-1)
        out_clock = (clock + (-1 if inverse else 1)) % count
        if not wrap:
            result[(x, direction, out_clock)] = tuple(2*z for z in value)
            continue
        if inverse:
            x -= VELOCITY[direction]
        for out in range(2):
            coefficient = conjugate(COIN[direction][out]) if inverse else COIN[out][direction]
            key = x if inverse else x + VELOCITY[out], out, out_clock
            result[key] = plus(result.get(key, (0, 0)), times(coefficient, value))
    return {key: value for key, value in result.items() if value != (0, 0)}


def clock_checks(steps):
    records = []
    for count in (1, 2, 3, 4):
        initial = state = {(0, 0, 0): (1, 0)}
        free = {(0, 0): (1, 0)}
        for t in range(steps + 1):
            if t and t % count == 0:
                free = single_step(free, 0)
            moves = t // count
            factor = 2**(t-moves)
            assert state == {(x, d, t % count): tuple(factor*z for z in value)
                             for (x, d), value in free.items()}
            assert sum(a*a+b*b for a, b in state.values()) == 4**t
            if t < steps:
                state = clock_step(state, count)
        for _ in range(steps):
            state = clock_step(state, count, inverse=True)
        assert state == {(0, 0, 0): (4**steps, 0)}

        # Test the operator identity on arbitrary clock-channel superpositions.
        probe = {(q-1, q % 2, q): (q+1, 1-q) for q in range(count)}
        actual = probe
        for _ in range(count):
            actual = clock_step(actual, count)
        expected = {}
        for q in range(count):
            sector = {(x, d): v for (x, d, clock), v in probe.items() if clock == q}
            for (x, d), v in single_step(sector, 0).items():
                expected[(x, d, q)] = tuple(2**(count-1)*z for z in v)
        assert actual == expected
        records.append({"internal_clock_channels": count,
                        "structural_mass": count, "curvature_mass": str(count),
                        "source_charge_times_curvature": "1",
                        "acceleration_per_weak_coupling_in_same_background": "-1/2"})
    return {"status": "additional clock-length axiom; stable fixed-count sectors only",
            "identity": "W_M^M = U_0 on each clock channel",
            "records": records,
            "qualification": "M=0, variable-count collisions, relativistic mass, and dynamical fields are not supplied by this clock rule."}


def pair_checks():
    records = []
    for separation in (1, 2, 4, 6):
        free = interacting = initial_state(separation)
        # Initial physical distance is 2*separation. At time separation,
        # contact can first occur; D acts on that amplitude at the next step.
        for t in range(separation + 1):
            assert free == interacting
            if t < separation:
                free = evolve(free, OPEN)
                interacting = evolve(interacting, CLOSING)
        free, interacting = evolve(free, OPEN), evolve(interacting, CLOSING)
        assert free != interacting
        for state in (free, interacting):
            assert sum(a*a + b*b for a, b in state.values()) == 2 * 4**(separation + 1)
        records.append({"initial_distance": 2 * separation,
                        "states_equal_through_step": separation,
                        "first_different_step": separation + 1})
    state = initial_state(0)
    before = snapshot(state, 0, CLOSING)["expected_defect"]
    state = evolve(state, CLOSING)
    after = snapshot(state, 1, CLOSING)["expected_defect"]
    assert (before, after) == ("1", "0")
    return {"no_interaction_before_contact": records,
            "structural_mass_not_conserved": {"before_one_step": before, "after_one_step": after},
            "bound_mode_expected_defect": "1/3",
            "bound_mode_certificate": "new_frontiers/experiments/mobile_defects/certificate.py"}


def cartan(length):
    return [[F(2 if i == j else -1 if abs(i-j) == 1 else 0)
             for j in range(length)] for i in range(length)]


def green(length):
    # Interior sites are 1,...,length; boundaries at 0,length+1.
    return [[F(min(i, j) * (length + 1 - max(i, j)), length + 1)
             for j in range(1, length + 1)] for i in range(1, length + 1)]


def matvec(matrix, vector):
    return [sum(a*b for a, b in zip(row, vector)) for row in matrix]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def field_energy(matrix, rho, phi):
    return dot(phi, matvec(matrix, phi))/2 - dot(rho, phi)


def static_field_checks():
    for length in range(1, 17):
        c, g = cartan(length), green(length)
        for j in range(length):
            assert matvec(c, [row[j] for row in g]) == [F(i == j) for i in range(length)]
        rho = [F((3*i + 1) % 4) for i in range(length)]
        phi = matvec(g, rho)
        perturbation = [F((-1)**i * (i + 1), 7) for i in range(length)]
        shifted = [x+y for x, y in zip(phi, perturbation)]
        difference = field_energy(c, rho, shifted) - field_energy(c, rho, phi)
        expected = dot(perturbation, matvec(c, perturbation))/2
        assert difference == expected > 0
        assert field_energy(c, rho, phi) == -dot(rho, phi)/2

    length, source_site, source_charge = 11, 6, F(1)
    g = green(length)
    rows = []
    for probe_charge in (F(1), F(2)):
        potential = [-source_charge * probe_charge * value for value in g[source_site-1]]
        for site in range(1, length + 1):
            if site < source_site:
                assert potential[site] < potential[site-1]
            elif site > source_site:
                assert potential[site-2] < potential[site-1]
        rows.append({"probe_structural_mass": str(probe_charge),
                     "cross_potential_by_site": [str(x) for x in potential],
                     "right_side_force_per_weak_coupling": str(-source_charge * probe_charge * F(source_site, length+1)),
                     "curvature_mass": "1",
                     "right_side_acceleration_per_weak_coupling": str(-source_charge * probe_charge * F(source_site, length+1))})
    assert rows[0]["right_side_acceleration_per_weak_coupling"] == "-1/2"
    assert rows[1]["right_side_acceleration_per_weak_coupling"] == "-1"
    return {"status": "additional static field axiom; not base-walk gravity",
            "inverse_sizes_checked": list(range(1, 17)),
            "green_formula": "min(i,j)*(L+1-max(i,j))/(L+1)",
            "source_site": source_site, "interior_sites": length,
            "toward_source_cross_potential": rows,
            "equivalence_condition": "probe charge times probe quasienergy curvature must be species-independent",
            "equivalence_condition_satisfied_by_defect_charge": False,
            "qualification": "Force and acceleration entries are leading weak-coupling diagnostics, not simulated coupled-field evolution."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=12)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 1 <= args.steps <= 64:
        parser.error("--steps must be between 1 and 64")
    results = {"single_objects": single_mass_checks(args.steps), "pair_checks": pair_checks(),
               "clock_extension": clock_checks(args.steps),
               "dispersion": {"free_cos_omega": "cos(k)/sqrt(2)",
                              "free_curvature_mass_all_structural_masses": "1",
                              "bound_curvature_mass": "2*sqrt(2)",
                              "certificate": "new_frontiers/experiments/proposed_universe/certificate.py"},
               "static_extension": static_field_checks()}
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    print("Exact phase-only mass, clock, reversal, causal contact, nonconservation, and static Cartan field checks passed.")


if __name__ == "__main__":
    main()
