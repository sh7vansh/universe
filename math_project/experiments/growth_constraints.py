"""Test what completion-triggered arity growth does and does not determine.

The completion record currently tracks explored vertices/edges, not a
condition defined from a field amplitude. Countermodels keep this record
fixed while changing field dynamics or the clock.
"""

from itertools import product
import json
from math import comb

import numpy as np

from k6_physics_equations import cell_matrices
from k6_spin_transport import right_rotations, spans, trees
from physics_catalogue import spectral_evolve


def graph(n):
    vertices = trees(n)
    index = {t: i for i, t in enumerate(vertices)}
    edges = sorted((index[t], index[u]) for t in vertices for u in right_rotations(t))
    adjacency = np.zeros((len(vertices), len(vertices)))
    for s, t in edges:
        adjacency[s, t] = adjacency[t, s] = 1
    degree = np.diag(adjacency.sum(axis=1))
    return vertices, edges, degree - adjacency, degree + adjacency


def completion_order(edges, reverse=False):
    seen = {0}
    pending = list(range(len(edges)))
    if reverse:
        pending.reverse()
    order = []
    while pending:
        next_position = next(i for i, e in enumerate(pending)
                             if seen.intersection(edges[e]))
        edge = pending.pop(next_position)
        seen.update(edges[edge])
        order.append(edge)
    assert seen == set(range(42))
    assert set(order) == set(range(84)) and len(order) == 84
    return order


def catalan(k):
    return comb(2 * k, k) // (k + 1)


def edge_count(n):
    return (n - 2) * catalan(n - 1) // 2


def run():
    vertices, edges, L, H = graph(6)
    _, _, b1, _, _, _ = cell_matrices()
    assert np.array_equal(L, b1 @ b1.T)
    order_a, order_b = completion_order(edges), completion_order(edges, reverse=True)
    assert order_a != order_b
    # Every prefix is incomplete; the last event alone triggers growth.
    assert all(len(set(order_a[:k])) < 84 for k in range(84))
    assert len(set(order_a)) == 84
    durations = {"unit_clock": float(len(order_a)), "scaled_clock": 2.5 * len(order_a)}
    assert durations["scaled_clock"] == 2.5 * durations["unit_clock"]

    # Three inequivalent dynamics, identical completion bookkeeping, T=1.
    initial = np.eye(42)[0]
    diffuse = spectral_evolve(L, initial, 1.0)
    diffuse_faster = spectral_evolve(2 * L, initial, 1.0)
    quantum = spectral_evolve(H, initial.astype(complex), 1.0, quantum=True)
    quantum_probabilities = np.abs(quantum) ** 2
    assert np.allclose(diffuse.sum(), 1)
    assert np.allclose(diffuse_faster.sum(), 1)
    assert np.allclose(quantum_probabilities.sum(), 1)
    assert diffuse.min() >= -1e-12 and diffuse_faster.min() >= -1e-12
    heat_rate_difference = float(np.linalg.norm(diffuse - diffuse_faster, ord=1))
    heat_quantum_difference = float(np.linalg.norm(diffuse - quantum_probabilities, ord=1))
    assert heat_rate_difference > 1e-4
    assert heat_quantum_difference > 1e-4

    # Two mass parameters also satisfy the same growth predicate, yet give
    # genuinely different spectra with the same chosen kinetic normalization.
    massive_a = np.linalg.eigvalsh(L + 0.25 * np.eye(42))
    massive_b = np.linalg.eigvalsh(L + 2.25 * np.eye(42))
    assert np.allclose(massive_b - massive_a, 2)

    # Expansion preserves internal graph structure, not full dynamics.
    bigger_vertices, bigger_edges, bigger_L, bigger_H = graph(7)
    bigger_index = {t: i for i, t in enumerate(bigger_vertices)}
    inclusion = np.zeros((132, 42))
    for i, t in enumerate(vertices):
        inclusion[bigger_index[(t, "x")], i] = 1
    assert np.array_equal(inclusion.T @ inclusion, np.eye(42))
    for small, large in ((L, bigger_L), (H, bigger_H)):
        assert np.array_equal(inclusion.T @ large @ inclusion, small + np.eye(42))
        assert not np.array_equal(large @ inclusion, inclusion @ small)
    projection = inclusion @ inclusion.T
    outside_coupling = (np.eye(132) - projection) @ bigger_H @ inclusion
    assert np.array_equal(outside_coupling.T @ outside_coupling, np.eye(42))
    growth_intertwining_residual = float(np.linalg.norm(bigger_H @ inclusion - inclusion @ H))
    assert np.allclose(growth_intertwining_residual ** 2, 84)
    bigger_initial = inclusion @ initial
    leakage = []
    for time in (0.02, 0.01, 0.005):
        state = spectral_evolve(bigger_H, bigger_initial.astype(complex), time, quantum=True)
        outside = (np.eye(132) - projection) @ state
        probability = float(np.vdot(outside, outside).real)
        leakage.append({"time": time, "outside_probability": probability,
                        "probability_over_time_squared": probability / time ** 2})
    assert abs(leakage[-1]["probability_over_time_squared"] - 1) < 1e-3

    # Completion requires memory: a field alone does not contain this record.
    constant = np.ones(42) / np.sqrt(42)
    assert np.allclose(L @ constant, np.zeros(42), atol=1e-14)
    assert np.allclose(H @ constant, 8 * constant)
    assert np.allclose(np.abs(spectral_evolve(H, constant.astype(complex), 1,
                                            quantum=True)) ** 2, np.abs(constant) ** 2)
    # Identical field configuration can coexist with either completion record.
    incomplete_record, complete_record = set(), set(range(84))
    assert incomplete_record != complete_record

    # Reaching the top face is weaker than exploring every configuration.
    # Left/right combs share no proper brackets, so their face join is K6.
    assert spans(vertices[0])[1].intersection(spans(vertices[-1])[1]) == frozenset()
    assert len({vertices[0], vertices[-1]}) == 2 < len(vertices)
    # Completion memory has its own Boolean lattice. Cardinality is modular;
    # it must not be confused with the associahedral face-rank energy defect.
    records = [{i for i in range(5) if mask & (1 << i)} for mask in range(32)]
    for a, b in product(records, repeat=2):
        assert len(a) + len(b) - len(a | b) - len(a & b) == 0

    workloads = [{"complete_K": n, "next_K": n + 1,
                  "new_relation_completions_this_stage": edge_count(n) - edge_count(n - 1)}
                 for n in range(7, 11)]
    assert [row["new_relation_completions_this_stage"] for row in workloads] == [246, 957, 3718, 14443]
    return {
        "verdict": "Completion constrains the growth trigger, but does not uniquely select the field law, its parameters, the exploration order, or a physical clock.",
        "counterexamples": {
            "distinct_valid_completion_orders": 2,
            "completion_times_for_same_record": durations,
            "heat_rates_1_vs_2_final_probability_L1_difference": heat_rate_difference,
            "heat_vs_quantum_final_probability_L1_difference": heat_quantum_difference,
            "mass_squared_0_25_vs_2_25_spectral_shift": 2.0,
        },
        "expansion_constraints": {
            "K6_to_K7_intrinsic_embedding": "isometric, graph edges preserved",
            "full_generator_intertwining": False,
            "generator_intertwining_Frobenius_residual": growth_intertwining_residual,
            "unit_negative_link_short_time_leakage": leakage,
        },
        "workloads": workloads,
        "conditional_time_prediction": "With one new relation completed per unit time, no repeats and inherited work retained, completion time equals the new-edge count; cumulative stage time grows approximately as 4^n/sqrt(n).",
        "missing_coupling": "A completion memory and a rule connecting it to field evolution/interaction events are not yet supplied.",
        "completion_vs_face_lattice": {
            "two_vertices_can_already_join_to_whole_K6": True,
            "edge_record_cardinality_modularity_defect": 0,
            "finite_completion_scope": "all configurations and elementary relations, not all paths; cycles give infinitely many paths",
        },
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
