"""Does higher/lower associahedral nesting force quantum measurement?

Build an actual K3 x K4 facet inside K6. Compare a classical probability
model with an explicitly added Hilbert/Born/instrument model. Quantum
diagnostics do not constitute a derivation of those added assumptions.
"""

from itertools import combinations, product
import json

import numpy as np

from growth_constraints import graph
from k6_spin_transport import spans, trees
from physics_catalogue import Checks, spectral_evolve


def graft_first(outer, inner):
    if outer == "x":
        return inner
    return graft_first(outer[0], inner), outer[1]


def reduced_states(rho):
    tensor = rho.reshape(2, 5, 2, 5)
    return np.trace(tensor, axis1=1, axis2=3), np.trace(tensor, axis1=0, axis2=2)


def density(state):
    return np.outer(state, state.conjugate())


def purity(rho):
    return float(np.trace(rho @ rho).real)


def run():
    checks = Checks()
    vertices, edges, L, H = graph(6)
    index = {t: i for i, t in enumerate(vertices)}
    subsystem = trees(3)
    observer = trees(4)
    inclusion = np.zeros((42, 10))
    for i, inner in enumerate(subsystem):
        for j, outer in enumerate(observer):
            inclusion[index[graft_first(outer, inner)], i * 5 + j] = 1
    face_indices = {i for i, t in enumerate(vertices) if (0, 3) in spans(t)[1]}
    checks.true("actual_product_facet", len(face_indices) == 10)
    checks.true("actual_product_facet", set(np.flatnonzero(inclusion.sum(axis=1))) == face_indices)
    checks.close("actual_product_facet", inclusion.T @ inclusion, np.eye(10), 0)
    _, _, _, Hs = graph(3)
    _, _, _, Ho = graph(4)
    local_H = np.kron(Hs, np.eye(5)) + np.kron(np.eye(2), Ho)
    checks.close("actual_product_facet", inclusion.T @ H @ inclusion, local_H + np.eye(10), 0)

    # Bracket-presence tests are perfectly valid commuting classical events.
    intervals = [(i, j) for i in range(6) for j in range(i + 2, 7)
                 if (i, j) != (0, 6)]
    bracket_sets = [spans(t)[1] for t in vertices]
    events = [np.diag([int(interval in bs) for bs in bracket_sets]) for interval in intervals]
    for a, b in combinations(events, 2):
        checks.close("geometric_bracket_events", a @ b - b @ a, 0, 0)
    checks.close("geometric_bracket_events", L.sum(axis=0), 0, 0)

    # A reversible classical recorder on the same two-by-five product states.
    swap = np.eye(5)
    swap[:2, :2] = np.array([[0, 1], [1, 0]])
    controlled_copy = np.block([[np.eye(5), np.zeros((5, 5))],
                                [np.zeros((5, 5)), swap]])
    checks.close("classical_nested_observer", controlled_copy.T @ controlled_copy, np.eye(10), 0)
    classical_initial = np.zeros(10)
    classical_initial[0] = classical_initial[5] = 0.5
    classical_final = controlled_copy @ classical_initial
    checks.close("classical_nested_observer", classical_final[[0, 6]], [0.5, 0.5], 0)
    checks.close("classical_nested_observer", classical_final.sum(), 1, 0)
    classical_table = classical_final.reshape(2, 5)
    checks.close("classical_nested_observer", classical_table[0, 1] + classical_table[1, 0], 0, 0)

    # Pure geometry-derived negative-link Hamiltonian on the isolated product
    # is a sum of local operators: it cannot entangle a product state.
    rng = np.random.default_rng(20261012)
    s = rng.normal(size=2) + 1j * rng.normal(size=2)
    o = rng.normal(size=5) + 1j * rng.normal(size=5)
    s /= np.linalg.norm(s)
    o /= np.linalg.norm(o)
    unentangled_purities = []
    for time in (0.0, 0.2, 0.7, 1.4):
        state = spectral_evolve(local_H, np.kron(s, o), time, quantum=True)
        factorized = np.kron(spectral_evolve(Hs, s, time, quantum=True),
                             spectral_evolve(Ho, o, time, quantum=True))
        checks.close("isolated_natural_dynamics", state, factorized)
        rs, ro = reduced_states(density(state))
        checks.close("isolated_natural_dynamics", purity(rs), 1)
        unentangled_purities.append(purity(rs))
        pointer_zero = np.eye(5)[0]
        out0 = spectral_evolve(local_H, np.kron(np.eye(2)[0], pointer_zero), time, quantum=True)
        out1 = spectral_evolve(local_H, np.kron(np.eye(2)[1], pointer_zero), time, quantum=True)
        _, pointer0 = reduced_states(density(out0))
        _, pointer1 = reduced_states(density(out1))
        checks.close("isolated_natural_dynamics", pointer0, pointer1)

    # Quantum measurement: now add complex superposition, Born probabilities,
    # a controlled interaction, and partial trace. None is forced by nesting.
    zero, one = np.eye(2)
    plus, minus = (zero + one) / np.sqrt(2), (zero - one) / np.sqrt(2)
    pointer0 = np.eye(5)[0]
    coherent = np.kron(plus, pointer0)
    entangled = controlled_copy @ coherent
    rho = density(entangled)
    rs, ro = reduced_states(rho)
    checks.close("added_quantum_recording", np.diag(rho), classical_final)
    checks.close("added_quantum_recording", purity(rs), 0.5)
    checks.close("added_quantum_recording", purity(ro), 0.5)
    checks.close("added_quantum_recording", purity(rho), 1)
    classical_rho = np.diag(classical_final)
    checks.true("added_quantum_recording", np.linalg.norm(rho - classical_rho) > 0.5)

    hadamard = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
    checks.close("phase_sensitive_interference", np.abs(plus) ** 2, np.abs(minus) ** 2)
    checks.close("phase_sensitive_interference", np.abs(hadamard @ plus) ** 2, [1, 0])
    checks.close("phase_sensitive_interference", np.abs(hadamard @ minus) ** 2, [0, 1])
    checks.close("phase_sensitive_interference", np.diag(hadamard @ rs @ hadamard.T), [0.5, 0.5])
    unrecorded = controlled_copy.T @ entangled
    restored = np.kron(hadamard, np.eye(5)) @ unrecorded
    restored_s, _ = reduced_states(density(restored))
    checks.close("phase_sensitive_interference", np.diag(restored_s), [1, 0])

    # Vary the recording strength without changing the associahedral geometry.
    visibility_results = []
    for alpha in np.linspace(0, np.pi / 2, 9):
        record0 = np.eye(5)[0]
        record1 = np.cos(alpha) * np.eye(5)[0] + np.sin(alpha) * np.eye(5)[1]
        joint = (np.kron(zero, record0) + np.kron(one, record1)) / np.sqrt(2)
        reduced, _ = reduced_states(density(joint))
        output = np.diag(hadamard @ reduced @ hadamard.T).real
        visibility = abs(np.vdot(record0, record1))
        distinguishability = np.sum(np.abs(np.linalg.eigvalsh(density(record0) - density(record1)))) / 2
        checks.close("recording_vs_interference", output, [(1 + np.cos(alpha)) / 2,
                                                          (1 - np.cos(alpha)) / 2])
        checks.close("recording_vs_interference", visibility ** 2 + distinguishability ** 2, 1)
        visibility_results.append({"record_angle": float(alpha), "visibility": float(visibility),
                                   "record_distinguishability": float(distinguishability)})

    # Added noncommuting measurements, contrasted with the commuting face events.
    Pz = density(zero)
    Px = density(plus)
    commutator = Pz @ Px - Px @ Pz
    checks.true("added_measurement_incompatibility", np.linalg.norm(commutator) > 0)
    initial_s = zero
    z_then_x = float(np.linalg.norm(Px @ Pz @ initial_s) ** 2)
    x_then_z = float(np.linalg.norm(Pz @ Px @ initial_s) ** 2)
    checks.close("added_measurement_incompatibility", z_then_x, 0.5)
    checks.close("added_measurement_incompatibility", x_then_z, 0.25)
    # Order alone is not a quantum diagnostic: classical invasive resets differ too.
    reset0 = np.array([[1, 1], [0, 0]])
    reset1 = np.array([[0, 0], [1, 1]])
    checks.true("classical_order_counterexample", not np.array_equal(reset1 @ reset0, reset0 @ reset1))

    # Bell benchmark on the same 2x5 states, using only the pointer's first two.
    X = np.array([[0, 1], [1, 0]])
    Z = np.diag([1, -1])
    def pointer_observable(block):
        matrix = np.eye(5)
        matrix[:2, :2] = block
        return matrix
    B0 = pointer_observable((Z + X) / np.sqrt(2))
    B1 = pointer_observable((Z - X) / np.sqrt(2))
    CHSH = np.kron(Z, B0 + B1) + np.kron(X, B0 - B1)
    quantum_chsh = float(np.trace(rho @ CHSH).real)
    mixed_chsh = float(np.trace(classical_rho @ CHSH).real)
    checks.close("bell_benchmark", quantum_chsh, 2 * np.sqrt(2))
    local_values = [a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1
                    for a0, a1, b0, b1 in product((-1, 1), repeat=4)]
    checks.close("bell_benchmark", max(abs(value) for value in local_values), 2, 0)
    checks.true("bell_benchmark", abs(mixed_chsh) <= 2)
    checks.close("bell_benchmark", B0 @ B0, np.eye(5))
    checks.close("bell_benchmark", B1 @ B1, np.eye(5))

    # No-signalling identity for nonselective local projective measurements.
    for projector in (Pz, Px):
        projectors = [np.kron(projector, np.eye(5)), np.kron(np.eye(2) - projector, np.eye(5))]
        after = sum(P @ rho @ P for P in projectors)
        _, after_observer = reduced_states(after)
        checks.close("no_signalling_identity", after_observer, ro)

    # If the full K6 environment is allowed, projected quantum dynamics can
    # generate conditional correlations. This already assumes quantum dynamics
    # and Born postselection; it is not a derivation from observer size.
    initial_global = inclusion @ np.kron(zero, pointer0)
    conditional = []
    for time in (0.2, 0.7, 1.4):
        whole = spectral_evolve(H, initial_global.astype(complex), time, quantum=True)
        projected = inclusion.T @ whole
        weight = float(np.vdot(projected, projected).real)
        reduced, _ = reduced_states(density(projected / np.sqrt(weight)))
        checks.true("full_environment_postselection", 0 < weight <= 1 + 1e-12)
        checks.true("full_environment_postselection", 0.5 - 1e-12 <= purity(reduced) <= 1 + 1e-12)
        # On this regular graph H=8I-L. A real initial basis vector gives
        # conjugate trajectories up to global phase, hence equal probabilities
        # and subsystem purity. This correlation is not specific to -1 links.
        ordinary_whole = spectral_evolve(L, initial_global.astype(complex), time, quantum=True)
        ordinary_projected = inclusion.T @ ordinary_whole
        ordinary_weight = float(np.vdot(ordinary_projected, ordinary_projected).real)
        ordinary_reduced, _ = reduced_states(density(ordinary_projected / np.sqrt(ordinary_weight)))
        checks.close("ordinary_connection_control", ordinary_weight, weight)
        checks.close("ordinary_connection_control", purity(ordinary_reduced), purity(reduced))
        conditional.append({"time": time, "facet_probability": weight,
                            "conditional_subsystem_purity": purity(reduced),
                            "ordinary_connection_purity": purity(ordinary_reduced)})

    return {
        "verdict": "Nesting permits both classical and quantum observer models; quantum measurement is not forced by the geometry alone.",
        "geometric_system": "actual K3 x K4 facet inside K6",
        "classical_observer_states": 5,
        "subsystem_states": 2,
        "commuting_geometric_observable_pairs_tested": 91,
        "checks": checks.results,
        "quantitative_results": {
            "classical_record_accuracy": 1.0,
            "isolated_product_subsystem_purities": unentangled_purities,
            "added_entangled_subsystem_purity": purity(rs),
            "selective_joint_probabilities_Z_then_X_and_X_then_Z": [z_then_x, x_then_z],
            "classical_local_CHSH_bound": 2,
            "added_quantum_CHSH": quantum_chsh,
            "dephased_correlated_state_CHSH": mixed_chsh,
            "recording_strength_tradeoff": visibility_results,
            "full_environment_with_added_quantum_postselection": conditional,
        },
        "added_quantum_assumptions": ["complex Hilbert state space", "tensor-product state representation",
                                       "unitary time evolution", "Born probabilities", "projective instruments",
                                       "chosen controlled recording interaction"],
        "qualification": "Algebraic and numerical model tests, not a physical Bell experiment or derivation of single measurement outcomes.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
