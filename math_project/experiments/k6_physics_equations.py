"""Check structural wave, gauge-field and quantum equations derived on K6.

Requires numpy. The quadratic actions and continuous amplitudes are added
modeling assumptions; these are not physics theorems from the Lean paper.
"""

from itertools import combinations
import json

import numpy as np

from k6_spin_transport import compatible, right_rotations, spans, trees


def cell_matrices():
    vertices = trees(6)
    index = {v: i for i, v in enumerate(vertices)}
    edges = sorted((index[v], index[w]) for v in vertices
                   for w in right_rotations(v))
    edge_index = {frozenset((s, t)): i for i, (s, t) in enumerate(edges)}
    incidence = np.zeros((42, 84), dtype=int)
    neighbors = {i: set() for i in range(42)}
    for e, (s, t) in enumerate(edges):
        incidence[s, e], incidence[t, e] = -1, 1
        neighbors[s].add(t)
        neighbors[t].add(s)
    intervals = [(i, j) for i in range(6) for j in range(i + 2, 7)
                 if (i, j) != (0, 6)]
    brackets = [spans(v)[1] for v in vertices]
    columns = []
    sizes = []
    constraints = []
    for a, b in combinations(intervals, 2):
        if not compatible(a, b):
            continue
        face = {i for i, bs in enumerate(brackets) if {a, b} <= bs}
        start = min(face)
        path = [start, min(neighbors[start] & face)]
        while True:
            candidates = (neighbors[path[-1]] & face) - {path[-2]}
            assert len(candidates) == 1
            nxt = candidates.pop()
            if nxt == start:
                break
            assert nxt not in path
            path.append(nxt)
        assert set(path) == face
        boundary = np.zeros(84, dtype=int)
        for s, t in zip(path, path[1:] + path[:1]):
            e = edge_index[frozenset((s, t))]
            boundary[e] = 1 if edges[e] == (s, t) else -1
        columns.append(boundary)
        sizes.append(len(face))
        constraints.append({a, b})
    boundary2 = np.column_stack(columns)
    # Orient each 3D facet's closed boundary; verify the resulting signs exactly.
    facet_columns = []
    for interval in intervals:
        included = [i for i, fixed in enumerate(constraints) if interval in fixed]
        local = boundary2[:, included]
        _, singular, vectors = np.linalg.svd(local, full_matrices=False)
        assert np.sum(singular < 1e-10) == 1
        null = vectors[-1]
        signs = np.rint(null / np.max(np.abs(null))).astype(int)
        assert np.all(np.abs(signs) == 1)
        assert np.array_equal(local @ signs, np.zeros(84, dtype=int))
        column = np.zeros(56, dtype=int)
        column[included] = signs
        facet_columns.append(column)
    return vertices, edges, incidence, boundary2, np.column_stack(facet_columns), sizes


def run():
    rng = np.random.default_rng(20261012)
    _, edges, boundary1, boundary2, boundary3, sizes = cell_matrices()
    d0, d1, d2 = boundary1.T, boundary2.T, boundary3.T
    assert np.array_equal(d1 @ d0, np.zeros((56, 42), dtype=int))
    assert np.array_equal(d2 @ d1, np.zeros((14, 84), dtype=int))
    assert np.linalg.matrix_rank(d0) == 41
    assert np.linalg.matrix_rank(d1) == 43
    assert np.linalg.matrix_rank(d2) == 13

    # Maxwell structure: A is on matter edges, phi on vertices, F on faces.
    A, velocity = rng.normal(size=(2, 84))
    phi, chi, chi_dot = rng.normal(size=(3, 42))
    E, F = -velocity - d0 @ phi, d1 @ A
    assert np.allclose(d2 @ F, 0)
    A_new = A + d0 @ chi
    velocity_new = velocity + d0 @ chi_dot
    phi_new = phi - chi_dot
    assert np.allclose(d1 @ A_new, F)
    assert np.allclose(-velocity_new - d0 @ phi_new, E)
    # Faraday identity; Ampere evolution preserves Gauss's constraint.
    assert np.allclose(d1 @ E + d1 @ velocity, 0)
    E_dot = d1.T @ F
    F_dot = -d1 @ E
    assert np.allclose(d0.T @ E_dot, 0)
    energy_derivative = E @ E_dot + F @ F_dot
    assert abs(energy_derivative) < 1e-10

    # K6 has root labels A4. Its Cartan form is exactly B^T B.
    B = np.zeros((5, 4), dtype=int)
    for e in range(5):
        if e > 0:
            B[e, e - 1] -= 1
        if e < 4:
            B[e, e] += 1
    C = B.T @ B
    expected = 2 * np.eye(4, dtype=int)
    for i in range(3):
        expected[i, i + 1] = expected[i + 1, i] = -1
    assert np.array_equal(C, expected)
    eigenvalues, modes = np.linalg.eigh(C)
    analytic = 2 - 2 * np.cos(np.arange(1, 5) * np.pi / 5)
    assert np.allclose(eigenvalues, analytic)
    q0, v0 = rng.normal(size=(2, 4))
    q_modes, v_modes = modes.T @ q0, modes.T @ v0
    frequencies = np.sqrt(eigenvalues)
    energies = []
    for time in np.linspace(0, 10, 101):
        cosine, sine = np.cos(frequencies * time), np.sin(frequencies * time)
        q = modes @ (q_modes * cosine + v_modes * sine / frequencies)
        v = modes @ (-q_modes * frequencies * sine + v_modes * cosine)
        energies.append((v @ v + q @ C @ q) / 2)
    assert np.allclose(energies, energies[0])

    # Proposed spinor parity becomes a Z2 connection on the rotation graph.
    # Signed covariant derivative: psi_target - u_e psi_source, u_e = -1.
    covariant = np.zeros((84, 42), dtype=complex)
    for e, (s, t) in enumerate(edges):
        covariant[e, s] = covariant[e, t] = 1
    H = covariant.conj().T @ covariant
    assert np.allclose(H, H.conj().T)
    spectrum, basis = np.linalg.eigh(H)
    assert spectrum[0] > 1e-8  # Frustrated pentagons forbid a nonzero zero mode.
    ordinary = np.linalg.eigvalsh(d0.T @ d0)
    assert abs(ordinary[0]) < 1e-10
    psi = rng.normal(size=42) + 1j * rng.normal(size=42)
    evolved = basis @ (np.exp(-1j * spectrum * 0.7) * (basis.conj().T @ psi))
    assert np.allclose(np.vdot(evolved, evolved), np.vdot(psi, psi))
    phases = np.exp(1j * rng.normal(size=42))
    transformed = np.zeros_like(covariant)
    for e, (s, t) in enumerate(edges):
        u_new = -phases[t] * phases[s].conjugate()
        transformed[e, s], transformed[e, t] = -u_new, 1
    assert np.allclose(np.linalg.norm(transformed @ (phases * psi)) ** 2,
                       np.linalg.norm(covariant @ psi) ** 2)
    holonomy = np.exp(1j * np.pi * (d1 @ np.ones(84)))
    assert all(np.allclose(w, -1 if size == 5 else 1)
               for w, size in zip(holonomy, sizes))
    return {
        "cells": {"vertices": 42, "edges": 84, "two_faces": 56},
        "boundary_of_boundary": "exactly zero",
        "maxwell_checks": ["gauge invariance", "magnetic Bianchi identity", "Faraday identity",
                           "Gauss constraint preservation", "energy conservation"],
        "cartan_wave_frequencies": frequencies.tolist(),
        "wave_energy_max_drift": float(np.ptp(energies)),
        "quantum_checks": ["Hermitian Hamiltonian", "norm conservation",
                           "local phase covariance", "face holonomies"],
        "parity_connection_lowest_eigenvalue": float(spectrum[0]),
        "ordinary_connection_lowest_eigenvalue": float(ordinary[0]),
        "qualification": "Quadratic actions and continuous fields are supplied assumptions; spin and spacetime are not derived.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
