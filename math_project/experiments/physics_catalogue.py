"""Dimensionless physics structures tested on the actual K6 cell complex.

Run: python3 math_project/experiments/physics_catalogue.py
Requires NumPy. Outputs a machine-readable verification catalogue.
These are conditional finite-model correspondences, not empirical tests.
"""

from itertools import product
import json

import numpy as np

from k6_physics_equations import cell_matrices
from k6_spin_transport import spans


class Checks:
    def __init__(self):
        self.results = {}

    def close(self, name, left, right, tolerance=1e-9):
        error = float(np.max(np.abs(np.asarray(left) - np.asarray(right))))
        assert error <= tolerance, (name, error, tolerance)
        row = self.results.setdefault(name, {"status": "PASS", "checks": 0,
                                             "maximum_residual": 0.0})
        row["checks"] += 1
        row["maximum_residual"] = max(row["maximum_residual"], error)

    def true(self, name, condition):
        assert condition, name
        row = self.results.setdefault(name, {"status": "PASS", "checks": 0,
                                             "maximum_residual": 0.0})
        row["checks"] += 1


def spectral_evolve(matrix, state, time, quantum=False):
    eigenvalues, basis = np.linalg.eigh(matrix)
    multiplier = np.exp((-1j if quantum else -1) * eigenvalues * time)
    return basis @ (multiplier * (basis.conj().T @ state))


def quadratic_wave(matrix, q0, p0, time):
    eigenvalues, basis = np.linalg.eigh(matrix)
    assert eigenvalues.min() > -1e-9
    frequency = np.sqrt(np.maximum(eigenvalues, 0))
    initial_q, initial_p = basis.T @ q0, basis.T @ p0
    cosine = np.cos(frequency * time)
    sine = np.sin(frequency * time)
    sine_over_frequency = np.full_like(frequency, time)
    np.divide(sine, frequency, out=sine_over_frequency, where=frequency > 1e-7)
    q = basis @ (cosine * initial_q + sine_over_frequency * initial_p)
    p = basis @ (-frequency * sine * initial_q + cosine * initial_p)
    return q, p


def gradient_by_differences(energy, q):
    result = np.zeros_like(q)
    step = 1e-5
    for i in range(len(q)):
        shift = np.zeros_like(q)
        shift[i] = step
        result[i] = (energy(q + shift) - energy(q - shift)) / (2 * step)
    return result


def run():
    checks = Checks()
    rng = np.random.default_rng(20261012)
    vertices, edges, b1, b2, b3, face_sizes = cell_matrices()
    # Orient the boundary of the whole four-dimensional polytope.
    _, singular, vectors = np.linalg.svd(b3, full_matrices=False)
    checks.true("cellular_complex", np.sum(singular < 1e-10) == 1)
    signs = np.rint(vectors[-1] / np.max(np.abs(vectors[-1]))).astype(int)
    checks.true("cellular_complex", np.all(np.abs(signs) == 1))
    b4 = signs[:, None]
    derivatives = [b1.T, b2.T, b3.T, b4.T]
    for left, right in zip(derivatives[1:], derivatives[:-1]):
        checks.close("cellular_complex", left @ right, 0, tolerance=0)
    d0, d1, d2, d3 = derivatives
    L = d0.T @ d0
    adjacency = 4 * np.eye(42) - L
    checks.close("cellular_complex", adjacency.sum(axis=1), 4, tolerance=0)
    H = 4 * np.eye(42) + adjacency
    C = 2 * np.eye(4) - np.eye(4, k=1) - np.eye(4, k=-1)
    times = np.linspace(0, 4, 17)
    lap_values, lap_basis = np.linalg.eigh(L)
    L_inverse = (lap_basis[:, lap_values > 1e-8] /
                 lap_values[lap_values > 1e-8]) @ lap_basis[:, lap_values > 1e-8].T

    # 1-4. Cartan, graph waves, Klein-Gordon and canonical Hamilton equations.
    for name, matrix in (("cartan_wave", C), ("graph_wave", L),
                         ("klein_gordon", L + 0.7 ** 2 * np.eye(42))):
        n = len(matrix)
        q0, p0 = rng.normal(size=(2, n))
        energy0 = (p0 @ p0 + q0 @ matrix @ q0) / 2
        for time in times:
            q, p = quadratic_wave(matrix, q0, p0, time)
            checks.close(name, (p @ p + q @ matrix @ q) / 2, energy0)
            checks.close(name, p @ (-matrix @ q) + q @ matrix @ p, 0)
        eps = 1e-5
        q, p = quadratic_wave(matrix, q0, p0, 0.8)
        _, plus = quadratic_wave(matrix, q0, p0, 0.8 + eps)
        _, minus = quadratic_wave(matrix, q0, p0, 0.8 - eps)
        checks.close(name, (plus - minus) / (2 * eps), -matrix @ q, 1e-7)
    identity, zero = np.eye(4), np.zeros((4, 4))
    J = np.block([[zero, identity], [-identity, zero]])
    K = np.block([[C, zero], [zero, identity]])
    generator = J @ K
    checks.close("hamilton_equations", generator.T @ J + J @ generator, 0, 0)
    checks.close("hamilton_equations", generator.T @ K + K @ generator, 0, 0)

    # 5. Damped/telegraph equation, including exact damped eigenmode trajectories.
    damping = 0.2
    omega2, mode_basis = np.linalg.eigh(L + np.eye(42))
    nu = np.sqrt(omega2 - damping ** 2 / 4)
    qa, va = rng.normal(size=(2, 42))
    qb = (va + damping * qa / 2) / nu
    damped_energies = []
    for time in times:
        cosine, sine = np.cos(nu * time), np.sin(nu * time)
        z = qa * cosine + qb * sine
        dz = -qa * nu * sine + qb * nu * cosine
        q = mode_basis @ (np.exp(-damping * time / 2) * z)
        p = mode_basis @ (np.exp(-damping * time / 2) * (dz - damping * z / 2))
        force = -(L + np.eye(42)) @ q - damping * p
        checks.close("telegraph_equation", p @ force + q @ (L + np.eye(42)) @ p,
                     -damping * (p @ p))
        damped_energies.append((p @ p + q @ (L + np.eye(42)) @ q) / 2)
    checks.true("telegraph_equation", np.max(np.diff(damped_energies)) <= 1e-10)

    # 6-7. Heat and unbiased continuous-time master equation.
    initial = rng.uniform(size=42)
    initial /= initial.sum()
    heat_energy = []
    for time in times:
        p = spectral_evolve(L, initial, time)
        checks.close("heat_equation", p.sum(), 1)
        checks.true("heat_equation", p.min() >= -1e-12)
        checks.true("heat_equation", p.min() >= initial.min() - 1e-12)
        checks.true("heat_equation", p.max() <= initial.max() + 1e-12)
        heat_energy.append(p @ L @ p / 2)
        flux = d0 @ p
        checks.close("markov_master_equation", -L @ p + b1 @ flux, 0)
    checks.true("heat_equation", np.max(np.diff(heat_energy)) <= 1e-12)
    checks.close("markov_master_equation", (-L).sum(axis=0), 0, 0)
    off_diagonal = -L + np.diag(np.diag(L))
    checks.true("markov_master_equation", off_diagonal.min() >= 0)

    # 8-9. Poisson equation, electrostatic energy and effective resistance.
    charge = rng.normal(size=42)
    charge -= charge.mean()
    potential = L_inverse @ charge
    checks.close("poisson_equation", L @ potential, charge)
    checks.close("poisson_equation", potential.mean(), 0)
    field = d0 @ potential
    checks.close("electrostatics_kirchhoff", b1 @ field, charge)
    checks.close("electrostatics_kirchhoff", field @ field, charge @ potential)
    resistance_min = float("inf")
    for s, t in edges:
        dipole = np.eye(42)[s] - np.eye(42)[t]
        voltage = L_inverse @ dipole
        resistance = float(dipole @ voltage)
        resistance_min = min(resistance_min, resistance)
        checks.true("electrostatics_kirchhoff", resistance > 0)
        checks.close("electrostatics_kirchhoff", resistance, np.linalg.norm(d0 @ voltage) ** 2)

    # 10-12. Magnetic quantum evolution, continuity and Ehrenfest theorem.
    psi0 = rng.normal(size=42) + 1j * rng.normal(size=42)
    psi0 /= np.linalg.norm(psi0)
    observable = np.diag(rng.normal(size=42))
    for time in times:
        psi = spectral_evolve(H, psi0, time, quantum=True)
        psi_dot = -1j * H @ psi
        checks.close("magnetic_schrodinger", np.vdot(psi, psi), 1)
        checks.close("magnetic_schrodinger", np.vdot(psi, H @ psi), np.vdot(psi0, H @ psi0))
        rho_dot = 2 * np.real(psi.conjugate() * psi_dot)
        current = np.array([2 * np.imag(psi[t].conjugate() * (-1) * psi[s])
                            for s, t in edges])
        checks.close("quantum_continuity", rho_dot + b1 @ current, 0)
        derivative = np.vdot(psi_dot, observable @ psi) + np.vdot(psi, observable @ psi_dot)
        commutator = H @ observable - observable @ H
        checks.close("ehrenfest_theorem", derivative, 1j * np.vdot(psi, commutator @ psi))
    eps = 1e-5
    psi = spectral_evolve(H, psi0, 0.7, quantum=True)
    psi_plus = spectral_evolve(H, psi0, 0.7 + eps, quantum=True)
    psi_minus = spectral_evolve(H, psi0, 0.7 - eps, quantum=True)
    checks.close("magnetic_schrodinger", 1j * (psi_plus - psi_minus) / (2 * eps), H @ psi, 1e-7)

    # 13-15. Maxwell, sources/charge conservation, and constrained edge waves.
    edge_laplacian = d0 @ d0.T + d1.T @ d1
    inverse_edge = np.linalg.inv(edge_laplacian)
    random_edge = rng.normal(size=84)
    transverse = random_edge - d0 @ (L_inverse @ (d0.T @ random_edge))
    q0, _ = quadratic_wave(edge_laplacian, transverse, np.zeros(84), 0)
    p0 = rng.normal(size=84)
    p0 -= d0 @ (L_inverse @ (d0.T @ p0))
    initial_energy = (p0 @ p0 + np.linalg.norm(d1 @ q0) ** 2) / 2
    for time in times:
        A, velocity = quadratic_wave(edge_laplacian, q0, p0, time)
        E, F = -velocity, d1 @ A
        E_dot, F_dot = d1.T @ F, d1 @ velocity
        checks.close("cellular_maxwell", d0.T @ E, 0)
        checks.close("cellular_maxwell", d2 @ F, 0)
        checks.close("cellular_maxwell", F_dot + d1 @ E, 0)
        checks.close("cellular_maxwell", (E @ E + F @ F) / 2, initial_energy)
        checks.close("edge_gauge_wave", edge_laplacian @ A, d1.T @ d1 @ A)
        current = rng.normal(size=84)
        with_source = E_dot - current
        checks.close("maxwell_with_sources", d0.T @ with_source, -d0.T @ current)
        checks.close("maxwell_with_sources", E @ with_source + F @ F_dot, -E @ current)

    # 16-18. Full cellular Dirac factorization, graded algebra, Hodge decomposition.
    sizes = [42, 84, 56, 14, 1]
    starts = np.cumsum([0] + sizes)
    differential = np.zeros((sum(sizes), sum(sizes)), dtype=int)
    for degree, derivative in enumerate(derivatives):
        differential[starts[degree + 1]:starts[degree + 2],
                     starts[degree]:starts[degree + 1]] = derivative
    checks.close("hodge_dirac", differential @ differential, 0, 0)
    Q = differential + differential.T
    laplacian = differential.T @ differential + differential @ differential.T
    checks.close("hodge_dirac", Q @ Q, laplacian, 0)
    grading = np.concatenate([np.full(size, (-1) ** degree)
                              for degree, size in enumerate(sizes)])
    Gamma = np.diag(grading)
    checks.close("supersymmetric_algebra", Gamma @ Q + Q @ Gamma, 0, 0)
    q2 = 1j * Gamma @ Q
    checks.close("supersymmetric_algebra", q2 @ q2, laplacian, 0)
    checks.close("supersymmetric_algebra", Q @ q2 + q2 @ Q, 0, 0)
    checks.close("supersymmetric_algebra", q2.conjugate().T, q2, 0)
    lvalues, lbasis = np.linalg.eigh(laplacian)
    checks.true("hodge_dirac", np.sum(np.abs(lvalues) < 1e-8) == 1)
    for time in (0.0, 0.2, 1.0, 3.0):
        diagonal = (lbasis ** 2) @ np.exp(-lvalues * time)
        checks.close("supersymmetric_algebra", grading @ diagonal, 1)
    longitudinal = d0 @ (L_inverse @ (d0.T @ random_edge))
    coexact = d1.T @ np.linalg.pinv(d1 @ d1.T, rcond=1e-10) @ (d1 @ random_edge)
    checks.close("hodge_decomposition", longitudinal + coexact, random_edge)
    checks.close("hodge_decomposition", longitudinal @ coexact, 0)
    checks.close("hodge_decomposition", edge_laplacian @ inverse_edge, np.eye(84))

    # 19-20. Nonlinear scalar field and Allen-Cahn gradient flow.
    q, p = rng.normal(size=(2, 42))
    mu2, coupling = 0.3, 0.2
    def scalar_energy(x):
        return x @ L @ x / 2 + mu2 * (x @ x) / 2 + coupling * np.sum(x ** 4) / 4
    scalar_gradient = L @ q + mu2 * q + coupling * q ** 3
    checks.close("nonlinear_phi4", gradient_by_differences(scalar_energy, q), scalar_gradient, 1e-7)
    checks.close("nonlinear_phi4", p @ (-scalar_gradient) + scalar_gradient @ p, 0)
    def double_well(x):
        return x @ L @ x / 2 + coupling * np.sum((x ** 2 - 1) ** 2) / 4
    ac_gradient = L @ q + coupling * (q ** 3 - q)
    checks.close("allen_cahn", gradient_by_differences(double_well, q), ac_gradient, 1e-7)
    checks.close("allen_cahn", ac_gradient @ (-ac_gradient), -np.linalg.norm(ac_gradient) ** 2)

    # 21. Canonical ensemble for rank energy on all 198 completed faces.
    degeneracies = np.array([1, 42, 84, 56, 14, 1])
    energies = np.repeat(np.arange(6, dtype=float), degeneracies)
    beta = 0.7
    weights = np.exp(-beta * energies)
    partition = weights.sum()
    pi = weights / partition
    mean_energy = pi @ energies
    entropy = -pi @ np.log(pi)
    checks.close("gibbs_thermodynamics", entropy, np.log(partition) + beta * mean_energy)
    beta_step = 1e-5
    logz = lambda x: np.log(np.exp(-x * energies).sum())
    checks.close("gibbs_thermodynamics", (logz(beta + beta_step) - logz(beta - beta_step)) /
                 (2 * beta_step), -mean_energy, 1e-8)
    heat_capacity = beta ** 2 * (pi @ (energies ** 2) - mean_energy ** 2)
    checks.true("gibbs_thermodynamics", heat_capacity >= 0)

    # 22. A defect-based energy can enter a genuine detailed-balance master law.
    # Explicit model choice: pin one vertex v0, E(v) = -Delta(v0,v), epsilon=1.
    bracket_sets = [spans(v)[1] for v in vertices]
    vertex_energy = np.array([0 if i == 0 else 3 - len(bs & bracket_sets[0])
                              for i, bs in enumerate(bracket_sets)], dtype=float)
    checks.true("defect_metropolis", vertex_energy.min() >= 0)
    stationary = np.exp(-beta * vertex_energy)
    stationary /= stationary.sum()
    rates = np.zeros((42, 42))
    for s, t in edges:
        for source, target in ((s, t), (t, s)):
            rates[target, source] = np.exp(-beta * max(vertex_energy[target] -
                                                      vertex_energy[source], 0))
    rates -= np.diag(rates.sum(axis=0))
    checks.close("defect_metropolis", rates.sum(axis=0), 0)
    checks.close("defect_metropolis", rates @ stationary, 0)
    weighted = rates * stationary[None, :]
    checks.close("defect_metropolis", weighted, weighted.T)
    root = np.sqrt(stationary)
    symmetric = rates * root[None, :] / root[:, None]
    checks.close("defect_metropolis", symmetric, symmetric.T)
    evals, eigenvectors = np.linalg.eigh(symmetric)
    entropy_history = []
    for time in times:
        state = root * (eigenvectors @ (np.exp(evals * time) *
                                       (eigenvectors.T @ (initial / root))))
        checks.close("defect_metropolis", state.sum(), 1)
        checks.true("defect_metropolis", state.min() > 0)
        entropy_history.append(float(state @ np.log(state / stationary)))
        derivative = (rates @ state) @ np.log(state / stationary)
        checks.true("defect_metropolis", derivative <= 1e-12)
    checks.true("defect_metropolis", np.max(np.diff(entropy_history)) <= 1e-12)

    # 23. Exact Ising frustration on a square and pentagon (classical +/-1 states).
    ising = {}
    for size in (4, 5):
        es = np.array([sum(s[i] * s[(i + 1) % size] for i in range(size))
                       for s in product((-1, 1), repeat=size)])
        z_exact = np.exp(-beta * es).sum()
        z_transfer = (2 * np.cosh(beta)) ** size + (-2 * np.sinh(beta)) ** size
        checks.close("ising_frustration", z_exact, z_transfer)
        checks.close("ising_frustration", es.min(), -size if size == 4 else -size + 2, 0)
        ground_count = int(np.sum(es == es.min()))
        checks.true("ising_frustration", ground_count == (2 if size == 4 else 10))
        ising[str(size)] = {"ground_energy": int(es.min()), "ground_states": ground_count}

    # 24. Abelian Wilson loops, gauge covariance and compact flux curvature.
    theta = np.pi * np.ones(84)
    phase_flux = np.exp(1j * (d1 @ theta))
    expected_holonomy = np.array([-1 if size == 5 else 1 for size in face_sizes])
    checks.close("wilson_gauge", phase_flux, expected_holonomy)
    chi = rng.normal(size=42)
    checks.close("wilson_gauge", np.exp(1j * (d1 @ (theta + d0 @ chi))), phase_flux)
    # Discrete Bianchi product around every 3D facet, with orientation signs.
    checks.close("wilson_gauge", np.exp(1j * (d2 @ (d1 @ theta))), 1)
    compact_energy = float(np.sum(1 - phase_flux.real))
    checks.close("wilson_gauge", compact_energy, 56)
    flat_covariant = d0.astype(complex)
    flux_covariant = np.abs(d0).astype(complex)
    checks.close("magnetic_schrodinger", flat_covariant.conjugate().T @ flat_covariant, L, 0)
    checks.close("magnetic_schrodinger", flux_covariant.conjugate().T @ flux_covariant, H, 0)
    flat_D = d1 @ flat_covariant
    curved_D = d1 @ flux_covariant
    checks.close("wilson_gauge", flat_D, 0, 0)
    checks.true("wilson_gauge", np.max(np.abs(curved_D)) > 0)

    # 25. The travel monoid's shear is exactly sampled free Hamiltonian flow.
    symplectic = np.array([[0, 1], [-1, 0]])
    shear = lambda label: np.array([[1, label], [0, 1]])
    for a, b in product(range(-5, 6), repeat=2):
        checks.close("free_particle_shear", shear(a) @ shear(b), shear(a + b), 0)
        checks.close("free_particle_shear", shear(a).T @ symplectic @ shear(a), symplectic, 0)
    phase_point = rng.normal(size=2)
    for time in range(-5, 6):
        q, p = shear(time) @ phase_point
        checks.close("free_particle_shear", q, phase_point[0] + time * phase_point[1])
        checks.close("free_particle_shear", p, phase_point[1])

    # 26. Open A4 Toda chain: added exponential potential, exact Lax structure.
    def toda_energy(q, p):
        return (p @ p) / 2 + np.exp(q[:-1] - q[1:]).sum()

    def toda_force(q):
        bonds = np.exp(q[:-1] - q[1:])
        force = np.zeros(5)
        force[:-1] -= bonds
        force[1:] += bonds
        return force

    def toda_lax(q, p):
        a = np.exp((q[:-1] - q[1:]) / 2) / 2
        b = -p / 2
        matrix = np.diag(b) + np.diag(a, k=1) + np.diag(a, k=-1)
        skew = np.diag(a, k=1) - np.diag(a, k=-1)
        a_dot = a * (p[:-1] - p[1:]) / 2
        matrix_dot = np.diag(-toda_force(q) / 2) + np.diag(a_dot, k=1) + np.diag(a_dot, k=-1)
        return matrix, skew, matrix_dot

    tq, tp = rng.normal(scale=0.3, size=(2, 5))
    # A4 roots live in the zero-sum subspace of five coordinates.
    tq -= tq.mean()
    tp -= tp.mean()
    checks.close("toda_lax", gradient_by_differences(lambda x: toda_energy(x, tp), tq),
                 -toda_force(tq), 1e-8)
    tm, tb, tm_dot = toda_lax(tq, tp)
    checks.close("toda_lax", tm_dot, tb @ tm - tm @ tb)
    checks.close("toda_lax", toda_energy(tq, tp), 2 * np.trace(tm @ tm))
    for power in range(1, 6):
        checks.close("toda_lax", power * np.trace(np.linalg.matrix_power(tm, power - 1) @ tm_dot), 0)
    checks.close("toda_lax", toda_force(tq).sum(), 0)

    def toda_rhs(state):
        q, p = state[:5], state[5:]
        return np.concatenate([p, toda_force(q)])

    def integrate_toda(steps):
        state = np.concatenate([tq, tp])
        dt = 1 / steps
        for _ in range(steps):
            first = toda_rhs(state)
            second = toda_rhs(state + dt * first / 2)
            third = toda_rhs(state + dt * second / 2)
            fourth = toda_rhs(state + dt * third)
            state += dt * (first + 2 * second + 2 * third + fourth) / 6
        return state

    coarse, fine = integrate_toda(100), integrate_toda(200)
    checks.close("toda_lax", coarse, fine, 1e-7)
    final_lax, _, _ = toda_lax(fine[:5], fine[5:])
    for power in range(1, 6):
        checks.close("toda_lax", np.trace(np.linalg.matrix_power(final_lax, power)),
                     np.trace(np.linalg.matrix_power(tm, power)), 1e-7)

    betti = []
    for degree, size in enumerate(sizes):
        incoming_rank = 0 if degree == 0 else np.linalg.matrix_rank(derivatives[degree - 1])
        outgoing_rank = 0 if degree == 4 else np.linalg.matrix_rank(derivatives[degree])
        betti.append(int(size - incoming_rank - outgoing_rank))
    checks.true("cellular_complex", betti == [1, 0, 0, 0, 0])
    return {
        "scope": "Conditional dimensionless finite-model correspondences; no empirical validation or Lean proof of added dynamics.",
        "cells_by_dimension": sizes,
        "cellular_betti_numbers": betti,
        "tested_equation_forms": len(checks.results) - 1,
        "checks": checks.results,
        "numerical_results": {
            "magnetic_lowest_eigenvalue": float(np.linalg.eigvalsh(H)[0]),
            "minimum_edge_effective_resistance": resistance_min,
            "rank_energy_partition_at_beta_0_7": float(partition),
            "rank_energy_heat_capacity_at_beta_0_7": float(heat_capacity),
            "defect_energy_levels": sorted(set(vertex_energy.tolist())),
            "defect_relative_entropy_initial_final": [entropy_history[0], entropy_history[-1]],
            "ising_cycles": ising,
            "compact_wilson_energy_fixed_parity_background": compact_energy,
        },
        "important_obstruction": "Nonflat parity transport has d1 D_U != 0; it cannot replace the flat cellular differential in the supersymmetric construction.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
