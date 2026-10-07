"""Dirac bridge: symbolic identities, exact rational walks, and numerical limits.

Run: python3 -m new_frontiers.experiments.relativistic_bridge.certificate
Optional: --output PATH. Requires SymPy; numerical diagnostics use stdlib only.
The mass/count coupling is an ADDED law, not a consequence of submodularity.
"""

import argparse
import cmath
from fractions import Fraction as F
import json
import math
from pathlib import Path

import sympy as s

from .._shared.exact import QComplex, ZERO, ONE, apply, dagger
from .._shared.k4_graph import EDGES, mass
from .._shared.coins import rational_coin


def symbolic_checks():
    eye = s.eye(2)
    x = s.Matrix([[0, 1], [1, 0]])
    y = s.Matrix([[0, -s.I], [s.I, 0]])
    z = s.diag(1, -1)
    k, theta, eps, p, m, potential = s.symbols('k theta eps p m V', real=True)
    coin = s.cos(theta)*eye - s.I*s.sin(theta)*x
    shift = s.cos(k)*eye - s.I*s.sin(k)*z
    walk = shift*coin
    assert s.simplify(walk.H*walk-eye) == s.zeros(2)
    assert s.simplify(walk.det()) == 1
    assert s.simplify(s.trace(walk)-2*s.cos(k)*s.cos(theta)) == 0
    components = (s.cos(k)*s.sin(theta)*x + s.sin(k)*s.sin(theta)*y
                  + s.sin(k)*s.cos(theta)*z)
    assert s.simplify(walk-(s.cos(k)*s.cos(theta)*eye-s.I*components)) == s.zeros(2)
    original = s.Matrix([[1+s.I, 1-s.I], [1-s.I, 1+s.I]])/2
    phase = s.expand_complex(s.exp(s.I*s.pi/4))
    assert s.simplify(original-phase*coin.subs(theta, s.pi/4)) == s.zeros(2)

    h = p*z+m*x
    assert h*h == (p*p+m*m)*eye
    scaled = walk.subs({k: eps*p, theta: eps*m})
    generator = scaled.applyfunc(lambda q: s.diff(q, eps).subs(eps, 0))
    assert generator == -s.I*h
    with_phase = s.exp(-s.I*eps*potential)*scaled
    phase_generator = with_phase.applyfunc(lambda q: s.diff(q, eps).subs(eps, 0))
    assert s.simplify(phase_generator+s.I*(h+potential*eye)) == s.zeros(2)

    # An exactly rational local coin has the same infinitesimal mass term.
    a = eps*m/2
    rational_coin = ((1-a*a)*eye-2*s.I*a*x)/(1+a*a)
    assert s.simplify(rational_coin.H*rational_coin-eye) == s.zeros(2)
    assert rational_coin.applyfunc(lambda q: s.diff(q, eps).subs(eps, 0)) == -s.I*m*x
    # Implicitly differentiate cos(omega)=cos(k)*cos(theta) at k=0.
    # Here 0<theta<pi/2: omega(0)=theta, omega'(0)=0.
    band_curvature = s.cos(theta)/s.sin(theta)
    band_expansion = theta+band_curvature*k*k/2
    residual = s.cos(band_expansion)-s.cos(k)*s.cos(theta)
    assert s.simplify(s.diff(residual,k,2).subs(k,0)) == 0
    # E=omega(eps*p)/eps; for m>0 and eps*m<2, curvature is eps*cot(theta).
    curvature = s.cancel(eps*(1-a*a)/(2*a))
    assert s.simplify(curvature-(1/m-eps**2*m/4)) == 0
    assert s.limit(curvature, eps, 0) == 1/m

    fixed = s.acos(s.cos(k)/s.sqrt(2))
    assert s.simplify(s.diff(fixed,k,2).subs(k,0)) == 1
    fourth = s.simplify(s.diff(fixed,k,4).subs(k,0)/s.factorial(4))
    assert fourth == -s.Rational(1,6)
    matched = s.sqrt((s.pi/4)**2+(s.pi/4)*k*k)
    matched_fourth = s.simplify(s.diff(matched,k,4).subs(k,0)/s.factorial(4))
    assert matched_fourth == -1/(2*s.pi)

    # Static lapse principal symbol has speeds +/-N; identity potential cannot change them.
    lapse, q = s.symbols('N q', real=True)
    assert s.simplify((lapse*p*z+lapse*m*x)**2-lapse**2*(p*p+m*m)*eye) == s.zeros(2)
    assert (q*eye-z).det() == q*q-1
    assert (q*eye-lapse*z).det() == q*q-lapse*lapse
    return {'coin_matches_existing_B_up_to_global_phase': True,
            'dirac_generator': 'p*sigma_z + m*sigma_x',
            'relativistic_dispersion': 'E^2 = p^2 + m^2 (continuum limit)',
            'rational_coin_curvature': '1/m - epsilon^2*m/4; m>0, epsilon*m<2',
            'fixed_balanced_coin_fourth_order': str(fourth),
            'gap_and_curvature_matched_relativistic_fourth_order': str(matched_fourth),
            'weak_scalar_phase_generator': 'V*identity, not metric transport',
            'lapse_characteristic_speeds': '+/-N'}


def exact_step(state, count_at, epsilon, inverse=False):
    if inverse:
        unshifted = {(site-(1 if direction == 0 else -1), direction): value
                     for (site, direction), value in state.items()}
        result = {}
        for site in {site for site, _ in unshifted}:
            vector = tuple(unshifted.get((site, d), ZERO) for d in (0, 1))
            for d, value in enumerate(apply(dagger(rational_coin(count_at(site), epsilon)), vector)):
                result[site, d] = value
    else:
        result = {}
        for site in {site for site, _ in state}:
            vector = tuple(state.get((site, d), ZERO) for d in (0, 1))
            for d, value in enumerate(apply(rational_coin(count_at(site), epsilon), vector)):
                result[site+(1 if d == 0 else -1), d] = value
    return {key: value for key, value in result.items() if value != ZERO}


def exact_walk_checks():
    def mask(edges):
        return sum(1 << EDGES.index(edge) for edge in edges)
    objects = [mask(((0,1),(1,2))), mask(((0,1),(1,2),(0,2))),
               mask(((0,1),(0,2),(0,3),(1,2),(1,3))), 63]
    counts = [mass(obj) for obj in objects]
    assert counts == [0, 1, 2, 3]
    epsilon, steps = F(1, 8), 10
    initial = {(0,0): QComplex(F(3,5)), (0,1): QComplex(0,F(4,5))}
    profiles = [(str(count), lambda site, count=count: count) for count in counts]
    profiles.append(('prescribed_nonuniform_count', lambda site: abs(site)%4))
    for label, profile in profiles:
        state = initial
        for tick in range(1, steps+1):
            state = exact_step(state, profile, epsilon)
            assert sum(value.norm2() for value in state.values()) == 1
            assert all(abs(site) <= tick for site, _ in state)
        for _ in range(steps):
            state = exact_step(state, profile, epsilon, inverse=True)
        assert state == initial, label
    state = {(0,0): ONE}
    for _ in range(steps):
        state = exact_step(state, lambda site: 0, epsilon)
    assert state == {(steps,0): ONE}
    # Different counts now change probabilities, rather than only a global phase.
    one = exact_step({(0,0): ONE}, lambda site: 1, epsilon)
    two = exact_step({(0,0): ONE}, lambda site: 2, epsilon)
    assert {k:v.norm2() for k,v in one.items()} != {k:v.norm2() for k,v in two.items()}
    return {'arithmetic': 'Gaussian rational, exact', 'epsilon': str(epsilon),
            'steps': steps, 'graph_counts': counts, 'norm_and_inverse': True,
            'nonuniform_profile': 'prescribed background only; no graph conversion dynamics',
            'zero_count_chiral_translation': True, 'count_changes_probabilities': True}


def multiply(a, b):
    return [[sum(a[i][q]*b[q][j] for q in range(2)) for j in range(2)] for i in range(2)]


def matrix_power(matrix, n):
    result = [[1+0j,0j],[0j,1+0j]]
    while n:
        if n%2:
            result = multiply(result, matrix)
        matrix = multiply(matrix, matrix)
        n //= 2
    return result


def numerical_limit_checks():
    records = []
    # Fixed time T=1 and bounded physical momenta; no high-momentum convergence claimed.
    for steps in (20, 40, 80, 160, 320):
        epsilon, max_error, max_energy_error = 1/steps, 0.0, 0.0
        for m in (0,1,2,3,4):
            a = epsilon*m/2
            c, b = (1-a*a)/(1+a*a), -2j*a/(1+a*a)
            for p in (-2,-0.5,0,0.5,2):
                phase = cmath.exp(-1j*epsilon*p)
                walk = [[phase*c,phase*b],[phase.conjugate()*b,phase.conjugate()*c]]
                actual = matrix_power(walk, steps)
                energy = math.hypot(p,m)
                factor = math.sin(energy)/energy if energy else 1
                expected = [[math.cos(energy)-1j*factor*p,-1j*factor*m],
                            [-1j*factor*m,math.cos(energy)+1j*factor*p]]
                error = math.sqrt(sum(abs(actual[i][j]-expected[i][j])**2
                                      for i in range(2) for j in range(2)))
                max_error = max(max_error, error)
                cosine = max(-1.0,min(1.0,math.cos(epsilon*p)*c))
                walk_energy = math.acos(cosine)/epsilon
                max_energy_error = max(max_energy_error,abs(walk_energy-energy))
        records.append({'ticks_per_unit_time':steps, 'epsilon':epsilon,
                        'max_propagator_frobenius_error':max_error,
                        'max_positive_energy_error':max_energy_error})
    assert all(b['max_propagator_frobenius_error'] < a['max_propagator_frobenius_error']
               for a,b in zip(records,records[1:]))
    assert all(b['max_positive_energy_error'] < a['max_positive_energy_error']
               for a,b in zip(records,records[1:]))
    assert records[-1]['max_propagator_frobenius_error'] < 0.012
    return {'time':1, 'masses':[0,1,2,3,4], 'momenta':[-2,-0.5,0,0.5,2],
            'arithmetic':'floating point diagnostic; symbolic generator is checked separately',
            'records':records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    results = {'symbolic':symbolic_checks(), 'exact_walk':exact_walk_checks(),
               'continuum_comparison':numerical_limit_checks(),
               'status':'Dirac bridge under added coin/count coupling; no Einstein field dynamics'}
    if args.output:
        args.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
    print('Symbolic Dirac bridge, exact rational norm/inverse/locality, and numerical limit checks passed.')


if __name__ == '__main__':
    main()
