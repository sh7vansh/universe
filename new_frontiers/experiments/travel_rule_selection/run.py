"""Exact tests of whether the lattice conditions determine a travel rule.

Run: python3 -m new_frontiers.experiments.travel_rule_selection.run
Optional artifact: --output new_frontiers/experiments/travel_rule_selection/results.json
Standard library only. No continuum-time evolution or particle data.
"""

import argparse
from fractions import Fraction as F
from itertools import permutations, product
import json
from pathlib import Path

from .._shared.exact import QComplex, ZERO, ONE, check_unitary, apply, times, plus, conjugate


def rank(s):
    # Graphic rank of the three edges of a triangle.
    return min(s.bit_count(), 2)


def mass(s):
    return s.bit_count() - rank(s)


def defect(a, b):
    return rank(a) + rank(b) - rank(a | b) - rank(a & b)


def mixer_family():
    examples = [('identity', ONE), ('swap', QComplex(-1)),
                ('balanced', QComplex(0, 1)), ('inverse_balanced', QComplex(0, -1)),
                ('unequal_split', QComplex(F(3, 5), F(4, 5)))]
    rows = []
    for name, xi in examples:
        a, b = F(1, 2) * (ONE + xi), F(1, 2) * (ONE - xi)
        coin = ((a, b), (b, a))
        check_unitary(coin)
        assert apply(coin, (ONE, ONE)) == (ONE, ONE)
        for n, m in product(range(-4, 5), repeat=2):
            assert xi**(n + m) == xi**n * xi**m
        squared = tuple(apply(coin, column) for column in zip(*coin))
        involutive = squared == ((ONE, ZERO), (ZERO, ONE))
        rows.append({'name': name, 'xi': str(xi), 'probabilities_from_R': [str(a.norm2()), str(b.norm2())],
                     'involutive': involutive,
                     'square_root_of_swap': squared == ((ZERO, ONE), (ONE, ZERO))})
    return rows


def grover_certificate(degree):
    """The reflection selected by uniform-neighbor and involution principles."""
    matrix = tuple(tuple(QComplex(F(2, degree) - (1 if i == j else 0)) for j in range(degree))
                   for i in range(degree))
    check_unitary(matrix)
    assert apply(matrix, (ONE,) * degree) == (ONE,) * degree
    assert tuple(apply(matrix, column) for column in zip(*matrix)) == tuple(
        tuple(ONE if i == j else ZERO for j in range(degree)) for i in range(degree))
    assert apply(matrix, (ONE, -ONE) + (ZERO,) * (degree - 2)) == (-ONE, ONE) + (ZERO,) * (degree - 2)
    return {'degree': degree, 'diagonal': str(F(2, degree) - 1),
            'off_diagonal': str(F(2, degree)),
            'probabilities_from_one_neighbor': [str(z.norm2()) for z in apply(matrix, (ONE,) + (ZERO,) * (degree - 1))]}


def cube_step(state, phase, inverse=False):
    # G_3 has diagonal -1/3 and off-diagonal 2/3. Keep numerator integers.
    result = {}
    for (subset, direction), value in state.items():
        if inverse:
            subset ^= 1 << direction
        if mass(subset):
            value = times(conjugate(phase) if inverse else phase, value)
        for output in range(3):
            coefficient = -1 if output == direction else 2
            key = (subset if inverse else subset ^ (1 << output), output)
            result[key] = plus(result.get(key, (0, 0)), tuple(coefficient * z for z in value))
    return {key: value for key, value in result.items() if value != (0, 0)}


def cube_run(phase, steps=12):
    initial = state = {(0, d): (1, 0) for d in range(3)}
    records = []
    for t in range(steps + 1):
        den = 3 * 9**t
        numerators = [sum(real * real + imag * imag for (s, _), (real, imag) in state.items() if s == subset)
                      for subset in range(8)]
        assert sum(numerators) == den
        records.append({'step': t, 'probabilities': [str(F(n, den)) for n in numerators],
                        'empty_probability': str(F(numerators[0], den)),
                        'cycle_probability': str(F(numerators[7], den))})
        if t < steps:
            state = cube_step(state, phase)
    for _ in range(steps):
        state = cube_step(state, phase, inverse=True)
    scale = 3**(2 * steps)
    assert state == {key: (scale, 0) for key in initial}

    def relabel(state, perm):
        def subset_map(s):
            return sum(1 << perm[d] for d in range(3) if s & (1 << d))
        return {(subset_map(s), perm[d]): value for (s, d), value in state.items()}

    probe = {(7, 1): (1, 2), (3, 0): (-1, 0)}
    for perm in permutations(range(3)):
        assert cube_step(relabel(probe, perm), phase) == relabel(cube_step(probe, phase), perm)
    return records


def associativity_checks():
    for a, b in product(range(8), repeat=2):
        assert defect(a, b) >= 0
    violations, disjoint = 0, 0
    for a, b, c in product(range(8), repeat=3):
        left = defect(a, b) + defect(a | b, c)
        right = defect(b, c) + defect(a, b | c)
        if left != right:
            violations += 1
        if a & b == b & c == a & c == 0:
            assert left == right
            disjoint += 1
    a, b, c = 3, 4, 7
    assert defect(a, b) == 1
    assert defect(a | b, c) == defect(b, c) == defect(a, b | c) == 0
    return {'triples_checked': 512, 'integer_defect_associativity_violations': violations,
            'pairwise_disjoint_triples_checked': disjoint,
            'counterexample': {'A': 'two triangle edges', 'B': 'missing edge', 'C': 'whole triangle',
                             'left_total_defect': 1, 'right_total_defect': 0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = {'mixer_family': mixer_family(),
               'reflection_candidates': [grover_certificate(d) for d in (2, 3, 6)],
               'join_associativity': associativity_checks(), 'cube_rules': {}}
    for label, phase in [('nontrivial_sign', (-1, 0)), ('nontrivial_quarter_turn', (0, 1))]:
        results['cube_rules'][label] = cube_run(phase)
    one = results['cube_rules']['nontrivial_sign'][6]['empty_probability']
    two = results['cube_rules']['nontrivial_quarter_turn'][6]['empty_probability']
    assert one != two
    print('Same triangle lattice, rank, cover graph, mixer, preparation, and six steps:')
    print('Return probability, sign phase:', one)
    print('Return probability, quarter-turn phase:', two)
    print(json.dumps({key: value for key, value in results.items() if key != 'cube_rules'}, indent=2))
    print('All exact probability, reversal, symmetry, additive-phase, reflection, and associativity checks passed.')
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
