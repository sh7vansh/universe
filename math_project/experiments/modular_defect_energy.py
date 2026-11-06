"""Check what face-rank and Cartan-energy modular defects actually measure."""

from collections import Counter
from itertools import combinations, product
import json

from k6_spin_transport import compatible


def rank(face):
    return 0 if face is None else 5 - len(face)


def meet(a, b):
    if a is None or b is None:
        return None
    union = a | b
    return union if all(compatible(x, y) for x, y in combinations(union, 2)) else None


def join(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return a & b


def defect(a, b):
    return rank(a) + rank(b) - rank(join(a, b)) - rank(meet(a, b))


def cartan(q):
    padded = (0,) + q + (0,)
    return sum((b - a) ** 2 for a, b in zip(padded, padded[1:]))


def run():
    intervals = [(i, j) for i in range(6) for j in range(i + 2, 7)
                 if (i, j) != (0, 6)]
    faces = [None]
    for size in range(len(intervals) + 1):
        for fixed in combinations(intervals, size):
            if all(compatible(a, b) for a, b in combinations(fixed, 2)):
                faces.append(frozenset(fixed))
    assert len(faces) == 198
    histogram = Counter()
    for a, b in product(faces, repeat=2):
        delta = defect(a, b)
        histogram[delta] += 1
        assert delta == defect(b, a)
        # With E=rank and an overlap correction, the interaction remainder is -Delta.
        interaction = rank(join(a, b)) - (rank(a) + rank(b) - rank(meet(a, b)))
        assert interaction == -delta
        if a == b:
            assert delta == 0
        if join(a, b) == a or join(a, b) == b:
            assert delta == 0
    incompatible_facets = (frozenset({(0, 2)}), frozenset({(1, 3)}))
    assert defect(*incompatible_facets) == 3
    # The two-state kernel [[0,3],[3,0]] has a negative quadratic direction.
    assert 2 * 1 * (-1) * defect(*incompatible_facets) == -6

    vectors = list(product((-1, 0, 1), repeat=4))
    for a, b in product(vectors, repeat=2):
        upper = tuple(max(x, y) for x, y in zip(a, b))
        lower = tuple(min(x, y) for x, y in zip(a, b))
        delta_q = cartan(a) + cartan(b) - cartan(upper) - cartan(lower)
        positive = [max(x - y, 0) for x, y in zip(a, b)]
        negative = [max(y - x, 0) for x, y in zip(a, b)]
        formula = 2 * sum(positive[i] * negative[i + 1] +
                          negative[i] * positive[i + 1] for i in range(3))
        assert delta_q == formula >= 0
    return {
        "completed_K6_faces": len(faces),
        "ordered_face_pairs_checked": len(faces) ** 2,
        "face_rank_defect_histogram": dict(sorted(histogram.items())),
        "rank_energy_interaction_remainder": "-Delta (exact)",
        "positive_semidefinite_energy_kernel": False,
        "cartan_vector_pairs_checked": len(vectors) ** 2,
        "cartan_energy_defect": "nonnegative; measures energy nonadditivity, not total energy",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
