"""Enumerate K6 and test the proposed spin transport on every 2D face.

This tests a mathematical toy model, not experimental evidence for spin.
Added assumptions: right/left rotations transport by (-1)**sign, and
two routes are coherently recombined with balanced amplitudes and no
additional relative phase. The other output port completes normalization.
Run with: python3 math_project/experiments/k6_spin_transport.py
"""

from functools import lru_cache
from itertools import combinations
import json


@lru_cache(None)
def trees(n):
    if n == 1:
        return ("x",)
    return tuple((a, b) for k in range(1, n)
                 for a in trees(k) for b in trees(n - k))


def right_rotations(t):
    if t == "x":
        return set()
    left, right = t
    out = {(u, right) for u in right_rotations(left)}
    out.update((left, u) for u in right_rotations(right))
    if left != "x":
        a, b = left
        out.add((a, (b, right)))
    return out


def spans(t, start=0, root=True):
    if t == "x":
        return start + 1, frozenset()
    middle, left = spans(t[0], start, False)
    end, right = spans(t[1], middle, False)
    own = frozenset() if root else frozenset({(start, end)})
    return end, left | right | own


def compatible(a, b):
    i, j = a
    k, l = b
    return j <= k or l <= i or i <= k <= l <= j or k <= i <= j <= l


def directed_paths(source, target, adjacency):
    if source == target:
        return [(source,)]
    return [(source,) + path for neighbor in adjacency[source]
            for path in directed_paths(neighbor, target, adjacency)]


def transport(sign):
    return 1 if sign % 2 == 0 else -1


def run():
    vertices = trees(6)
    graph = {t: right_rotations(t) for t in vertices}
    brackets = {t: spans(t)[1] for t in vertices}
    intervals = [(i, j) for i in range(6) for j in range(i + 2, 7)
                 if (i, j) != (0, 6)]
    assert len(vertices) == 42
    assert sum(map(len, graph.values())) == 84
    assert len(intervals) == 14
    # Each rotation replaces one of the four proper brackets: defect zero.
    assert all(len(brackets[t] & brackets[u]) == 3
               for t in vertices for u in graph[t])

    counts = {"pentagon": 0, "square": 0}
    examples = {}
    # Dimension = 4 - number of fixed proper brackets. Enumerate all 2D faces.
    for a, b in combinations(intervals, 2):
        if not compatible(a, b):
            continue
        face = {t for t in vertices if {a, b} <= brackets[t]}
        adjacency = {t: graph[t] & face for t in face}
        sources = [t for t in face if not any(t in adjacency[u] for u in face)]
        sinks = [t for t in face if not adjacency[t]]
        assert len(sources) == len(sinks) == 1
        # Check this induced face really is a cycle.
        assert all(len(adjacency[t]) + sum(t in adjacency[u] for u in face) == 2
                   for t in face)
        paths = directed_paths(sources[0], sinks[0], adjacency)
        assert len(paths) == 2
        lengths = sorted(len(p) - 1 for p in paths)
        kind = {4: "square", 5: "pentagon"}[len(face)]
        assert lengths == ([2, 2] if kind == "square" else [2, 3])
        loop_sign = lengths[0] - lengths[1]
        factors = [transport(length) for length in lengths]
        bright = ((factors[0] + factors[1]) / 2) ** 2
        dark = ((factors[0] - factors[1]) / 2) ** 2
        assert bright + dark == 1
        assert bright == (1 if kind == "square" else 0)
        assert transport(loop_sign) * transport(-loop_sign) == 1
        assert transport(2 * loop_sign) == 1
        counts[kind] += 1
        examples[kind] = {
            "right_rotation_route_lengths": lengths,
            "relative_loop_sign": loop_sign,
            "route_spinor_factors": factors,
            "balanced_output_probabilities": {"bright": bright, "dark": dark},
        }
    assert counts == {"pentagon": 28, "square": 28}
    return {
        "model": "K6 rotation graph with added parity spinor transport",
        "vertices": len(vertices),
        "edges": sum(map(len, graph.values())),
        "facets": len(intervals),
        "two_dimensional_faces_tested": counts,
        "results": examples,
        "scope": "Exact combinatorial check under balanced coherent-route assumptions; no physical spin derivation.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
