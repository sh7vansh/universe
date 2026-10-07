"""Graphic rank, nullity, and defect on subsets of the six edges of K4.

This is the specific complete-graph-on-four-vertices example, not a general
graph algorithm or an assignment of physical particle masses.
"""

from itertools import combinations


EDGES = tuple(combinations(range(4), 2))
STATES = range(1 << len(EDGES))


def graphic_rank(mask):
    """r(S) = |V| - components(V,S); unused vertices count as components."""
    parent = list(range(4))

    def root(vertex):
        while parent[vertex] != vertex:
            vertex = parent[vertex]
        return vertex

    rank = 0
    for index, (a, b) in enumerate(EDGES):
        if mask & (1 << index):
            a, b = root(a), root(b)
            if a != b:
                parent[a] = b
                rank += 1
    return rank


RANK = tuple(graphic_rank(mask) for mask in STATES)


def mass(mask):
    return mask.bit_count() - RANK[mask]


def defect(a, b):
    return RANK[a] + RANK[b] - RANK[a | b] - RANK[a & b]
