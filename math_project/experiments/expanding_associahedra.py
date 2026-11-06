"""Check nested surrounding-group embeddings and their dynamical limits."""

from itertools import combinations
import json

from k6_spin_transport import right_rotations, spans, trees


def compatible(a, b):
    i, j = a
    k, l = b
    return j <= k or l <= i or i <= k <= l <= j or k <= i <= j <= l


def vertex_defect(a, b, n):
    return 0 if a == b else 3 - n + len(spans(a)[1] & spans(b)[1])


def run():
    counts = []
    embeddings = []
    completion_stages = []
    inherited_vertices, inherited_edges = set(), set()
    for n in range(6, 10):
        vertices = trees(n)
        vertex_set = set(vertices)
        outgoing = {t: right_rotations(t) for t in vertices}
        degrees = {t: len(outgoing[t]) for t in vertices}
        for destinations in outgoing.values():
            assert destinations <= vertex_set
            for t in destinations:
                degrees[t] += 1
        assert set(degrees.values()) == {n - 2}
        edges = sum(map(len, outgoing.values()))
        assert edges == (n - 2) * len(vertices) // 2
        facets = sum(1 for i in range(n) for j in range(i + 2, n + 1)
                     if (i, j) != (0, n))
        counts.append({"K": n, "dimension": n - 2, "vertices": len(vertices),
                       "edges": edges, "facets": facets})
        # User's completion-triggered growth: retain every completed relation.
        index = {t: i for i, t in enumerate(vertices)}
        all_edges = {frozenset((t, u)) for t, targets in outgoing.items() for u in targets}
        completed_vertices = set(inherited_vertices)
        completed_edges = set(inherited_edges)
        assert completed_vertices <= vertex_set and completed_edges <= all_edges
        if not completed_vertices:
            completed_vertices.add(vertices[0])
        new_vertices = len(vertex_set - completed_vertices)
        new_relations = len(all_edges - completed_edges)
        pending = sorted(all_edges - completed_edges,
                         key=lambda edge: sorted(index[t] for t in edge))
        processed = 0
        while pending:
            frontier = next((i for i, edge in enumerate(pending)
                             if edge & completed_vertices), None)
            assert frontier is not None  # Connected graph supplies a reachable next step.
            assert not (completed_vertices == vertex_set and completed_edges == all_edges)
            edge = pending.pop(frontier)
            completed_vertices.update(edge)
            completed_edges.add(edge)
            processed += 1
        ready_to_grow = completed_vertices == vertex_set and completed_edges == all_edges
        assert ready_to_grow
        assert processed == new_relations
        completion_stages.append({"K": n, "new_vertices_to_complete": new_vertices,
                                  "new_relations_to_complete": new_relations,
                                  "completion_steps": processed,
                                  "append_next_x_only_after_complete": ready_to_grow})
        inherited_vertices = {(t, "x") for t in completed_vertices}
        inherited_edges = {frozenset((t, "x") for t in edge) for edge in completed_edges}
        if n == 9:
            continue
        embedded = {(t, "x") for t in vertices}
        bigger = set(trees(n + 1))
        assert embedded <= bigger
        assert all((0, n) in spans(t)[1] for t in embedded)
        all_facet_vertices = {t for t in bigger if (0, n) in spans(t)[1]}
        assert all_facet_vertices == embedded
        for t in vertices:
            mapped_rotations = {(u, "x") for u in outgoing[t]}
            bigger_rotations = right_rotations((t, "x"))
            assert bigger_rotations & embedded == mapped_rotations
            assert len(bigger_rotations - embedded) == 1
        pair_checks = 0
        for a, b in combinations(vertices, 2):
            assert vertex_defect(a, b, n) == vertex_defect((a, "x"), (b, "x"), n + 1)
            pair_checks += 1
        # Old intrinsic degree n-2; full graph's degree n-1. Thus both
        # ordinary and uniform-negative-link Laplacian principal blocks shift by I.
        embeddings.append({"from": n, "to": n + 1,
                           "facet_vertex_count": len(embedded),
                           "vertex_defect_pairs_preserved": pair_checks,
                           "extra_external_neighbor_per_old_vertex": 1,
                           "full_laplacian_principal_block": "old intrinsic operator + I"})
    return {"counts": counts, "embeddings": embeddings,
            "completion_triggered_growth": completion_stages,
            "interpretation": "Dimension increases with arity; this alone does not specify physical spatial expansion."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
