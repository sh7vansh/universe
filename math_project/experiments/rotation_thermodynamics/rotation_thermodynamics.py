"""
Rotation thermodynamics on the associahedron
============================================

Builds on thin-category-lattice.md (Sections 3.3, 4.0.1, 5, 6.4).

Three associations, each turned into an executable check:

A. KOLMOGOROV  <->  PENTAGON OBSTRUCTION
   Let right rotations fire at rate p and left rotations at rate q.
   Kolmogorov's criterion: a Markov chain is reversible (has an equilibrium
   energy E with p/q = exp(-dE)) iff the product of rate ratios around every
   cycle is 1.  Around a cycle that product is (p/q)^sigma(cycle).  The paper's
   pentagon loop has sigma = -1, so for every p != q the chain is a
   NON-EQUILIBRIUM steady state with circulating probability currents.
   `pentagon_sign_additive_quotient_trivial` is the statement that no energy
   function can rescue detailed balance.
   Witness: the steady-state "rotation current" J_sigma = <d sigma/dt>.  If sigma
   had a vertex potential h, J_sigma = <dh/dt> = 0 in any stationary state of a
   finite chain.  So J_sigma != 0 is a dynamical proof of non-exactness.

B. LODAY GEOMETRY  =  A COLLISION RULE  (the integrating factor)
   Under a right rotation ((S T) U) -> (S (T U)) the Loday vector changes by
       s*u * (e_i - e_j),   i = gap(S|T) < j = gap(T|U)
   i.e. a positive multiple of a type-A root, with sum(v) conserved.
   Reading gaps as cells and v as occupation: each rotation is a binary
   collision moving s*u quanta from cell j to cell i.  The unit sign sigma
   counts COLLISIONS (path function, like heat); the displacement counts
   MOMENTUM TRANSFER (state function).  The paper's open problem "change the
   edge labels so they respect the path relations" is solved by the root-
   valued label: it is exact by construction.

C. CURVATURE LIVES ON PENTAGONS; CATALAN = OPEN TASEP
   Every 2-face of K_m is a pentagon (flux +-1) or a square (flux 0).
   The open TASEP (exclusion lattice gas, the order-book toy) with
   alpha = beta = 1 has partition function C_{N+1} = #vertices of K_{N+2}.
"""

import itertools
import json
from functools import lru_cache
from math import comb, log
from pathlib import Path

import numpy as np

# ---------------------------------------------------------------------------
# full binary trees on leaves lo..hi-1   (nested tuples, leaf = int)
# ---------------------------------------------------------------------------


@lru_cache(None)
def trees(lo, hi):
    if hi - lo == 1:
        return (lo,)
    out = []
    for mid in range(lo + 1, hi):
        for L in trees(lo, mid):
            for R in trees(mid, hi):
                out.append((L, R))
    return tuple(out)


def leaves(t):
    return 1 if isinstance(t, int) else leaves(t[0]) + leaves(t[1])


def first_leaf(t):
    return t if isinstance(t, int) else first_leaf(t[0])


def right_rotations(t):
    """All trees reachable by one right rotation ((S,T),U)->(S,(T,U)) at any
    subtree.  Returns list of (new_tree, s, u, gap_ST, gap_TU)."""
    if isinstance(t, int):
        return []
    out = []
    L, R = t
    if not isinstance(L, int):
        S, T = L
        s, u = leaves(S), leaves(R)
        g_st = first_leaf(T) - 1  # gap index between S and T
        g_tu = first_leaf(R) - 1
        out.append(((S, (T, R)), s, u, g_st, g_tu))
    for nl, *rest in right_rotations(L):
        out.append(((nl, R), *rest))
    for nr, *rest in right_rotations(R):
        out.append(((L, nr), *rest))
    return out


def loday(t, m):
    v = np.zeros(m - 1, dtype=int)

    def rec(x):
        if isinstance(x, int):
            return
        L, R = x
        v[first_leaf(R) - 1] = leaves(L) * leaves(R)
        rec(L)
        rec(R)

    rec(t)
    return v


def brackets(t):
    """proper bracket intervals [a,b) of size >= 2, excluding the root."""
    out = set()

    def rec(x, root):
        if isinstance(x, int):
            return (x, x + 1)
        a, _ = rec(x[0], False)
        _, b = rec(x[1], False)
        if not root and b - a >= 2:
            out.add((a, b))
        return (a, b)

    rec(t, True)
    return frozenset(out)


# ---------------------------------------------------------------------------
def build(m):
    V = list(trees(0, m))
    idx = {t: i for i, t in enumerate(V)}
    E = []  # (i, j, s, u, gi, gj) for right rotation i -> j
    for t in V:
        for nt, s, u, gi, gj in right_rotations(t):
            E.append((idx[t], idx[nt], s, u, gi, gj))
    return V, idx, E


def check_B(m):
    """Every right rotation displaces the Loday vector by s*u*(e_i - e_j), i<j."""
    V, idx, E = build(m)
    L = np.array([loday(t, m) for t in V])
    total = L.sum(1)
    ok = True
    su_hist = {}
    for i, j, s, u, gi, gj in E:
        d = L[j] - L[i]
        expect = np.zeros(m - 1, dtype=int)
        expect[gi] += s * u
        expect[gj] -= s * u
        ok &= bool(np.array_equal(d, expect)) and gi < gj
        su_hist[s * u] = su_hist.get(s * u, 0) + 1
    return {
        "m_leaves": m,
        "vertices": len(V),
        "edges": len(E),
        "displacement_is_su_times_root": ok,
        "loday_sum_conserved": bool(np.all(total == comb(m, 2))),
        "conserved_sum": int(comb(m, 2)),
        "collision_size_histogram": dict(sorted(su_hist.items())),
    }


def check_A(m, p, q):
    """Biased rotation CTMC: stationary state, currents, entropy production."""
    V, idx, E = build(m)
    n = len(V)
    Q = np.zeros((n, n))
    for i, j, *_ in E:
        Q[i, j] += p
        Q[j, i] += q
    Q -= np.diag(Q.sum(1))
    # stationary distribution: pi Q = 0, sum pi = 1
    A = np.vstack([Q.T, np.ones(n)])
    b = np.zeros(n + 1)
    b[-1] = 1
    pi = np.linalg.lstsq(A, b, rcond=None)[0]
    J = np.array([pi[i] * p - pi[j] * q for i, j, *_ in E])  # net current on right edges
    J_sigma = J.sum()  # <d sigma / dt>
    EP = sum(
        Ji * log((pi[i] * p) / (pi[j] * q)) for Ji, (i, j, *_) in zip(J, E)
    )  # Schnakenberg entropy production
    # Kolmogorov / detailed balance residual
    db = max(abs(Ji) for Ji in J)
    # Loday potential drift (must vanish: it IS a potential)
    Lv = np.array([loday(t, m) for t in V], dtype=float)
    c = np.arange(1, m)  # any functional
    drift_potential = sum(Ji * (c @ (Lv[j] - Lv[i])) for Ji, (i, j, *_) in zip(J, E))
    return {
        "m_leaves": m,
        "p": p,
        "q": q,
        "rotation_current_J_sigma": J_sigma,
        "entropy_production": EP,
        "max_edge_current": db,
        "drift_of_Loday_potential": drift_potential,
        "pi_min_max": (float(pi.min()), float(pi.max())),
    }


def check_C_faces(m):
    """Classify 2-faces of K_m and their Tamari flux (route-length difference)."""
    V, idx, E = build(m)
    B = [brackets(t) for t in V]
    need = (m - 2) - 2  # brackets in a 2-face
    counts = {"pentagon": 0, "square": 0, "other": 0}
    flux = {"pentagon": set(), "square": set()}
    adj = {}
    for i, j, *_ in E:
        adj.setdefault(i, []).append(j)
    seen = set()
    for i in range(len(V)):
        for S in itertools.combinations(sorted(B[i]), need):
            S = frozenset(S)
            if S in seen:
                continue
            seen.add(S)
            verts = [k for k in range(len(V)) if S <= B[k]]
            # directed subgraph restricted to the face
            vs = set(verts)
            sub = {k: [j for j in adj.get(k, []) if j in vs] for k in verts}
            indeg = {k: 0 for k in verts}
            for k in verts:
                for j in sub[k]:
                    indeg[j] += 1
            src = [k for k in verts if indeg[k] == 0][0]
            # all maximal directed path lengths from source to sink
            lengths = set()

            def dfs(k, d):
                if not sub[k]:
                    lengths.add(d)
                for j in sub[k]:
                    dfs(j, d + 1)

            dfs(src, 0)
            kind = {5: "pentagon", 4: "square"}.get(len(verts), "other")
            counts[kind] += 1
            if kind in flux:
                flux[kind].add(max(lengths) - min(lengths))
    return {
        "m_leaves": m,
        "two_faces": counts,
        "flux_values": {k: sorted(v) for k, v in flux.items()},
    }


def check_C_tasep(N):
    """Open TASEP, N sites, alpha = beta = 1.  Return Z / weight(empty)."""
    n = 2**N
    Q = np.zeros((n, n))
    for s in range(n):
        bits = [(s >> k) & 1 for k in range(N)]
        def put(b):
            return sum(x << k for k, x in enumerate(b))
        if bits[0] == 0:  # injection at left
            b = bits.copy(); b[0] = 1; Q[s, put(b)] += 1
        if bits[-1] == 1:  # extraction at right
            b = bits.copy(); b[-1] = 0; Q[s, put(b)] += 1
        for k in range(N - 1):  # hop right
            if bits[k] == 1 and bits[k + 1] == 0:
                b = bits.copy(); b[k], b[k + 1] = 0, 1; Q[s, put(b)] += 1
    Q -= np.diag(Q.sum(1))
    A = np.vstack([Q.T, np.ones(n)])
    rhs = np.zeros(n + 1); rhs[-1] = 1
    pi = np.linalg.lstsq(A, rhs, rcond=None)[0]
    return pi.sum() / pi[0]


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    res = {}
    print("B. Loday displacement = s*u * root, Loday sum conserved")
    res["B"] = []
    for m in range(3, 10):
        r = check_B(m)
        res["B"].append(r)
        print(f"  m={m}: V={r['vertices']:5d} E={r['edges']:6d} root-move={r['displacement_is_su_times_root']} "
              f"sum conserved={r['loday_sum_conserved']} ({r['conserved_sum']})  "
              f"collision sizes={r['collision_size_histogram']}")

    print("\nA. Biased rotations: Kolmogorov failure, currents, entropy production")
    res["A"] = []
    for m in (4, 5, 6, 7, 8):
        for p, q in ((1.0, 1.0), (2.0, 1.0), (5.0, 1.0)):
            r = check_A(m, p, q)
            res["A"].append(r)
            print(f"  m={m} p/q={p/q:3.0f}: J_sigma={r['rotation_current_J_sigma']:+.5f}  "
                  f"EP={r['entropy_production']:.5f}  max|J_e|={r['max_edge_current']:.2e}  "
                  f"Loday drift={r['drift_of_Loday_potential']:+.1e}")

    print("\nC1. 2-faces and their flux (|longest - shortest| directed route)")
    res["C_faces"] = []
    for m in range(4, 9):
        r = check_C_faces(m)
        res["C_faces"].append(r)
        print(f"  K_{m}: {r['two_faces']}  flux={r['flux_values']}")

    print("\nC2. Open TASEP alpha=beta=1:  Z_N / w(empty)  vs  Catalan C_{N+1}")
    res["C_tasep"] = []
    for N in range(1, 11):
        z = check_C_tasep(N)
        cat = comb(2 * (N + 1), N + 1) // (N + 2)
        res["C_tasep"].append({"N": N, "Z": z, "catalan": cat})
        print(f"  N={N:2d}: Z={z:10.4f}   C_(N+1)={cat}")

    with open(Path(__file__).with_name("rotation_thermodynamics_results.json"), "w") as f:
        json.dump(res, f, indent=1, default=float)
