"""Exact structural mixing selection and counterexamples.

Requires SymPy. Run with optional --output PATH. No fitted particle parameters.
The response-composition law is an additional principle; graph constructions
show why invariant cycle count by itself does not supply the coupling.
"""

import argparse
from fractions import Fraction as F
from itertools import permutations
import json
from pathlib import Path

import sympy as s

from .._shared.exact import QComplex, ONE, ZERO, check_unitary
from .._shared.coins import rational_coin


def product(a, b):
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(2)), ZERO)
                       for j in range(2)) for i in range(2))


def count_composition_checks():
    identity = ((ONE,ZERO),(ZERO,ONE))
    epsilon = F(1,16)
    elementary = rational_coin(1,epsilon)
    gates = [identity]
    for _ in range(8):
        gates.append(product(gates[-1],elementary))
    for gate in gates:
        check_unitary(gate)
    for n in range(5):
        for r in range(5):
            assert gates[n+r] == product(gates[n],gates[r])
    # The older rational coin with its mass parameter set to M has the same
    # continuum generator, but does NOT have exact count composition.
    assert product(rational_coin(1,epsilon),rational_coin(1,epsilon)) != rational_coin(2,epsilon)
    rows=[]
    for count in range(5):
        direct = rational_coin(count,epsilon)
        nonlinear = rational_coin(count*count,epsilon)
        check_unitary(direct)
        check_unitary(nonlinear)
        rows.append({'count':count,
                     'same_unit_gate_repeated_flip_probability':str(gates[count][1][0].norm2()),
                     'direct_count_coin_flip_probability':str(direct[1][0].norm2()),
                     'nonlinear_count_coin_flip_probability':str(nonlinear[1][0].norm2())})
    # Composition can be exact and periodic. It does not guarantee distinct
    # finite-spacing spectral masses for every count.
    quarter_turn = ((ZERO,QComplex(0,-1)),(QComplex(0,-1),ZERO))
    periodic=identity
    for _ in range(4):
        periodic=product(periodic,quarter_turn)
    assert periodic==identity
    return {'arithmetic':'Gaussian rational, exact','epsilon':str(epsilon),
            'count_compositions_checked':25,'unitary_counts_checked':list(range(9)),
            'direct_and_nonlinear_unitary_counts_checked':list(range(5)),
            'previous_rational_count_coin_is_not_exactly_compositional':True,
            'four_quarter_turn_unit_gates_equal_identity':True,'records':rows}


def incidence(vertices,edges):
    matrix=s.zeros(vertices,len(edges))
    for i,(a,b) in enumerate(edges):
        matrix[a,i]=-1
        matrix[b,i]=1
    return matrix


def cycle_projector(boundary):
    columns=boundary.nullspace()
    if not columns:
        return s.zeros(boundary.cols),None
    z=s.Matrix.hstack(*columns)
    return z*(z.T*z).inv()*z.T,z


def graph_checks():
    graphs=[('forest',4,((0,1),(1,2))),
            ('triangle',3,((0,1),(0,2),(1,2))),
            ('square',4,((0,1),(0,3),(1,2),(2,3))),
            ('pentagon',5,((0,1),(0,4),(1,2),(2,3),(3,4))),
            ('square_with_diagonal',4,((0,1),(0,2),(0,3),(1,2),(2,3))),
            ('two_triangles_one_shared_vertex',5,((0,1),(0,2),(0,3),(0,4),(1,2),(3,4))),
            ('complete_K4',4,tuple((a,b) for a in range(4) for b in range(a+1,4)))]
    rows=[]
    for name,vertices,edges in graphs:
        boundary=incidence(vertices,edges)
        projector,z=cycle_projector(boundary)
        count=len(edges)-boundary.rank()
        assert projector.T==projector and projector**2==projector
        assert s.trace(projector)==count
        assert boundary*projector==s.zeros(vertices,len(edges))
        assert boundary.T*boundary*projector==s.zeros(len(edges))
        if count:
            assert z is not None
            basis_change=s.eye(count)
            if count>1:
                basis_change[0,1]=2
            changed=z*basis_change
            assert changed*(changed.T*changed).inv()*changed.T==projector
            x=s.Matrix([[0,1],[1,0]])
            degenerate=s.kronecker_product(s.eye(count),x)
            assert degenerate.eigenvals()=={-1:count,1:count}
            assert (count*x).eigenvals()=={-count:1,count:1}
            assert s.trace(s.eye(count)/count)==1
        relabelings=0
        for perm in permutations(range(vertices)):
            target_edges=tuple(sorted(tuple(sorted((perm[a],perm[b]))) for a,b in edges))
            q=s.zeros(len(edges))
            for i,(a,b) in enumerate(edges):
                mapped=(perm[a],perm[b])
                q[target_edges.index(tuple(sorted(mapped))),i]=1 if mapped[0]<mapped[1] else -1
            target=incidence(vertices,target_edges)
            target_projector,_=cycle_projector(target)
            assert q*q.T==s.eye(len(edges))
            assert target_projector==q*projector*q.T
            relabelings+=1
        laplacian=boundary*boundary.T
        rows.append({'graph':name,'vertices':vertices,'edges':len(edges),
                     'cycle_count':count,'cycle_projector_trace':str(s.trace(projector)),
                     'edge_hodge_operator_annihilates_cycles':True,
                     'basis_and_signed_relabeling_invariance':True,
                     'vertex_relabelings_checked':relabelings,
                     'vertex_laplacian_characteristic_polynomial':str(laplacian.charpoly().as_expr()),
                     'degenerate_channel_masses':[] if not count else [1]*count,
                     'unnormalized_collective_mass':count})
    return rows


def cycle_internal_travel(n):
    edges={tuple(sorted((i,(i+1)%n))) for i in range(n)}
    arcs=tuple(sorted((a,b) for a,b in edges for a,b in ((a,b),(b,a))))
    neighbors={v:{u for a,b in edges for u in ([b] if a==v else [a] if b==v else [])}
               for v in range(n)}
    step=s.zeros(2*n)
    for j,(a,b) in enumerate(arcs):
        other=neighbors[b]-{a}
        assert len(other)==1
        out=(b,next(iter(other)))
        step[arcs.index(out),j]=1
    assert step.T*step==s.eye(2*n)
    assert step**n==s.eye(2*n)
    assert all(step**t!=s.eye(2*n) for t in range(1,n))
    # Check naturality against every graph vertex relabelling; no preferred
    # cycle orientation is used by the two-direction state space.
    for perm in permutations(range(n)):
        mapped_arcs=tuple(sorted((perm[a],perm[b]) for a,b in arcs))
        q=s.zeros(2*n)
        target=s.zeros(2*n)
        for j,(a,b) in enumerate(arcs):
            q[mapped_arcs.index((perm[a],perm[b])),j]=1
        for j,(a,b) in enumerate(mapped_arcs):
            candidates=[c for u,c in mapped_arcs if u==b and c!=a]
            assert len(candidates)==1
            target[mapped_arcs.index((b,candidates[0])),j]=1
        assert target*q==q*step
    return {'cycle_length':n,'cycle_count':1,'directed_edge_states':2*n,
            'exact_period':n,'unitary_and_relabeling_invariant':True,
            'trace_of_step_cubed':str(s.trace(step**3)),
            'characteristic_polynomial':str(step.charpoly().as_expr())}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    results={'composition':count_composition_checks(),'cycle_spaces':graph_checks(),
             'canonical_internal_travel':[cycle_internal_travel(n) for n in (3,4,5)],
             'status':'Count proportionality follows from extra shared-direction composition; cycle space alone does not supply it.'}
    if args.output:
        args.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
    print('Exact composition, cycle projector, relabeling, degenerate-channel, and internal-travel checks passed.')


if __name__=='__main__':
    main()
