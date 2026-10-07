# Does the framework select its own travel rule?

This addresses the open question in the [moving-pair experiment](../mobile_defects/README.md):
can the lattice determine the propagation law that was previously supplied?

**Result:** the existing order, rank, defect, and composition conditions do not
select a unique travel rule. Even after adding probability conservation,
reversibility, and relabelling symmetry, different nontrivial rules remain.
A small package of extra mathematical principles can select a rule, and one
such principle recovers the previous balanced direction mixer. Those principles
are additional axioms; they have not been derived from the existing framework.

There is also a proved restriction: a phase depending only on submodular defect
cannot decorate lattice join or meet associatively for every overlapping input
unless it is trivial on every defect that occurs.

## Artifacts and checks

- [Exact experiment](run.py), standard library only.
- [Exact results](results.json).
- [Lean proofs](../../../math_project/MathProject/TravelRuleSelection.lean).

Run from the repository root:

```bash
python3 -m new_frontiers.experiments.travel_rule_selection.run \
  --output new_frontiers/experiments/travel_rule_selection/results.json
cd math_project
lake build MathProject.DefectMassExploration
lake env lean MathProject/TravelRuleSelection.lean
```

The finite experiment checks exact probability conservation, inverse evolution,
generator relabelling, additive phase composition, local reflections, and all
512 ordered triples in the triangle's edge-set lattice. The Lean module proves
the join/meet restrictions and scalar parameter-selection results. The general
matrix symmetry classification below is a mathematical argument, not a full
matrix theorem in Lean.

## 1. What the current structure determines

The lattice supplies objects, comparability, meet, join, and a valuation once a
submodular rank has been specified. For a locally finite poset, its covering
relations also determine a neighbor graph. These data constrain the defect.

The travel monoid supplies an additive cost and integer label. Its concatenation
law constrains how labels combine. It does not choose how a label becomes an
amplitude or a propagation operator. For example, for any unit complex number z,

\[
\chi_z(n)=z^n,\qquad \chi_z(n+m)=\chi_z(n)\chi_z(m),\qquad \chi_z(0)=1.
\]

Every such character satisfies the same additive label law. Choosing z=-1 or
z=i gives two nontrivial choices. Both are exact, discrete-algebraic phase rules.
Neither requires SI units or continuous-time evolution. Avoiding measured
constants therefore does not remove the choice.

## 2. Same structure, different observable predictions

Use the three edges of a triangle as generators. Its eight edge subsets form
a Boolean lattice. The rank is min(number of edges, 2), and accumulated mass
is number of edges minus rank. Only the full triangle has mass one.

Its undirected cover graph is a cube, with three neighbors at each object.
Use the same direction mixer in both tests:

\[
G_3=\frac13\begin{pmatrix}-1&2&2\\2&-1&2\\2&2&-1\end{pmatrix}.
\]

A state retains the current subset and which generator direction it uses.
At each step it gets phase z to the power of its current mass, receives the
mixer, and toggles the generator indicated by the resulting direction.
The initial subset is empty and the three initial direction amplitudes are
equal. The two tests differ only in z.

| Defect phase | Probability of returning to the empty subset after six steps |
|---|---|
| Sign: z=-1 | 58081/59049, about 98.4% |
| Quarter turn: z=i | 39265/59049, about 66.5% |

Both rules conserve probability exactly, have an exact inverse, preserve every
permutation of the three generators, and respect additive phase composition.
Both have a nontrivial response to a unit defect. Thus the listed consistency
conditions do not determine the measured probability.

This experiment uses the cover graph of the state lattice, rather than adding
a separate spatial line. It still adds an amplitude space, a clock, direction
records, and permission to traverse covers in both directions. Downward moves
are not arrows of the original upward thin category. This is a reversible walk
on its underlying graph, not a claim that the poset category already contains
unitary time evolution.

## 3. Strict associative composition imposes a stronger restriction

One possible attempt to derive an interaction directly from the lattice is
to define a phase-weighted join on basis vectors:

\[
|A\rangle\star|B\rangle=
\chi(\Delta(A,B))|A\vee B\rangle,\qquad \chi(0)=1.
\]

Strict associativity requires

\[
\chi(\Delta(A,B))\chi(\Delta(A\vee B,C))=
\chi(\Delta(B,C))\chi(\Delta(A,B\vee C)).
\]

Choose C=A join B. Every defect in this equation except Delta(A,B) is zero,
because its arguments are comparable. Hence chi(Delta(A,B))=1 for every A,B.
The same argument for meet uses C=A meet B. Both statements are proved in Lean.

A concrete example uses A as two triangle edges, B as the missing edge, and C
as the complete triangle. Combining A and B first creates defect one; combining
B and C first creates no new defect. The two bracketings give phase z and phase
one. The finite experiment finds 24 failures of the corresponding integer
defect associativity equation among the 512 triples.

This restriction is specific to that attempted scalar decoration of join or
meet. It does not rule out quantum dynamics with separate histories, a richer
state space, or additional associativity data. The earlier unitary walks were
not defined by that binary product and do not violate this theorem.

For pairwise disjoint sets, all four meet ranks are zero, and the defects do
obey the additive associativity equation. All 64 pairwise disjoint triples in
this lattice pass. But in that setting assembly action telescopes to an endpoint
invariant, as established in the first experiment. Restricting to disjoint
assembly resolves this consistency problem without selecting a travel law.

## 4. Extra principles can select a rule

Here is one explicit selection problem. At a vertex with d neighbors, add these
requirements for its direction mixer:

1. Treat all neighbor directions symmetrically.
2. Preserve the uniform direction vector.
3. Applying the mixer twice returns the original direction state.
4. The mixer is not the identity.

These are stronger than reversibility. A reversible operator need not be its
own inverse. Full neighbor symmetry is also stronger than the automorphisms of
an arbitrary ranked poset; neighbors with different target ranks need not be
interchangeable. It is an added modeling principle.

For d>=2, a matrix commuting with all neighbor permutations has the form
a I + b J, where J has every entry one. The uniform vector has eigenvalue
a+d b, and its orthogonal complement has eigenvalue a. Requirements 2 and 3
give a+d b=1 and a^2=1. Requirement 4 selects a=-1, and therefore b=2/d:

\[
\boxed{G_d=\frac2d J-I.}
\]

This is the Grover reflection. Its coefficients depend only on the neighbor
count. The experiment checks degrees 2, 3, and 6 exactly. The scalar conclusion
is proved in Lean as `reflection_parameters`.

A similar extra requirement can select the sign phase. Require phase composition
to respect addition, require two units of defect to restore the phase, and require
one unit to have a nonidentity effect. Then the one-unit phase is -1, and
chi(n)=(-1)^n. The integer-valued version is proved in Lean as
`involutive_nontrivial_phase_unique`.

Once the graph, rank, amplitude interpretation, and these extra requirements
are fixed, S G D is a parameter-free candidate walk. Its factors are determined
by those choices. The axioms still need motivation. Choosing this candidate
does not prove that it describes gravity or quantum matter.

## 5. The earlier balanced mixer can also be characterized

On a two-neighbor line, G_2 merely exchanges the directions. It creates no
branching from a single direction state. That reflection is not the balanced
mixer used in the moving-pair experiment.

To recover that mixer, replace requirement 3 by a different principle:
**two mixer substeps implement the reflection**. Keep neighbor symmetry and
preservation of the uniform vector.

Let P=J/d be the projection onto the uniform direction. Every such unitary mixer
can have the form

\[
C_\xi=P+\xi(I-P),\qquad |\xi|=1.
\]

Requiring C_xi squared = G_d forces xi squared = -1, so xi is either i or -i.
The two choices are inverses. With the additional choice xi=i and d=2, this gives

\[
C_i=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix},
\]

exactly the earlier balanced mixer. Thus its numerical entries need not be
independently assigned once a half-reflection principle is supplied. Choosing
that principle, and then the phase orientation, remains an extra step.
The experiment checks C_i squared = C_minus_i squared = G_2 exactly; Lean proves
that the equation xi squared = -1 has only those two complex solutions.

With only unitary evolution, neighbor exchange symmetry, and uniform-vector
preservation, xi is unrestricted on the unit circle. The experiment exhibits
identity, direction exchange, both balanced mixers, and an unequal splitter,
all satisfying those weaker conditions. They give different direction
probabilities from the same input.

## 6. What has been established

The framework already supplies useful constraints and can support quantum
travel models. It currently supplies no axiom that selects a phase character,
a direction mixer, or a discrete clock step. This is a statement about the
present definitions and the tested constraints, not a claim that no canonical
construction can ever be made from a poset.

The new selection principles show a route to a stronger theory: state a small
set of structural laws, derive their allowed operators, and test the consequences.
They also expose costs. A sign phase only records parity; a full reflection
on a line is deterministic; a half-reflection still needs a phase orientation.

The question that remains is which such law is part of the proposed universe,
and why its categorical structure requires that law. The successful binding
experiment can then become a consequence of stated axioms rather than an
example chosen from a family of consistent walks.

The [structural-law candidate](../proposed_universe/README.md) now carries out that step:
it states the added laws, derives their motion, tests defect against inertia,
and examines a separate Cartan source-field extension and an internal-clock
repair.
