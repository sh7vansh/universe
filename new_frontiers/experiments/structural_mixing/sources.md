# Primary sources and structural choices for additive directional mixing

Date: 2026-10-07. Question: can one equal contribution per independent graph
cycle explain the Dirac mixing coefficient, with the overall scale treated as
a choice of units? Source-backed statements are cited below. Proposed
couplings and elementary calculations are explicitly identified as ours.

## What the established Dirac constructions determine

Arrighi, Facchini, and Forets define the direction-mixing coin

\[
C_\varepsilon=\exp(-i\varepsilon m\sigma_x)
\]

in natural units. Combined with conditional translation, it has the Dirac
equation as its continuum limit. The particle mass remains an input
coefficient; there is no cycle-space assignment in this construction.
[Discrete Lorentz covariance for Quantum Walks and Quantum Cellular Automata,
Sec. II.A, Eqs. (1), (6)–(7)](https://arxiv.org/pdf/1404.4499).

D'Ariano and Perinotti derive a local coupling of two Weyl automata from
unitarity and locality. Their Dirac automaton has blocks

\[
\begin{pmatrix}nA(k)&imI\\imI&nA(k)^\dagger\end{pmatrix},
\qquad n^2+m^2=1.
\]

Their symmetry assumptions constrain this form, while the coupling magnitude
remains a parameter. The one-dimensional reduction has the same freedom.
[Derivation of the Dirac Equation from Principles of Information Processing,
Sec. V, Eq. (36), Sec. VI.B, and Appendix B](https://arxiv.org/pdf/1306.1934).
An analytic solution of the one-dimensional automaton explicitly treats an
arbitrary mass parameter.
[Path-integral solution of the one-dimensional Dirac quantum cellular
automaton, abstract and Sec. II](https://arxiv.org/pdf/1406.1021).

Thus these results justify identifying directional mixing with relativistic
mass in their stated limits. They do not select the value of that mixing
from this project's structural count.

## A cycle count that needs no chosen cycle basis

For a connected undirected graph, choose an arbitrary orientation and let
\(B\) be its signed vertex–edge incidence matrix. The real cycle space is
\(Z=\ker B\); incidence rank is \(|V|-1\), hence
\(\dim Z=|E|-|V|+1\). A spanning tree supplies a fundamental cycle basis,
but the subspace itself does not require choosing that tree.
[Synchronization of Coupled Phase Oscillators with Stochastic Disturbances
and the Cycle Space of the Graph, Lemma 2.1 and Definition 2.2](https://epubs.siam.org/doi/full/10.1137/22M1489502).

Our elementary extension: use the standard inner product on edge space and
the orthogonal projection \(P_Z\) onto \(Z\). Then

\[
M=\operatorname{Tr}(P_Z)=\operatorname{Tr}(I_Z).
\]

This trace is unchanged by relabelling or reversing edge orientations.
It is additive under direct sums of cycle spaces. It gives a canonical count,
with no ordering of cycles and no distinguished loop.

For a graph regarded strictly as a one-dimensional complex, the edge Hodge
operator is \(L_1=B^\mathsf{T}B\). Our calculation gives
\(\langle z,L_1z\rangle=\|Bz\|^2=0\) for every \(z\in Z\). Its harmonic
cycle modes therefore have zero eigenvalue; the count is the multiplicity
of zero modes, not a nonzero frequency. General Hodge decomposition separates
gradient, curl, and harmonic flows.
[Statistical ranking and combinatorial Hodge theory, Secs. 4–5](https://arxiv.org/pdf/0811.1067).

Do not silently fill triangles with two-dimensional faces. That introduces
an upper boundary operator and can remove triangle cycles from harmonic
homology. The graph cycle space used here keeps every edge cycle.

## Two different ways to use the same internal space

The following are our model comparisons, not claims made by the papers.

1. **Degenerate internal channels.** On \(Z\otimes\mathbb C^2\), choose
   \(H_{\rm mix}=gI_Z\otimes\sigma_x\). Every internal channel has the same
   direction mixing \(g\), independently of \(M\). For a normalized internal
   state \(\rho\),
   \(\operatorname{Tr}_Z[(\rho\otimes I)H_{\rm mix}]=g\sigma_x\).
2. **Extensive collective coupling.** Define the Hamiltonian on the common
   direction factor by
   \(H_{\rm mix}=g\operatorname{Tr}(I_Z)\sigma_x=gM\sigma_x\).
   This uses all internal dimensions as additive contributions to one common
   mixing generator. The unnormalized operator trace is an added coupling
   prescription; it is not the reduced dynamics obtained by tracing a
   normalized internal state in the first model.

Both use the basis-free identity on the same cycle space. Only the second
produces count-dependent mass. A one-particle superposition across \(M\)
orthogonal modes and \(M\) occupied constituents are also different physical
states. Counting available modes alone does not imply that all are occupied
or that their effects add to one direction spinor.

## The useful composition principle

Our proposed selection principle is to assume count is sufficient for the
coin and impose, on one shared two-dimensional direction space,

\[
C_0(\varepsilon)=I,\qquad
C_{n+r}(\varepsilon)=C_n(\varepsilon)C_r(\varepsilon),\qquad
C_n(0)=I.
\]

Induction gives \(C_n(\varepsilon)=C_1(\varepsilon)^n\). Differentiating at
zero gives \(C_n'(0)=nC_1'(0)\). Thus if the elementary generator is
\(-ig\sigma_x\), the count-\(n\) generator is \(-ign\sigma_x\), without
postulating a separate mass coefficient for every count. This conclusion
needs differentiability, but no global one-parameter time-group assumption.

If additionally \(C_1(t+s)=C_1(t)C_1(s)\) and continuity hold, unitary group
theory supplies a self-adjoint generator and an exponential evolution.
[Teschl, Mathematical Methods in Quantum Mechanics, Sec. 5.1,
Theorem 5.3](https://radon.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf).
Then the elementary \(\sigma_x\) generator gives the exact exponential
\(C_n(t)=\exp(-itgn\sigma_x)\).

Count composition is a proposal about how structural parts act on the same
direction factor. Ordinary composition of independent Hilbert spaces uses
tensor products, so this shared-factor multiplication must be specified.
Graph-isomorphism invariance alone does not imply count sufficiency: it also
allows dependence on cycle lengths, degrees, weights, and nonzero spectra.
The elementary generator's mixing axis and coherent sign are further data.
Choosing a generator transverse to \(\sigma_z\) makes a Dirac mass term;
a scalar identity generator only gives a common phase. A common transverse
phase can be changed by a diagonal spinor-basis transformation preserving
\(\sigma_z\), but channel-dependent phases need not add coherently.

## Consequence for the project

The shortest defensible bridge is **basis-free count + extensive composition
on a common direction factor + one elementary mixing generator**. Its count
dependence follows mathematically; its overall common positive scale can be
used to define time and mass units. The extensive coupling and the common
generator remain the physical content. Neither the graph Hodge operator nor
the existing Dirac-walk symmetry derivations establish them automatically.
