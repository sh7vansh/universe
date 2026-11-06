# Lattice growth, Cartan energy, and Riemann's explicit formula

Research date: 2026-10-15. Companion to [thin-category-lattice.md](../../thin-category-lattice.md).

## Finding and status

There are two exact bridges from ingredients of the paper to the Riemann zeta function:

1. Specialize the paper's least-missing-generator growth to a divisibility lattice. Its logarithmic growth observable is exactly Chebyshev's prime-power counting function. Its Mellin transform is the logarithmic derivative of Riemann zeta, whose inversion gives the classical explicit formula.
2. Take spectral zeta functions of the paper's type-A Cartan matrices. After mesh rescaling, they converge to the spectral zeta function of a Dirichlet interval, which is a rescaled Riemann zeta function.

These are elementary deductions and applications of established analytic number theory. They are not claims of a new explicit formula, a proof of the Riemann hypothesis, or an identification of Koopman eigenvalues with Riemann zeros. The arithmetic specialization, spectral limit, and centered-energy identity below are not new Lean theorems in this repository. The original paper has not been edited.

The current Lean source supplies the abstract starting points: [`fixedPriorityPhi`, `xSeq`, and `novelty_of_fixedPriorityPhi`](../MathProject/FunctorialGeometry.lean), together with `cartanMatrix`, `cartanMatrix_row`, and `cartanEnergy_eq_cartanMatrix`. Its `rootAn_cartan_norm` already proves norm two at every rank, beyond the rank-three discussion in the Markdown paper. This note derives connections from these definitions; it does not report a fresh compilation of the Lean development.

## 1. A precise arithmetic instance of the growth rule

Fix an integer cutoff \(N\ge2\), and put
\[
M_N=\operatorname{lcm}(1,2,\ldots,N),\qquad
L_N=\{d\in\mathbb N_{>0}:d\mid M_N\}.
\]
Order \(L_N\) by divisibility. Then
\[
d\wedge e=\gcd(d,e),\quad d\vee e=\operatorname{lcm}(d,e),
\quad\bot=1,\quad\top=M_N.
\]

Use **all integers** \(2,\ldots,N\) as generators, with their usual numerical priority. They are join-dense: if \(d\mid M_N\), each maximal prime-power factor of \(d\) is at most \(N\), and \(d\) is their least common multiple. The empty join represents \(1\).

The paper's update becomes
\[
q(d)=\min\{m\in\{2,\ldots,N\}:m\nmid d\},\qquad
G_N(d)=\operatorname{lcm}(d,q(d))
\]
when \(d<M_N\), and \(G_N(M_N)=M_N\). Thus the priority rule does not need a precomputed list of primes.

**Proposition.** Every selected generator \(q(d)\) is a prime power, and each update multiplies the state by a prime.

**Proof.** If \(q\) has at least two distinct prime factors, group its maximal prime-power factors into two coprime proper factors \(a,b<q\) with \(q=ab\). By minimality, both \(a\) and \(b\) divide \(d\). Hence \(q=\operatorname{lcm}(a,b)\mid d\), a contradiction. Therefore \(q=p^k\). Minimality gives \(p^{k-1}\mid d\), while \(p^k\nmid d\). The update raises that prime's exponent by exactly one, so \(G_N(d)/d=p\). This argument works for every state, not only the orbit from \(1\).

Starting from \(1\), the successive events are exactly the prime powers in increasing numerical order:

| Selected missing generator | State after adjoining it | Multiplier |
|---:|---:|---:|
| 2 | 2 | 2 |
| 3 | 6 | 3 |
| 4 | 12 | 2 |
| 5 | 60 | 5 |
| 7 | 420 | 7 |
| 8 | 840 | 2 |
| 9 | 2520 | 3 |
| 11 | 27720 | 11 |

After incorporating \(q\), every integer at most \(q\) divides the state, so future selected generators are larger. A future prime power \(p^k\) cannot already divide a least common multiple of smaller integers. This proves the asserted event sequence.

There is also a literal subobject interpretation. A cyclic group of order \(M_N\) has one subgroup of each order \(d\mid M_N\). Intersections correspond to gcd and generated joins to lcm. An update from subgroup order \(d\) to order \(pd\) has quotient a cyclic group of prime order, hence a simple object in the category of abelian groups. This connects the arithmetic instance to the one-simple-cell successor steps in §7.1 as well as the priority rule in §7.2.

The integer valuation \(\Omega(d)=\sum_p v_p(d)\) increases by one at every event and is modular. The real valuation \(\log d\) is modular too, because
\[
de=\gcd(d,e)\operatorname{lcm}(d,e).
\]
Thus this arithmetic lattice has zero defect for those valuations; it should not be identified with the paper's completed associahedral face lattice, where face-rank defects can have either sign.

### A single transfinite subobject model

The finite cutoffs fit inside one literal instance of the paper's complete-lattice construction. Take the abelian group \(U=\mathbb Q/\mathbb Z\), and let
\[
H_m=(\tfrac1m\mathbb Z)/\mathbb Z\subseteq U,\qquad m\ge2.
\]
Each \(H_m\) is cyclic of order \(m\), \(H_a\subseteq H_b\) iff \(a\mid b\), and \(H_a\vee H_b=H_{\operatorname{lcm}(a,b)}\). These generators are join-dense in the full subgroup lattice: an element of order \(m\) generates precisely \(H_m\). Thus every subgroup is a join of the \(H_m\) it contains.

Choose the usual numerical priority on \(m\) and start from the zero subgroup \(H_1\). Every finite stage is \(H_{D(q_j)}\) after \(j\) additions. Its next quotient is cyclic of prime order by the prime-multiplier proposition. At the limit,
\[
C_\omega=\bigvee_{j<\omega}C_j
=\bigcup_{j<\omega}H_{D(q_j)}=\mathbb Q/\mathbb Z.
\]
Indeed, any rational residue has some finite denominator \(m\), and eventually \(m\mid D(q_j)\). No finite stage equals \(U\), so the first top stage is exactly \(\omega\). Also \(U\) is semi-Artinian: any nonzero quotient remains torsion, and a nonzero torsion abelian group has an element of prime order and hence a simple subgroup. This is a concrete transfinite filtration with simple successor quotients, not only a sequence of separate finite lattice examples. These claims follow from the displayed subgroup definitions; they have not been added as Lean declarations.

The observable \(\log|C_j|\) is finite at the finite stages and diverges at \(\omega\). The arithmetic transform below is built from those finite-stage jumps, rather than assigning a finite logarithmic size to \(\mathbb Q/\mathbb Z\).

## 2. The growth observable is exactly the function in the explicit formula

Distinguish two clocks. The **event index** advances only at a prime power; the **arithmetic threshold** advances through every integer, including plateaus. Define
\[
D(x)=\operatorname{lcm}(1,\ldots,\lfloor x\rfloor),\qquad F(x)=\log D(x),\quad x\ge1.
\]
The greedy states are \(D(q_j)\), where \(q_j\) is the \(j\)-th prime power. They are generally not \(D(j)\).

Unique factorization immediately gives
\[
D(x)=\prod_{p\le x}p^{\lfloor\log x/\log p\rfloor},\qquad
\boxed{F(x)=\sum_{p^k\le x}\log p=\psi(x).}
\]
The final expression is the standard Chebyshev function, as defined in [NIST DLMF 25.16.1](https://dlmf.nist.gov/25.16.E1). The equality with logarithmic lattice growth is the elementary deduction above.

If \(\Lambda(n)=\log p\) for \(n=p^k\) and zero otherwise, then
\[
F(n)-F(n-1)=\Lambda(n).
\]
For \(\Re s>1\), its Mellin–Stieltjes transform is
\[
\boxed{\int_{[1,\infty)}x^{-s}\,dF(x)
=\sum_{n\ge1}\Lambda(n)n^{-s}
=-\frac{\zeta'(s)}{\zeta(s)}.}
\]
The first equality follows by summing the jumps; the last is [NIST DLMF 27.4.12](https://dlmf.nist.gov/27.4.E12). Integration by parts also gives \(s\int_1^\infty F(x)x^{-s-1}\,dx\) for the same quantity.

This is an actual Fourier transform in logarithmic coordinates. For fixed \(c>1\), define the finite measure
\[
\mu_c=\sum_{n\ge1}\Lambda(n)n^{-c}\delta_{\log n}.
\]
Using the convention \(\widehat\mu(\tau)=\int e^{-i\tau t}\,d\mu(t)\),
\[
\widehat\mu_c(\tau)=-\frac{\zeta'(c+i\tau)}{\zeta(c+i\tau)}.
\]
This follows directly from the absolutely convergent series. The conjugate coordinate is \(\log n\), not the number of generator additions.

For \(x>1\), let \(F_0(x)=[F(x+)+F(x-)]/2\). The classical explicit formula now reads
\[
\boxed{F_0(x)=x-lim_{T\to\infty}
\sum_{\substack{\rho\text{ nontrivial zero}\\|\Im\rho|\le T}}
\frac{x^\rho}{\rho}
-\log(2\pi)-\frac12\log(1-x^{-2}).}
\]
Count zeros with multiplicity and use the displayed height-symmetric summation. The midpoint convention matters exactly at prime powers. Perron inversion and contour displacement yield the zero terms and corrections; see [Montgomery–Vaughan, Chapter 12, equation (12.1) and Theorem 12.5](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf). No Riemann hypothesis is assumed.

Putting \(x=e^t\), each term \(x^\rho\), with \(\rho=\beta+i\gamma\), becomes \(e^{\beta t}e^{i\gamma t}\). This explains the frequency interpretation of the zero ordinates. It does not make these zeros eigenvalues of \(G_N\).

```mermaid
flowchart LR
  A["Paper's least-missing-generator rule"] --> B["Divisibility + lcm + numerical priority"]
  B --> C["Logarithmic state F = ψ"]
  C --> D["Mellin transform −ζ′/ζ"]
  D --> E["Perron inversion: explicit formula"]
```

## 3. The Cartan matrices give a second exact route

Write \(A_r\) for the paper's rank-\(r\) type-A Cartan matrix, not the associahedron's vertex adjacency matrix. It has eigenpairs
\[
u_k(j)=\sqrt{\frac2{r+1}}\sin\frac{\pi kj}{r+1},\qquad
\lambda_{r,k}=4\sin^2\frac{\pi k}{2(r+1)},\quad 1\le j,k\le r.
\]
These are the discrete Dirichlet interval modes; [Dowker, §7, equation (30)](https://arxiv.org/pdf/1207.2096) gives this spectral description. Their substitution into the tridiagonal matrix also verifies the claim directly. Spectral coordinates are real or complex, extending the paper's integer-coordinate energy.

Use the mesh-normalized matrices and spectral zeta functions
\[
B_r=\frac{(r+1)^2}{\pi^2}A_r,\qquad
Z_r(s)=\operatorname{tr}(B_r^{-s})=\sum_{k=1}^r\mu_{r,k}^{-s}.
\]
All eigenvalues are positive, so powers use the real logarithm. Then
\[
\boxed{\lim_{r\to\infty}Z_r(s)=\zeta(2s),\qquad\Re s>\tfrac12.}
\]

**Proof.** For each fixed \(k\), \(\mu_{r,k}\to k^2\). On \([0,\pi/2]\), \(\sin t\ge2t/\pi\), hence
\[
\mu_{r,k}\ge\frac4{\pi^2}k^2.
\]
For \(\sigma=\Re s>1/2\), this bounds \(|\mu_{r,k}^{-s}|\) by a constant times \(k^{-2\sigma}\), a summable sequence. Extend the summand by zero for \(k>r\) and apply dominated convergence. Bounds uniform on compact subsets give local uniform convergence in this half-plane. Identifying the resulting series uses [NIST's definition of Riemann zeta](https://dlmf.nist.gov/25.2.E1).

In unnormalized interval units, \(\operatorname{tr}(((r+1)^2A_r)^{-s})\to\pi^{-2s}\zeta(2s)\). Thus adding rank must be accompanied by mesh rescaling to obtain this particular continuum limit. Merely appending coordinates without specifying a scale is a different limiting problem.

At \(s=1\), an exact finite identity provides a useful check:
\[
\operatorname{tr}(A_r^{-1})=\frac{r(r+2)}6,\qquad
Z_r(1)=\frac{\pi^2}{6}\left(1-\frac1{(r+1)^2}\right).
\]
Indeed \((A_r^{-1})_{ij}=\min(i,j)-ij/(r+1)\); summing its diagonal proves the formula.

The two bridges therefore meet through an explicit identity. If \(Z_\infty(s)=\zeta(2s)\), then for \(\Re s>1/2\),
\[
\boxed{-\frac12\frac{Z_\infty'(s)}{Z_\infty(s)}
=\int_{[1,\infty)}x^{-2s}\,dF(x).}
\]
This is the logarithmic derivative of a **spectral zeta function**, not the logarithmic derivative of a matrix determinant. It follows from the two separately proved identities. It does not intertwine the arithmetic update with Cartan evolution.

Each finite \(Z_r\) is entire. The convergence proved here is only for \(\Re s>1/2\); it is not a theorem about convergence of zeros in the critical strip. The continued zeros of \(\zeta(2s)\) occur at \(s=\rho/2\), while the underlying eigenvalues are \(k^2\). Zeta zeros and operator eigenvalues remain different objects.

## 4. An explicit energy for the arithmetic growth profile

There is a direct coordinate choice connecting these ingredients without claiming that the paper already fixes it. At thresholds \(0,\ldots,N\), set \(\psi(0)=0\) and
\[
w_j=\psi(j)-\frac jN\psi(N),\quad 0\le j\le N.
\]
Then \(w_0=w_N=0\). Apply the real extension of the paper's Cartan form at rank \(N-1\) to \((w_1,\ldots,w_{N-1})\). Since its increments are \(\Lambda(j)-\psi(N)/N\),
\[
\boxed{Q_{N-1}(w)=\sum_{j=1}^N
\left(\Lambda(j)-\frac{\psi(N)}N\right)^2
=\sum_{j=1}^N\Lambda(j)^2-\frac{\psi(N)^2}{N}.}
\]
Thus the Cartan energy measures the variation in arithmetic growth increments after removing their mean. This variance identity holds for any cumulative sequence; the arithmetic content here is that the increments are \(\Lambda\). The rank \(N-1\) indexes threshold samples, not the root rank associated to the associahedron of the shorter greedy-event chain.

## 5. What Koopman and associahedra do, and do not, add

For the arithmetic growth map, define \(Uf=f\circ G_N\). Every update increases \(\Omega(d)\) by one until reaching \(M_N\). Consequently, for \(K=\Omega(M_N)\),
\[
U^Kf(d)=f(M_N).
\]
In increasing numerical order of divisors, its finite matrix is upper triangular, with a single diagonal entry \(1\) at the top and all others \(0\). Its spectrum is therefore \(\{0,1\}\). The logarithmic step weight is the observable \((U-I)\log d\), but Riemann zeros do not appear as the eigenvalues of this finite matrix. A finite cutoff's arithmetic transform is also just an entire Dirichlet polynomial. The unbounded arithmetic family and analytic continuation are essential to the explicit formula.

A finite event chain with \(m\) arrows has the paper's \(K_m\) bracketing structure. Rebracketing preserves the chain's composite. The logarithmic increments add associatively as well. Using logarithmic costs would require a real-valued target beyond the existing \(\mathbb N\times\mathbb Z\) travel monoid; the current Lean theorem does not already assert this real-valued specialization.

The zeta connection above uses divisibility, ordinary numerical priority, and logarithmic weights. It does not arise from the associahedron's abstract shape alone, its rotation-graph spectrum, or the signed pentagon valuation. A link between those graph spectra and Riemann zeros has not been established here. Likewise, the Cartan spectral limit alone does not determine a growth law or prove RH.

## 6. Reproducible verification

Run `python3 math_project/experiments/riemann_growth.py` with NumPy and mpmath installed. It writes [riemann_growth_results.json](riemann_growth_results.json). All assertions passed on 2026-10-15:

- The least-missing algorithm, with all integer generators, selects all 193 prime powers through 1000, in order. The exact integer lcm states agree with independent prime-exponent reconstructions at every threshold.
- On all 48 divisors of \(M_{10}=2520\), checks verify join density, prime-ratio successor steps, and all 2304 gcd/lcm modular identities. The Koopman matrix reaches its terminal projection in exactly seven steps; its transient part is nilpotent.
- The centered arithmetic profile through 100 has Cartan energy \(233.047388461825\). The independent variance expression agrees within \(3\times10^{-14}\).
- Explicit sine modes satisfy the Cartan eigenvector equations and orthonormality through rank 31 to numerical tolerance. The inverse-trace identity is checked using exact rational arithmetic.
- Spectral sums at ranks 15, 63, 255, and 1023 approach \(\zeta(2s)\) at \(s=1,2,1+i\). At rank 1023, the absolute error for \(s=1\) is approximately \(1.57\times10^{-6}\). These finite numerical comparisons corroborate the analytic dominated-convergence proof, rather than replace it.
- Arithmetic Mellin sums through 10000 agree with \(-\zeta'/\zeta\) at \(s=2,2+i\) within an explicit omitted-tail bound derived from \(0\le\Lambda(n)\le\log n\).

The strongest established conclusion is the exact arithmetic specialization
\[
\boxed{\text{greedy lattice growth}\ \longrightarrow\ \psi
\ \xrightarrow{\text{Mellin transform}}\ -\zeta'/\zeta
\ \xrightarrow{\text{inversion}}\ \text{Riemann explicit formula},}
\]
together with the independent Cartan spectral limit. These give a concrete mathematical explanation of the proposed connection while identifying the extra arithmetic data it requires.
