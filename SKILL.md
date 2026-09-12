---
name: conjecture-diagnosis
description: Diagnose any mathematical conjecture by mapping it through the Basis Discovery Algorithm, Decoupling Algorithm, and algorithmic Friction limits.
---

# Conjecture Diagnosis

## Overview
This skill acts as a structural diagnostic tool for mathematical conjectures. It maps the conjecture into the failure modes of algorithmic extraction to determine if the conjecture is structurally aligned, mathematically paradoxical, or prone to Geometry Shattering.

## Trigger
Activate this skill whenever the user asks to analyze, diagnose, or run the Basis Discovery Algorithm or Decoupling Algorithm on a specific mathematical conjecture, hypothesis, or theorem (e.g., Riemann Hypothesis, Birch and Swinnerton-Dyer, Twin Prime).

## Prerequisite Reading
Before diagnosing the conjecture, you **MUST** read the foundational documents to load the mechanical framework into your context:
1. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/categoricalmachine.md`
2. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/ontologicalmachine.md`
3. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/friction.md`

## Instructions
1. Run an algorithmic trace in `<thinking>` before writing output. Trace the Basis Discovery Algorithm step-by-step under the BNR framework. Trace the Decoupling Algorithm pullback recursion and socle condition.
2. Follow the math, not the user. If the mathematical mapping contradicts the user's suggested verdict, say so.
3. Output the diagnosis using the sections below.

### Pre-Diagnostic
* **Formulation.** Exact conjecture statement.
* **Opposing Forces.** Conflicting mathematical structures.
* **Failing Tool.** Mathematical mechanism that breaks down.

### 1. Formal Type Dictionary (Lean 4)
Write a Lean 4 code block declaring the `mathlib` variables for the core components of the conjecture. 

**Real structures only.** You must use actual Mathlib structures that exist today. Do not invent generic placeholders just to force the code to compile. If Mathlib lacks the required structures, state exactly what is missing and only declare what exists.

### 2. Dual Algorithm Mapping
* **Basis Discovery Algorithm.** Ground set $U$, closure operator $\mathrm{cl}$, target object $C_\Omega$, well-order $\prec$, and discovery operator $\Phi(C)$.
* **Decoupling Algorithm.** Ambient Grothendieck category $\mathcal{A}$, ambient object $U_0$, simple generator selection $\Phi(S) \in \mathrm{Soc}(S)$, and extension classes $\xi \in \mathrm{Ext}^1$.

### 3. Dual Friction Limits
* **Basis Discovery Friction.** Cardinality bloat $c = |B_\Omega| / |B_{\mathrm{OPT}}|$ and discard rate $W = (k - |B_\Omega|)/k$. Check if the search hits flat closures or loops infinitely.
* **Decoupling Friction.** Check for socle vanishing ($\mathrm{Soc}(S) = 0$), wild extension classes, or non-vanishing residual colimits.
* **Modulus of Failure.** Mathematical invariant quantifying the breakdown.

### 4. The Verdict
Select exactly one verdict based on the primary breakdown:
* **Trivial Socle ($\mathrm{Soc}(S) = 0$).** Continuous quotient category has zero simple subobjects ($\mathrm{Soc}(S) = 0$). Halts the cellular filtration at the root. Root cause: The continuum has no atoms.
* **Asymptotic Discard Rate Divergence ($W \to 1$).** Discrete non-matroidal closure with misaligned priority order forces $W \to 1$. Root cause: Deterministic rules faking infinite randomness.
* **Non-Compactness of the Critical Sobolev Embedding.** Scaling symmetry breaks compactness in the critical Sobolev embedding, concentrating energy. Root cause: Macroscopic conservation cannot bind microscopic concentration.
* **Non-Vanishing First Yoneda Extension Group ($\mathrm{Ext}^1 \neq 0$).** Simple subobjects exist, but non-trivial $\mathrm{Ext}^1$ classes generate wild representation types. Root cause: Exactness without reconstructibility.
* **Strictly Incomparable Topologies ($\tau_1 \not\subseteq \tau_2$ and $\tau_2 \not\subseteq \tau_1$).** Discrete generators and continuous topologies share no common topological basis, leaving permanent oscillating residue. Triggers only when both algorithms fail concurrently on native dual-domain problems. Root cause: Incompatible metrics.

### 5. The Obstruction Class
* **The Gap.** Topological, algebraic, or homological defect where the construction breaks.
* **The Measure of Impossibility.** Invariant or error term quantifying the obstruction.
* **The Hard Limit.** Bounding theorem proving standard mathematics cannot force an equivalence without contradiction.

### 6. Lean 4 signature for the obstruction
Write a Lean 4 `theorem` or `def` type signature (with `sorry` for the proof) isolating the final obstruction. 

**Execution rules.** Verify this code using the Lean 4 compiler. Since the code relies on `Mathlib`, follow these rules:
1. Use a single `import Mathlib` directive at the top.
2. Save the code to a `.lean` file inside an existing Lake project that has Mathlib configured (e.g., `/home/shivansh/math_project`).
3. Compile using `~/.elan/bin/lake env lean <file>.lean` from within the Lake project directory.

**Missing definitions.** If you cannot compile the true mathematical obstruction because Mathlib lacks the definitions, do not fake the types. Stop the Lean step, show the code that compiles for the existing parts, and state exactly where Mathlib falls short.
