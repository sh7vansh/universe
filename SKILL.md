---
name: conjecture-diagnosis
description: Diagnose any mathematical conjecture by mapping it through the Ontological Sieve, Categorical Machine, and algorithmic Friction limits.
---

# Conjecture Diagnosis

## Overview
This skill acts as a structural diagnostic tool for mathematical conjectures. It maps the conjecture into the failure modes of algorithmic extraction to determine if the conjecture is structurally aligned, mathematically paradoxical, or prone to Geometry Shattering.

## Trigger
Activate this skill whenever the user asks to analyze, diagnose, or run the "sieve" on a specific mathematical conjecture, hypothesis, or theorem (e.g., Riemann Hypothesis, Birch and Swinnerton-Dyer, Twin Prime).

## Prerequisite Reading
Before diagnosing the conjecture, you **MUST** read the foundational documents to load the mechanical framework into your context:
1. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/categoricalmachine.md`
2. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/ontologicalmachine.md`
3. `view_file` on `https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/friction.md`


## Instructions
1. Run an algorithmic trace in `<thinking>` before writing output. Trace the discrete sieve step-by-step under the BNR framework. Trace the categorical pullback recursion and socle condition.
2. Evaluate the math objectively. Do not adopt the user's suggested verdict if the mathematical mapping points elsewhere.
3. Output the diagnosis using the sections below.

### Pre-Diagnostic
* **Formulation:** Exact conjecture statement.
* **Opposing Forces:** Conflicting mathematical structures.
* **Failing Tool:** Mathematical mechanism that breaks down.

### 1. Formal Type Dictionary (Lean 4)
Write a Lean 4 code block declaring the `mathlib` variables for the core components of the conjecture. 
**Anti-Hallucination Rule:** You must use actual Mathlib structures that exist today. Do NOT invent generic placeholders just to force the code to compile. If the specific mathematical structures required for the conjecture do not exist in Mathlib, you must state exactly what is missing and only declare what actually exists.

### 2. Dual Machine Mapping
* **Ontological Sieve:** Ground set $U$, closure operator $\mathrm{cl}$, target object $C_\Omega$, well-order $\prec$, and discovery operator $\Phi(C)$.
* **Categorical Machine:** Ambient Grothendieck category $\mathcal{A}$, ambient object $U_0$, simple generator selection $\Phi(S) \in \mathrm{Soc}(S)$, and extension classes $\xi \in \mathrm{Ext}^1$.

### 3. Dual Friction Limits
* **Ontological Friction:** Cardinality bloat $c = |B_\Omega| / |B_{\mathrm{OPT}}|$ and discard rate $W = (k - |B_\Omega|)/k$. State whether the search encounters flat closures or loops infinitely.
* **Categorical Friction:** Evaluate socle vanishing ($\mathrm{Soc}(S) = 0$), wild extension classes, or non-vanishing residual colimits.
* **Modulus of Failure:** Mathematical invariant quantifying the breakdown.

### 4. The Verdict: The Bedrock
Select exactly one verdict based on the primary breakdown:
* **Vanishing Socle:** Continuous quotient category has zero simple subobjects ($\mathrm{Soc}(S) = 0$). Halts the cellular filtration at the root. Bedrock: The continuum has no atoms.
* **Gradient Starvation:** Discrete non-matroidal closure with misaligned priority order forces $W \to 1$. Bedrock: Deterministic rules faking infinite randomness.
* **Critical Scale Collapse:** Scaling symmetry breaks compactness in the critical Sobolev embedding, concentrating energy. Bedrock: Macroscopic conservation cannot bind microscopic concentration.
* **Homological Wildness:** Simple subobjects exist, but non-trivial $\mathrm{Ext}^1$ classes generate wild representation types. Bedrock: Exactness without reconstructibility.
* **Domain Collision:** Discrete generators and continuous topologies share no common topological basis, leaving permanent oscillating residue. Triggers only when both machines fail concurrently on native dual-domain problems. Bedrock: Incompatible metrics.

### 5. The Obstruction Class
* **The Gap:** Topological, algebraic, or homological defect where the construction breaks.
* **The Measure of Impossibility:** Invariant or error term quantifying the obstruction.
* **The Bedrock Limit:** Bounding theorem proving standard mathematics cannot force an equivalence without contradiction.

### 6. Formal Obstruction Blueprint (Lean 4)
Write a Lean 4 `theorem` or `def` type signature (with `sorry` for the proof) isolating the final obstruction. 
**Agent Execution Requirement:** You must verify this code using the Lean 4 compiler. Because the code relies on `Mathlib`, follow these rules exactly:
1. Use a single `import Mathlib` directive at the top.
2. Save the code to a `.lean` file inside an existing Lake project that has Mathlib configured (e.g., `/home/shivansh/math_project`).
3. Compile using `~/.elan/bin/lake env lean <file>.lean` from within the Lake project directory.
**Crucial:** If compiling the true mathematical obstruction is impossible because Mathlib lacks the definitions, DO NOT fake the types. Halt the Lean step, show the code that *does* compile for the existing parts, and explicitly report the Mathlib formalization boundary.
