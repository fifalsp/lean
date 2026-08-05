# Low-degree indistinguishability in Lean

**Formalization started:** August 2026

**Path in monorepo:** `fifalsp/lean/2608-low-degree-indistinguishability`

This project is a machine-checked companion to *From Low Degree to
Statistical Indistinguishability for Bounded-Treewidth Planted Graphs* by Xuan
Chen and Shuangping Li.

## Current scope

The project formalizes finite Bernoulli Fourier analysis, total variation and
second moments, concrete graph-copy and isomorphism-class counting,
tree-decomposition and bounded-overlap bookkeeping, forest truncation, and the
paper's asymptotic arguments. All eighteen numbered statements in the paper
have concrete Lean proofs: Theorems 1.1, 1.2, and A.1; Lemmas 3.1--5.4 and
A.2--A.3; Proposition 5.1; and Definition 5.2.

Appendix Theorem A.1 is proved for the actual twice-truncated, uniformly
injected random plant. Its proof includes the exact Parseval expansion (A.5),
the injection/containment estimate (A.6), the support restrictions (A.7)--(A.8),
the finite enumeration bound (A.9), and the analytic estimates (A.10)--(A.12),
then packages the low-degree and total-variation conclusions under one
threshold `c₀`. The repository uses no `sorry`, `admit`, or project axiom. See
[`docs/PAPER_MAP.md`](docs/PAPER_MAP.md) for the statement-by-statement audit.

## Main formal theorem

`LowDegree.main_lowDegree_to_noisedL2_and_tv` proves the following implication.
For a positive background density, a sequence of plants on at most `n`
vertices, positive degree cutoffs `Dₙ`, and treewidth upper bounds `kₙ`,

$$
(k_n+1)\log n=o(D_n)
\qquad\text{and}\qquad
\left\lVert L_n^{\le D_n}\right\rVert_{L^2(Q_n)}^2=1+o(1)
$$

imply, for every fixed noise rate $\varepsilon\in(0,1)$,

$$
\left\lVert L_{n,\varepsilon}\right\rVert_{L^2(Q_n)}^2=1+o(1)
\qquad\text{and}\qquad
d_{\mathrm{TV}}\!\left(T_\varepsilon P_n,Q_n\right)=o(1).
$$

The norm and TV sequences are definitionally constructed from the concrete
finite laws.
`LowDegree.BoundedTreewidthPlantModel.main_lowDegree_to_noisedL2_and_tv_statement_proved`
also proves the original proposition-valued statement retained in
`LowDegree/Main.lean`.

## Build

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.
From the repository root:

```bash
cd 2608-low-degree-indistinguishability
lake build
```

The umbrella module is `LowDegree.lean`.
