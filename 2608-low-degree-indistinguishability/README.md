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
paper's asymptotic arguments.

All 21 numbered statements in the audited Overleaf snapshot have concrete
Lean proofs. This includes all 16 main-text statements, the revised treewidth
scale in Theorem 1.1, the new aggregate restriction injection in Lemma 4.3,
and the complete deterministic Appendix A.1--A.5. The appendix development
constructs the deterministic graph sequence unconditionally, proves the
multi-pair local-sparsity union bound and short-cycle first-moment estimate,
and identifies the uniformly injected/noised law exactly with the padded
planted-graph model. Theorem A.2 supplies an explicit threshold `c₀>1`
independent of the admissible noise rate.

The repository uses no `sorry`, `admit`, or project axiom. See
[`docs/PAPER_MAP.md`](docs/PAPER_MAP.md) for the statement-by-statement audit
against the current Overleaf fingerprint.

## Paper link

The stable project URL is
[github.com/fifalsp/lean/tree/main/2608-low-degree-indistinguishability](https://github.com/fifalsp/lean/tree/main/2608-low-degree-indistinguishability).
A paper-ready LaTeX sentence is:

```latex
The full Lean formalization is available at
\href{https://github.com/fifalsp/lean/tree/main/2608-low-degree-indistinguishability}{\texttt{fifalsp/lean/2608-low-degree-indistinguishability}}.
```

## Main formal theorem

The displayed formulas in this README use GitHub's native fenced-math syntax;
the source inside each block is ordinary LaTeX.

The theorem
[`main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth`](LowDegree/BoundedTreewidthTheorem.lean)
proves the following implication. Consider a positive background density, a
sequence of plants on at most $n$ vertices, and positive degree cutoffs $D_n$.
Assume

```math
\operatorname{tw}(\Gamma_n)\log n=o(D_n)
```

and

```math
\bigl\|L_n^{\le D_n}\bigr\|_{L^2(Q_n)}^2=1+o(1).
```

Then, for every fixed noise rate $\varepsilon\in(0,1)$,

```math
\bigl\|L_{n,\varepsilon}\bigr\|_{L^2(Q_n)}^2=1+o(1)
```

and consequently

```math
d_{\mathrm{TV}}\!\left(T_\varepsilon P_n,Q_n\right)=o(1).
```

The norm and TV sequences are definitionally constructed from the concrete
finite laws. The theorem is stated directly for the model-facing numerical
treewidth sequence; a root-namespace alias exposes the same result to clients.

## Deterministic appendix

For fixed even `D ≥ 6`, `r ∈ (0,1/2)`, and `γ ∈ (0,1)`, Appendix A uses

```math
m_n=\left\lfloor n^r\right\rfloor,
\qquad
D_n=\left\lceil(\log n)^2\right\rceil.
```

The paper-facing theorem
[`appendixA1_evenDegree_deterministicPlantWitness`](LowDegree/DeterministicConfigurationConstruction.lean)
constructs simple graphs $\Gamma_n$ with explicit positive constants $A$ and
$\kappa$ satisfying

```math
\begin{aligned}
\Delta(\Gamma_n)&\le D,\\
\mathsf e(\Gamma_n[U])
  &\le \left(1+\frac{A}{\log n}\right)|U|
    &&\text{for }2\le |U|\le m_n^\gamma,\\
\operatorname{girth}(\Gamma_n)&\ge \kappa\log n,\\
\frac{\mathsf e(\Gamma_n)}{m_n}&\longrightarrow \frac D2.
\end{aligned}
```

The supporting configuration-model results are
[`appendixConfigurationLocalSparsity_probability_tendsto_one`](LowDegree/DeterministicConfigurationLocalSparsity.lean)
for Lemma A.4 and
[`appendixA5_evenDegree_fewShortCycles_probability_tendsto_one`](LowDegree/DeterministicConfigurationShortCycles.lean)
for Lemma A.5.

## Build

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.
From the repository root:

```bash
cd 2608-low-degree-indistinguishability
lake build
```

The umbrella module is `LowDegree.lean`.
