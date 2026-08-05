# Low-degree indistinguishability in Lean

This repository is a machine-checked companion to *From Low Degree to
Statistical Indistinguishability for Bounded-Treewidth Planted Graphs* by Xuan
Chen and Shuangping Li.

## Current scope

The project formalizes reusable proof kernels for finite Bernoulli Fourier
analysis, total variation and second moments, isomorphism-triple counting,
tree-decomposition bookkeeping, and the paper's asymptotic arguments. It also
contains an exact Lean proposition for the bounded-treewidth low-degree
consequence, including the pointwise quantifier “for every fixed
`ε ∈ (0,1)`.”

This is not yet a complete verification of the paper's main theorem. In
particular, the graph-facing construction of the planted laws and likelihood
ratios, and the existence proof for the required bounded-overlap tree
decomposition, remain to be formalized. The repository deliberately uses no
`sorry`, `admit`, or project axiom to hide those gaps. See
[`docs/PAPER_MAP.md`](docs/PAPER_MAP.md) for the statement-by-statement audit.

## Main formal statement

`LowDegree.main_lowDegree_to_noisedL2_and_tv_statement` encodes the following
logical implication. For a positive background density, a sequence of plants
on at most `n` vertices, positive degree cutoffs `Dₙ`, and treewidth upper
bounds `kₙ`,

```text
(kₙ + 1) log n = o(Dₙ)
and ‖Lₙ^{≤Dₙ}‖² = 1 + o(1)
```

imply, for every fixed noise rate `ε ∈ (0,1)`,

```text
‖Lₙ,ε‖² = 1 + o(1)
and TV(Tε Pₙ, Qₙ) = o(1).
```

The declaration is a proposition marked as proof-pending, not an axiom. The
verified `SecondMomentCertificate.fixedNoiseConclusion` supplies the final
`L² → TV` step once the noised second-moment estimate is established.

## Build

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.

```bash
lake update
lake build
```

The umbrella module is `LowDegree.lean`.
