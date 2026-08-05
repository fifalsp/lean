# Low-degree indistinguishability in Lean

This repository is a machine-checked companion to *From Low Degree to
Statistical Indistinguishability for Bounded-Treewidth Planted Graphs* by Xuan
Chen and Shuangping Li.

## Current scope

The project formalizes reusable proof kernels for finite Bernoulli Fourier
analysis, total variation and second moments, concrete graph-copy and
isomorphism-triple counting, tree-decomposition bookkeeping, and the paper's
asymptotic arguments. It also
contains an exact Lean proposition for the bounded-treewidth low-degree
consequence, including the pointwise quantifier “for every fixed
`ε ∈ (0,1)`.”

This is not yet a complete verification of the paper's main theorem. The
finite Erdős--Rényi, planted, deleted, and noised laws and their genuine
likelihood ratios are now formalized, including the exact identity between
deletion before superposition and resampling afterward. Paper Lemmas 3.1,
3.2, 3.3, 4.1, and 4.2 and Definition 5.2 have concrete proofs. Equation
(4.4), the intrinsic weighted subcubic-tree partition core of Lemma 5.4, its
arbitrary-tree rooting adapter, and the short-cycle pruning estimate in Lemma
A.3 are also verified. The remaining main gaps are the classwise Fourier
regrouping and aggregate restriction arguments, the label-preserving cluster
quotient, and existence of the required edge-owned bounded-overlap
decomposition. The repository deliberately uses no `sorry`, `admit`, or
project axiom to hide those gaps. See
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

The declaration is a proposition marked as proof-pending, not an axiom. Its
norm and TV sequences are definitionally constructed from the concrete finite
laws. The verified `SecondMomentCertificate.fixedNoiseConclusion_of_model`
supplies the final `L² → TV` step once the noised second-moment estimate is
established.

## Build

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.

```bash
lake update
lake build
```

The umbrella module is `LowDegree.lean`.
