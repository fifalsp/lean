# Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth

Lean formalization of the paper by Xuan Chen and Shuangping Li.

## Current scope

Theorems 1.1 and 1.2, together with Theorem A.2 in Appendix A and the supporting
numbered statements used in their proofs, have been formalized in Lean.

The current development covers finite Bernoulli Fourier analysis and low-degree
projections; planted, noised, and truncated graph distributions and their
likelihood ratios; graph-copy, automorphism, and isomorphism-triple counting;
tree decompositions and bounded-overlap arguments; and the deterministic
configuration-model construction, local-sparsity estimates, short-cycle
control, and statistical distinguishability used in Appendix A.

The project builds with Lean 4.24.0 and mathlib 4.24.0 and contains no `sorry`,
`admit`, or project-specific axioms.
