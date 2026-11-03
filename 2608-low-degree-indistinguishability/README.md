# Rigorous Low-Degree Implications for Planted Subgraph Detection — Lean formalization

Machine-checked proofs for

> Xuan Chen and Shuangping Li.
> **Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth.**
> [arXiv:2608.06279](https://arxiv.org/abs/2608.06279)

The two main theorems, the appendix construction, and every lemma and proposition used in their proofs are stated and proved in Lean 4. The development contains **no `sorry`, `admit`, or project-specific axioms**.

## Main results

Throughout, $Q_n = G(n, c/n)$, $P_n$ plants a uniformly random copy of a deterministic graph $\Gamma_n$ into a sample of $Q_n$, and $T_\varepsilon$ resamples every edge indicator independently with probability $\varepsilon$.

| Paper | Statement | Lean declaration |
| --- | --- | --- |
| **Theorem 1.1** | Fix $c>0$. If $\operatorname{tw}(\Gamma_n)\log n = o(D_n)$ and $\lVert L_n^{\le D_n}\rVert_{L^2(Q_n)}^2 = 1+o(1)$, then for every fixed $\varepsilon\in(0,1)$, $\lVert L_{n,\varepsilon}\rVert_{L^2(Q_n)}^2 = 1+o(1)$ and $\lVert T_\varepsilon P_n - Q_n\rVert_{\mathrm{TV}} = o(1)$. | [`main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth`](LowDegree/BoundedTreewidthTheorem.lean) |
| **Theorem 1.2** | Fix $c\in(0,1]$. If $D_n=\omega(\log n)$ and $\lVert L_n^{\le D_n}\rVert_{L^2(Q_n)}^2 = 1+o(1)$, then $\lVert T_\varepsilon P_n - Q_n\rVert_{\mathrm{TV}} = o(1)$ for every fixed $\varepsilon\in(0,1)$, with no assumption on $\operatorname{tw}(\Gamma_n)$. | [`subcritical_lowDegree_to_tv`](LowDegree/Asymptotics/ForestLargeConnectedBetaMass.lean) |
| **Theorem A.3** | For every fixed $\varepsilon$ and all sufficiently large $c$, there are deterministic bounded-degree planted graphs whose degree-$(\log n)^2$ advantage vanishes, yet $\lVert T_\varepsilon P_n - Q_n\rVert_{\mathrm{TV}} = 1-o(1)$. | [`deterministicGap_exists_threshold_uniform_noise`](LowDegree/DeterministicGapTheorem.lean) |

All declarations live in the `LowDegree` namespace. The treewidth hypothesis of Theorem 1.1, $\operatorname{tw}(\Gamma_n) = o(D_n/\log n)$, is stated without division. For every numbered statement in the paper, [`docs/PAPER_MAP.md`](docs/PAPER_MAP.md) lists the Lean declaration and module, notes how faithful the formal statement is, and gives its proof status.

> **Numbering.** Statement numbers here and in `PAPER_MAP.md` follow the November 2026 version of the paper (the STOC 2027 submission).

## What is formalized

- **Model and Fourier analysis.** This covers the sparse Bernoulli background $G(n,c/n)$, uniformly embedded planted graphs, edge resampling, and the equivalence between resampling and deleting planted edges before superposition. It also covers Bernoulli characters, low-degree projections, and Parseval's identity.
- **Counting.** Concrete graph copies, automorphisms, and isomorphism triples. The identity $\lvert\mathrm{Tri}(F)\rvert = N_{\Gamma_n}(F)^2\,\lvert\mathrm{Aut}(F)\rvert$. The restriction injections and the overlap bound for ordered edge decompositions.
- **Tree decompositions.** Treewidth for arbitrary finite graphs, subcubic edge-owned refinements, the weighted tree partition, and the bounded-overlap edge decomposition (Proposition 5.1).
- **Asymptotics.** The comparison between exact and leading Fourier weights, the exclusion of short cycles at and below criticality, connected and component-expanded noised mass, and the vanishing probability of a retained cycle after deletion.
- **Appendix A.** The deterministic configuration-model construction, local sparsity, few short cycles, the connected-subgraph count, and the scan statistic.

## Building

The project pins Lean `v4.24.0` (see `lean-toolchain`) and mathlib `v4.24.0`.

```bash
# Install the Lean toolchain manager first: https://github.com/leanprover/elan
cd 2608-low-degree-indistinguishability
lake exe cache get   # download prebuilt mathlib
lake build
```

To confirm that no axioms beyond Lean's standard ones are used, run `#print axioms` on any of the declarations above.

## Layout

| Path | Contents |
| --- | --- |
| `LowDegree/` | Planted model, Fourier analysis, likelihood ratios, Appendix A construction, and the main theorems |
| `LowDegree/Combinatorics/` | Graph copies, isomorphism triples, tree decompositions, and tree partitions |
| `LowDegree/Asymptotics/` | Leading-term comparison, low-degree and noised mass bounds, and cycle exclusion |
| `LowDegree/Probability/` | Finite probability and Bernoulli event lemmas |
| `docs/PAPER_MAP.md` | Statement-by-statement map from the paper to Lean |

## Acknowledgment

The formalization was developed with the assistance of OpenAI Codex. All proofs are checked by the Lean kernel.

## Citation

```bibtex
@misc{ChenLi2026LowDegree,
  author        = {Chen, Xuan and Li, Shuangping},
  title         = {Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth},
  year          = {2026},
  eprint        = {2608.06279},
  archivePrefix = {arXiv}
}
```
