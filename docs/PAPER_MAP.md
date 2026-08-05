# Paper-to-Lean map

This file is the traceability index for the machine-checked companion to
*From Low Degree to Statistical Indistinguishability for Bounded-Treewidth Planted Graphs*.

## Source snapshot

- Source title: *From Low Degree to Statistical Indistinguishability for Bounded-Treewidth Planted Graphs*
- Authors in source: Xuan Chen and Shuangping Li
- Source working copy relative to the original research directory: `writing/overleaf_local/arxiv.tex`
- SHA-256: `6146a30285bf3ef27e8b1ffc78bef52c394ee94b468cc572bb415690e4dc826d`
- Source length at this snapshot: 1,914 lines
- Numbering source: the compiled `arxiv.aux` beside the TeX source; Definition 5.2 is inferred from the shared theorem counter because it has no `\label`.

If the TeX hash changes, audit the changed statements and identities before updating this map.

## Inventory and status conventions

| Environment | Count |
|---|---:|
| Theorem | 3 |
| Proposition | 1 |
| Lemma | 13 |
| Definition | 1 |
| Corollary | 0 |
| Claim | 0 |
| Remark instantiated in the paper | 0 |
| **Total numbered statements** | **18** |

The two status dimensions are deliberately independent:

- **Statement fidelity** records how the planned Lean declaration relates to the printed mathematical statement. “Exact + guards” means the same asymptotic assertion with domain facts that TeX leaves implicit, such as `c / n ≤ 1` eventually.
- **Proof status** records implementation progress only. **Statement formalized**
  means that Lean contains an exact proposition with the correct quantifier
  order, but does not claim a proof of that proposition.

## Numbered statements

| Paper statement | Source label / lines | Planned Lean declaration | Planned module | Statement fidelity | Proof status |
|---|---|---|---|---|---|
| Theorem 1.1, “Low-degree consequence for bounded-treewidth plants” | `thm:main`, 234–259 | Statement: `LowDegree.main_lowDegree_to_noisedL2_and_tv_statement`; future theorem: `LowDegree.main_lowDegree_to_noisedL2_and_tv` | `LowDegree/Main.lean` | Exact asymptotic shell, with `tw(Γₙ) ≤ kₙ`, positive `Dₙ`, and pointwise fixed-noise quantification. The model-facing realization must add the eventual Bernoulli-domain guards. Preserve both conclusions: noised `L²=1+o(1)` and TV `=o(1)`. | **Statement formalized; proof pending** |
| Theorem 1.2, “Critical and subcritical backgrounds” | `thm:subcritical`, 280–287 | `LowDegree.subcritical_lowDegree_to_tv` | `LowDegree/Subcritical.lean` | Exact + guards. The printed theorem concludes **TV only**, not noised `L²`. | Planned |
| Lemma 3.1, uniform leading-term comparison | `lem:leading-term`, 840–853 | `LowDegree.alpha_div_beta_tendsto_uniformly`, `LowDegree.alpha_div_graphBeta_tendsto_uniformly_on_occurringShapes` | `LowDegree/Asymptotics/LeadingTerm.lean`, `LowDegree/Asymptotics/ModelConsequences.lean` | Exact uniform little-`o` statement, including the adapter for nonempty support shapes that actually occur in the ambient plant; the eventual `1/2` and `2` bounds are also proved. | **Proved** |
| Lemma 3.2, edge-count consequence | `lem:edge`, 885–893 | `LowDegree.BoundedTreewidthPlantModel.edgeCount_isLittleO_sqrt` | `LowDegree/Asymptotics/ModelConsequences.lean` | Exact for the model-realized planted likelihood and projected norm; `degreeCutoff_pos` includes degree one (in fact at every index), and the sparse parameter is proved equal to `c/n` eventually. | **Proved** |
| Lemma 3.3, exclusion of short cycles | `lem:girth`, 919–929 | `LowDegree.BoundedTreewidthPlantModel.no_shortCycles_of_lowDegree` | `LowDegree/Asymptotics/NoShortCycles.lean` | Exact simultaneous eventual statement for every integer `3 ≤ l ≤ D_n`, proved from the concrete model Parseval sum for `0<c≤1`. | **Proved** |
| Lemma 4.1, isomorphism-triple count | `lem:isomorphism-triples`, 1023–1033 | `LowDegree.FiniteGraphShape.card_isomorphismTriplesIn`, `LowDegree.FiniteGraphShape.graphBetaWeight_eq_betaFromTriple` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact finite identities for concrete non-induced graph copies, `|Tri(F)|`, and `β_n(F)`. | **Proved** |
| Lemma 4.2, restriction map injection | `lem:map-injection`, 1076–1083 | `LowDegree.FiniteGraphShape.restrictIsomorphismTriple_injective`, `LowDegree.FiniteGraphShape.copyCount_sq_mul_aut_le_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact concrete restriction/transport map, injectivity proof, and expanded copy-count product bound. | **Proved** |
| Lemma 4.3, bounded treewidth implies divisibility | `lem:decomposition`, 1136–1139 | `LowDegree.treewidth_implies_divisible` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact, using an explicit arbitrary-graph treewidth convention. | Planned |
| Lemma 4.4, cluster expansion | `lem:cluster-expansion`, 1150–1159 | `LowDegree.clusterExpansion_bound` | `LowDegree/Main.lean` | Exact as printed, including its redundant low-degree premise; a stronger premise-minimized helper may coexist. | Planned |
| Lemma 4.5, connected noised mass | `lem:connect-upper-bound`, 1193–1201 | `LowDegree.connectedNoisedMass_isLittleO` | `LowDegree/Main.lean` | Exact + explicit contextual hypothesis `tw(Γ_n)=k_n`. | Planned |
| Lemma 4.6, no cycle after deletion | `lem:no-cycle`, 1291–1302 | `LowDegree.percolatedPlant_acyclic_inProbability` | `LowDegree/Subcritical.lean` | Exact convergence of the cycle-event probability to zero. | Planned |
| Proposition 5.1, bounded-overlap edge decomposition | `prop:treewidth-division`, 1449–1464 | `LowDegree.exists_boundedOverlap_edgeDecomposition` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact finite existence theorem. | Planned |
| Definition 5.2, tree decomposition and treewidth | unlabeled, 1473–1490 | `LowDegree.TreeDecomposition.Decomposition`, `LowDegree.TreeDecomposition.Decomposition.WidthAtMost`, `LowDegree.TreeDecomposition.treewidth` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact minimum-width definition for arbitrary finite graphs, hence also for the printed connected specialization. | **Proved** |
| Lemma 5.3, subcubic edge-owned refinement | `lem:decomposition-refinement`, 1492–1505 | `LowDegree.exists_subcubic_edgeOwned_decomposition` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact finite existence theorem, including all three ownership/degree properties. | Planned |
| Lemma 5.4, partition of a weighted subcubic tree | `lem:partition-tree`, 1540–1548 | `LowDegree.WeightedTreePartition.exists_partition`, `LowDegree.WeightedTreePartitionAdapter.exists_intrinsic_partition` | `LowDegree/Combinatorics/WeightedTreePartition.lean`, `LowDegree/Combinatorics/WeightedTreePartitionAdapter.lean` | Exact node-weight theorem on an intrinsic finite rooted subcubic tree; an arbitrary finite `SimpleGraph.IsTree` is now rooted and transferred to that theorem. Recovering an original-node-indexed cluster map and quotient from the intrinsic output remains. | **Core and arbitrary-tree rooting proved; label-preserving quotient pending** |
| Theorem A.1, randomized supercritical gap | `thm:supercritical-gap`, 1666–1680 | `LowDegree.supercritical_lowDegree_statisticalGap` | `LowDegree/Supercritical.lean` | Exact after making the choice of `A` precede the definition of `H_n^tr`; preserve `L²=1+o(1)` and TV `=1-o(1)`. | Planned |
| Lemma A.2, local-sparsity event | `lem:supercritical-local-sparsity`, 1687–1694 | `LowDegree.eventually_localSparsity` | `LowDegree/Supercritical.lean` | Exact existential choice `A=A(λ,r,γ)` with probability `1-o(1)`. | Planned |
| Lemma A.3, edge density after pruning | `lem:supercritical-pruning`, 1833–1840 | `LowDegree.sparseErdosRenyi_edgeDensity_tendstoInProbability`, `LowDegree.expected_shortCyclePruning_removedEdges_le_envelope`, `LowDegree.shortCyclePruning_removedEdges_isLittleOInProbability`, `LowDegree.shortCyclePruned_edgeDensity_tendstoInProbability` | `LowDegree/Probability/BernoulliCount.lean`, `LowDegree/SupercriticalPruning.lean` | The original sparse Erdős--Rényi edge density, exact short-cycle first moment, polylogarithmic envelope, `o_P(m_n)` removal, and preservation of `λ/2` are proved. The rare local-sparsity truncation input from Lemma A.2 remains. | **Short-cycle pruning proved; local truncation pending** |

## Proof-critical definitions

These prose definitions are part of statement fidelity even though most are not numbered environments.

| Paper object | Planned Lean object(s) | Planned module | Status |
|---|---|---|---|
| Fixed noise rates, `(kₙ+1)log n=o(Dₙ)`, and the model-realized Theorem 1.1 profile/conclusion | `NoiseRate`, `TreewidthDegreeScale`, `BoundedTreewidthPlantModel`, `FixedNoiseConclusion` | `LowDegree/Asymptotics/Basic.lean`, `LowDegree/Main.lean` | **Formalized; all scalar observables now derive from actual finite laws** |
| `Q_n=G(n,c/n)`, deterministic plant kernel `P_n`, random injection, union with background | `SparseBernoulliFamily`, `AmbientEdge`, `permutedPlantEdges`, `erdosRenyiLaw`, `plantedLaw` | `LowDegree/PlantedModel.lean` | **Formalized at the density level, with exact `c/n` proved eventually** |
| Edge resampling/deletion and noised planted law | `edgeNoise`, `resampleLaw`, `noisedPlantedLaw`, `deletedPlantedLaw` | `LowDegree/Fourier.lean`, `LowDegree/PlantedModel.lean`, `LowDegree/DeletedPlant.lean` | **Formalized, including exact deletion-before-superposition/resampling equivalence** |
| Likelihood ratios `L_n`, `L_{n,ε}` | `plantedLikelihood`, `noisedLikelihood`, `plantedLikelihood_isLikelihoodRatio`, `noisedLikelihood_isLikelihoodRatio` | `LowDegree/PlantedModel.lean` | **Formalized** |
| Degree-`D` polynomial subspace and orthogonal projection | `edgePolynomialLE`, `lowDegreeProjection`, `lowDegreeLikelihood` | `LowDegree/Fourier.lean` | Planned |
| Bernoulli characters `r_e`, `χ_S`, Fourier coefficients | `edgeCharacter`, `fourierCharacter`, `fourierCoeff` | `LowDegree/Fourier.lean` | Planned |
| Embedded copy `F^•`, concrete copy `F°`, `N_Γ(F)`, `Aut(F)`, `(n)_v` | `EmbeddedCopy`, `ConcreteCopy`, `subgraphCopyCount`, `GraphAut`, `Nat.fallingFactorial` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Exact and leading weights `α_n(F)`, `β_n(F)` | `alphaWeight`, `betaWeight` | `LowDegree/Asymptotics/LeadingTerm.lean` | Planned |
| Ordered edge decomposition and compatibility | `OrderedEdgeDecomposition`, `OrderedEdgeDecomposition.Compatible` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Isomorphism triples and restriction/transport | `IsomorphismTriple`, `IsomorphismTriple.restrict` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Vertex overlap | `OrderedEdgeDecomposition.overlap` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| `(l,C,a)`-divisibility | `Graph.IsDivisible` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Planned |
| Connected noised mass `θ_{n,ε}` | `connectedNoisedMass` | `LowDegree/Main.lean` | Planned |
| Cycle collections and deletion-percolated plant | `simpleCyclesOfLength`, `percolatedPlant` | `LowDegree/Subcritical.lean` | Planned |
| Forest truncation that replaces a cyclic retained plant by the empty graph | `forestTruncate`, `forestTruncatedPlantLaw` | `LowDegree/Subcritical.lean` | Planned |
| Tree bags, width, ownership, connected cluster contraction, quotient tree | `TreeDecomposition`, `EdgeOwnership`, `ConnectedClusterPartition`, `clusterQuotient` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Planned |
| Appendix `E_n`, `Ĥ_n`, `H_n^tr`, `P_n^sc`, and scan statistic `M_n` | `LocalSparsityEvent`, `shortCyclePrune`, `truncatedRandomPlant`, `supercriticalPlantedLaw`, `scanStatistic` | `LowDegree/Supercritical.lean` | Planned |

## Proof-critical identities and auxiliary lemmas

Overview equations 2.1 and 2.2 are expository versions of Eq. 4.4 and Proposition 5.1 respectively; they map to the same declarations rather than duplicate theorems.

| Paper identity or proof step | Source | Planned Lean declaration | Planned module | Proof status |
|---|---|---|---|---|
| Scale condition implies `Dₙ=ω(log n)` | prose following Theorem 1.1, lines 261–275 | `LowDegree.TreewidthDegreeScale.degree_isOmega_log` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Low-degree variational identity | Eq. 1.1, `eq:intro-low-degree-advantage` | `LowDegree.lowDegree_advantage_identity` | `LowDegree/Fourier.lean` | Planned |
| Noise preserves the null law | prose, lines 213–219 and 600–609 | `LowDegree.resampleLaw_erdosRenyiLaw` | `LowDegree/PlantedModel.lean` | **Proved** |
| Noise multiplies a degree-`d` Fourier coefficient by `(1-ε)^d` | prose, lines 159–161 | `LowDegree.fourierCoeff_edgeNoise` | `LowDegree/Fourier.lean` | **Proved** |
| Resampling a monotone plant equals deletion before superposition | prose, lines 213–219 and 600–609 | `LowDegree.deletedPlantedLikelihood_eq_noisedLikelihood`, `LowDegree.deletedPlantedLaw_eq_noisedPlantedLaw` | `LowDegree/DeletedPlant.lean` | **Proved** |
| Bernoulli characters form an orthonormal basis | prose preceding Eq. 3.1 | `LowDegree.fourierCharacters_orthonormalBasis` | `LowDegree/Fourier.lean` | Planned |
| Fourier expansion and degree projection | Eq. 3.1, `eq:fourier-expansion-1` | `LowDegree.fourierExpansion`, `LowDegree.lowDegreeProjection_eq_sum` | `LowDegree/Fourier.lean` | Planned |
| Parseval expression for the projected norm | Eq. 3.2, `eq:ldlr-1` | `LowDegree.lowDegree_norm_sq_eq_sum_fourierCoeff_sq` | `LowDegree/Fourier.lean` | Planned |
| Fixed-copy conditional likelihood expansion | Eq. 3.3, `eq:conditioned-likelihood` | `LowDegree.forcedLikelihood_fourierExpansion` | `LowDegree/Fourier.lean` | **Proved** |
| Mixture likelihood coefficients | Eq. 3.4, `eq:likelihood-expansion` | `LowDegree.fourierCoeff_plantedLikelihood`, `LowDegree.fourierCoeff_noisedLikelihood` | `LowDegree/PlantedModel.lean` | **Proved** |
| Number of embedded copies `(n)_v/|Aut(F)|` | prose, lines 766–770 | `LowDegree.card_embeddedCopies` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Containment probability `N_Γ(F)|Aut(F)|/(n)_v` | prose, lines 772–781 | `LowDegree.embedding_containment_probability` | `LowDegree/Fourier.lean` | Planned |
| Exact classwise low-degree norm | Eq. 3.5, `eq:ldlr-2` | `LowDegree.lowDegree_norm_sq_sub_one_eq_sum_alpha` | `LowDegree/Fourier.lean` | Planned |
| Exact full noised norm | Eq. 3.6, `eq:noise-lr` | `LowDegree.noised_norm_sq_sub_one_eq_sum_alpha` | `LowDegree/Fourier.lean` | Planned |
| Exact ratio `α/β=(1-c/n)^e n^v/(n)_v` and product form | proof of Lemma 3.1, lines 856–866 | `LowDegree.alpha_div_beta_exact` | `LowDegree/Asymptotics/LeadingTerm.lean` | Planned |
| Low-degree `β` mass is `o(1)` | Eq. 4.1, `eq:beta-low-degree` | `LowDegree.lowDegree_betaMass_isLittleO` | `LowDegree/Main.lean` | Planned |
| `β`-mass target suffices for noised `L²` | Eq. 4.2, `eq:beta-noised-target` | `LowDegree.noisedL2_of_betaMass_isLittleO` | `LowDegree/Main.lean` | Planned |
| Restriction/transport map | Eq. 4.3, `eq:isomorphism-map` | `LowDegree.IsomorphismTriple.restrict` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Overlap product bound `β(F)≤n^ov∏β(T_i)` | Eq. 4.4 / overview Eq. 2.1 | `LowDegree.FiniteGraphShape.graphBetaWeight_le_overlap_mul_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | **Proved for concrete non-induced graph copies** |
| Aggregate restriction injection over the disjoint union of all `F` | prose in Lemma 4.5 proof, lines 1244–1256 | `LowDegree.aggregateRestriction_injective` | `LowDegree/Combinatorics/IsomorphismTriples.lean` | Planned |
| Connected-component product injection and geometric-series estimate | proof of Lemma 4.4 | `LowDegree.componentRestriction_injective`, `LowDegree.sum_allSupports_le_geometric_connectedMass` | `LowDegree/Main.lean` | Planned |
| Select `l_n` with `3l_n≤D_n` and `(k_n+1)log n=o(l_n)` | proof of Lemma 4.5, lines 1203–1209 | `LowDegree.TreewidthDegreeScale.exists_intermediateScale` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Small connected-support contribution | Eq. 4.5, `eq:upper-bound-small` | `LowDegree.small_connectedNoisedMass_isLittleO` | `LowDegree/Main.lean` | Planned |
| Large connected-support contribution | Eq. 4.6, `eq:upper-bound-big` | `LowDegree.large_connectedNoisedMass_isLittleO` | `LowDegree/Main.lean` | Planned |
| TV/chi-square inequality and sequence-level certificate | proof of Theorem 1.1, lines 1280–1285 | `LowDegree.FiniteLaw.tv_le_half_sqrt_chiSq`, `LowDegree.SecondMomentCertificate.ofLikelihood` | `LowDegree/Probability/Finite.lean`, `LowDegree/Main.lean` | **Proved** |
| Short-girth path uniqueness | proof of Lemma 4.6, lines 1311–1318 | `LowDegree.atMostOne_shortPath_of_girth` | `LowDegree/Subcritical.lean` | Planned |
| Cycle encoding count `|C_k(Γ_n)|≤n^(k/r_n+1)` | proof of Lemma 4.6, lines 1320–1343 | `LowDegree.card_cycles_le_of_girth` | `LowDegree/Subcritical.lean` | Planned |
| Geometric survival-probability sum | proof of Lemma 4.6, lines 1344–1361 | `LowDegree.expected_survivingCycles_tendsto_zero` | `LowDegree/Subcritical.lean` | Planned |
| Forest truncation differs only on the cycle event | Eq. 4.7 setup, lines 1367–1386 | `LowDegree.tv_forestTruncation_le_cycleProbability` | `LowDegree/Subcritical.lean` | Planned |
| Forest-truncated Fourier coefficients are dominated; cyclic supports vanish | lines 1392–1417 | `LowDegree.forestTruncated_fourierCoeff_le`, `LowDegree.forestTruncated_fourierCoeff_eq_zero_of_cycle` | `LowDegree/Subcritical.lean` | Planned |
| Tree-support noised mass target | Eq. 4.8, `eq:truncated-sum-goal` | `LowDegree.treeNoisedMass_isLittleO` | `LowDegree/Subcritical.lean` | Planned |
| Treewidth monotonicity under subgraphs | prose, lines 1445–1448 | `LowDegree.TreeDecomposition.treewidth_mono_subgraph` | `LowDegree/Combinatorics/TreeDecomposition.lean` | **Proved** |
| Overlap as cluster-incidence excess | Eq. 5.1, `eq:overlap-decomposition` | `LowDegree.overlap_eq_sum_clusterIncidence` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Planned |
| Cluster incidence bounded by quotient-subtree edges | Eq. 5.2, `eq:overlap-decomposition-edge` | `LowDegree.clusterIncidence_sub_one_le_quotientEdges` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Planned |
| Each quotient interface repeats at most `k+1` graph vertices | proof of Proposition 5.1, lines 1596–1606 | `LowDegree.card_interface_le_width_add_one` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Planned |
| Local-sparsity event | Eq. A.1, `eq:supercritical-local-sparsity` | `LowDegree.LocalSparsityEvent` | `LowDegree/Supercritical.lean` | Planned |
| Local-density union bound | Eq. A.4, `eq:supercritical-local-union-bound` | `LowDegree.localSparsity_unionBound` | `LowDegree/Supercritical.lean` | Planned |
| Exact randomized-plant low-degree Parseval sum | Eq. A.5, `eq:supercritical-parseval` | `LowDegree.randomPlant_lowDegree_norm_eq_sum` | `LowDegree/Supercritical.lean` | Planned |
| Randomized containment upper bound | Eq. A.6, `eq:supercritical-containment` | `LowDegree.randomPlant_containment_le` | `LowDegree/Supercritical.lean` | Planned |
| Local excess restriction | Eq. A.7, `eq:supercritical-excess` | `LowDegree.localSparsity_excess_bound` | `LowDegree/Supercritical.lean` | Planned |
| Girth/vertex restriction | Eq. A.8, `eq:supercritical-girth-restriction` | `LowDegree.cyclicSupport_vertexCount_gt_girthCutoff` | `LowDegree/Supercritical.lean` | Planned |
| Supercritical graph-enumeration bound | Eq. A.9, `eq:supercritical-enumeration` | `LowDegree.supercritical_lowDegree_enumeration_bound` | `LowDegree/Supercritical.lean` | Planned |
| Factorial/binomial graph-count bound | Eq. A.10, `eq:supercritical-counting-bound` | `LowDegree.graphEnumeration_factorial_bound` | `LowDegree/Supercritical.lean` | Planned |
| Forest-like part of low-degree sum | Eq. A.11, `eq:super-critical-sum-1` | `LowDegree.subcriticalExcess_sum_bound` | `LowDegree/Supercritical.lean` | Planned |
| Cyclic/excess part of low-degree sum | Eq. A.12, `eq:super-critical-sum-2` | `LowDegree.nonnegativeExcess_sum_bound` | `LowDegree/Supercritical.lean` | Planned |
| Expected number of edges removed by short-cycle pruning is polylogarithmic | proof of Lemma A.3, lines 1842–1854 | `LowDegree.expected_shortCyclePruning_removedEdges_le_envelope` | `LowDegree/SupercriticalPruning.lean` | **Proved** |
| Pruning removes `o_P(m_n)` edges | proof of Lemma A.3 | `LowDegree.shortCyclePruning_removedEdges_isLittleOInProbability` | `LowDegree/SupercriticalPruning.lean` | **Proved** |
| Null scan-statistic tail tends to zero | proof of Eq. A.3, lines 1861–1898 | `LowDegree.null_scanStatistic_tail_tendsto_zero` | `LowDegree/Supercritical.lean` | Planned |
| Planted scan-statistic power tends to one | proof of Eq. A.3, lines 1899–1910 | `LowDegree.planted_scanStatistic_power_tendsto_one` | `LowDegree/Supercritical.lean` | Planned |

Standard library ingredients used throughout include Parseval, Cauchy–Schwarz, Markov, binomial concentration, the union bound, `\binom{N}{K}≤(eN/K)^K`, elementary logarithm inequalities, falling-factorial estimates, and total-variation triangle/coupling bounds. These should be reused from Mathlib when available and wrapped locally only when the paper’s exact normalization differs.

## Faithfulness hazards and required resolutions

1. **Bernoulli domain.** `G(n,c/n)` exists only when `0≤c/n≤1`. The paper works asymptotically and ignores finitely many small `n`. Lean declarations must either use an eventual filter with `n≥⌈c⌉` or carry the probability bound explicitly; they must not silently clamp `c/n`.
2. **Cross-referenced assumptions.** Later statements say “suppose Eq. 1.3 holds.” Standalone Lean declarations must restate the low-degree norm hypothesis, positivity/eventual lower bounds for `D_n`, and the definitions of the relevant likelihood ratios.
3. **Lemma 3.2 degree premise.** Its proof says `D_n→∞`, although the `K_2` argument only needs degree one to be included eventually. Encode the minimal explicit condition `1≤D_n` eventually while retaining the paper’s conclusion.
4. **Connected versus arbitrary treewidth.** Definition 5.2 is phrased for connected `F`, but Theorem 1.1 and Lemma 4.3 use treewidth for arbitrary `Γ`. Define tree decompositions for all finite simple graphs, then prove that the connected specialization matches the printed definition and that treewidth is monotone under subgraphs.
5. **Isolated vertices.** Plants may contain isolated vertices, while Fourier supports and abstract indexing graphs exclude them. Prove that deleting isolated plant vertices does not change the planted observation law, and state precisely how copy counts are indexed.
6. **Graph isomorphism classes.** The paper sums over abstract isomorphism classes. Lean quotient types can make finiteness and regrouping difficult. A labeled-representative implementation is acceptable only if it proves isomorphism invariance and recovers exactly the factor `N_Γ(F)^2|Aut(F)|` after regrouping.
7. **Aggregate injection.** Lemma 4.2 states a pointwise injection for one `F`, but Lemma 4.5 sums over `F` and uses the stronger fact that the image tuple recovers `F` from the union of first coordinates. Formalize `aggregateRestriction_injective` on a tagged disjoint union; the pointwise product inequality alone is insufficient for that sum.
8. **Compatible decomposition choices.** The prose globally fixes compatible ordered decompositions. Lean should carry the decomposition as witness data or use an explicit finite classical choice, preserving the piece isomorphism tags in aggregate maps.
9. **Theorem 1.2 conclusion.** Do not strengthen the mapped paper theorem to noised `L²=1+o(1)`. Its printed conclusion is only TV `=o(1)`, obtained through a forest-truncated comparison.
10. **Forest truncation semantics.** `T_ε^FΓ_n` does not delete only cyclic edges: if the retained graph has any cycle, the entire retained plant is replaced by the empty graph. The Lean definition and coefficient domination proof must use this exact operation.
11. **Appendix quantifier order.** The appendix introduces `A` “to be determined later,” defines `H_n^tr`, and then proves `∃A`. In Lean: choose an admissible `A=A(λ,r,γ)` first, define `H_n^tr` from it, and only then state Theorem A.1 and Lemma A.3.
12. **Fixed parameters in asymptotics.** Every use of `o`, `O`, `ω`, “uniformly,” “eventually,” and convergence in probability must specify the filter and hold `c,ε,r,γ,λ,A` fixed exactly where the paper does.
13. **Uniformity in Lemma 3.1.** The `o(1)` is uniform over a changing family of graphs `F`; a collection of pointwise `Tendsto` statements is not faithful. Use a supremum bound or an eventual uniform inequality.
14. **Finite support of abstract sums.** Although equations display sums over abstract graphs, only subgraphs of a fixed finite plant contribute. Lean sums must be explicitly finite or proved summable before invoking infinite-series operations.
15. **Redundant premise in Lemma 4.4.** The printed statement assumes Eq. 1.3, but its proof uses only `θ_{n,ε}=o(1)` and the exact component-product bound. Keep an exact wrapper with the printed hypotheses; an internal strengthened helper may omit the unused premise.
16. **Exact normalization.** The paper uses `‖P-Q‖_TV=sup_A|P(A)-Q(A)|=(1/2)E_Q|L-1|`, falling factorials, non-induced subgraph counts, and automorphism-group cardinalities. Match these normalizations before translating any standard Mathlib result.
17. **Small-`n` denominators.** Expressions involving `(n)_{v(F)}`, `c/n`, and `α_n(F)/β_n(F)` require positivity/nonzero proofs. The occurrence assumption `N_{Γ_n}(F)>0` and `|V(Γ_n)|≤n` provide `v(F)≤n`; record those facts explicitly.
18. **Theorem A.1 parameter dependence.** The printed `c_0=c_0(λ,r,γ)` does not list `ε`, but `λ` was chosen after fixing `ε` with `λ>2/(1-ε)`. Preserve that quantifier order rather than introducing an independent hidden dependence.

## Suggested update policy

When a declaration is added, update only its **Proof status** (`Planned` → `Statement formalized` → `Proved`), and link the declaration if useful. Change **Statement fidelity** only after comparing the Lean type directly with the source snapshot above. Any intentional strengthening or normalization lemma should be recorded as an auxiliary result, not substituted silently for the paper-facing wrapper.
