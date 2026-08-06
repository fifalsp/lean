# Paper-to-Lean map

This file is the traceability index for the machine-checked companion to
*Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*.

## Source snapshot

- Source title: *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
- Authors in source: Xuan Chen and Shuangping Li
- Current title verified in live Overleaf `arxiv.tex` on 2026-08-06
- The statement map below was audited against the earlier full-source snapshot with SHA-256 `0388eec946d9ce098bbf0a1c1ea641c2e8dee78702e1844a8a075bbe64db1b30`
- Audited snapshot length: 125,672 characters; 2,443 lines
- Numbering source: the 21 theorem-like environments in source order. Definition 5.2 is inferred from the shared theorem counter because it has no `\label`.

If the theorem statements change, audit the changed declarations and identities before updating this map.

## Inventory and status conventions

| Environment | Count |
|---|---:|
| Theorem | 3 |
| Proposition | 1 |
| Lemma | 16 |
| Definition | 1 |
| Corollary | 0 |
| Claim | 0 |
| Remark instantiated in the paper | 0 |
| **Total numbered statements** | **21** |

All 21 numbered statements in this snapshot are proved: the 16 main-text
statements and the five statements in the revised deterministic Appendix.
The earlier twice-truncated
random-plant Appendix modules remain in the repository as proved auxiliary
mathematics; they no longer correspond to the numbered statements in this
source snapshot.

The two status dimensions are deliberately independent:

- **Statement fidelity** records how the Lean declaration relates to the
  printed mathematical statement. “Exact + guards” means the same asymptotic
  assertion with domain facts that TeX leaves implicit, such as `c / n ≤ 1`
  eventually.
- **Proof status** records implementation progress only. **Proved** means the
  declaration has a Lean proof with no `sorry`, `admit`, or project axiom.

## Numbered statements

| Paper statement | Source label / lines | Lean declaration | Module | Statement fidelity | Proof status |
|---|---|---|---|---|---|
| Theorem 1.1, low-treewidth plants | `thm:main`, starts line 355 | `LowDegree.main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth`; `LowDegree.BoundedTreewidthPlantModel.main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth` | `LowDegree/BoundedTreewidthTheorem.lean` | Exact numerical hypothesis `tw(Γₙ) log n=o(Dₙ)`, positive cutoffs, and fixed-noise conclusions. The zero-treewidth/edgeless case is included. | **Proved** |
| Theorem 1.2, critical and subcritical regimes | `thm:subcritical`, starts line 431 | `LowDegree.subcritical_lowDegree_to_tv` | `LowDegree/Asymptotics/ForestLargeConnectedBetaMass.lean` | Exact + Bernoulli guards. The conclusion is TV only, as printed. | **Proved** |
| Lemma 3.1, uniform leading-term comparison | `lem:leading-term`, starts line 1182 | `LowDegree.alpha_div_beta_tendsto_uniformly`, `LowDegree.alpha_div_graphBeta_tendsto_uniformly_on_occurringShapes` | `LowDegree/Asymptotics/LeadingTerm.lean`, `LowDegree/Asymptotics/ModelConsequences.lean` | Exact uniform little-`o` statement and eventual `1/2`--`2` comparison for occurring support shapes. | **Proved** |
| Lemma 3.2, edge-count consequence | `lem:edge`, starts line 1227 | `LowDegree.BoundedTreewidthPlantModel.edgeCount_isLittleO_sqrt` | `LowDegree/Asymptotics/ModelConsequences.lean` | Exact for the model-realized likelihood and projected norm, including the eventual degree-one premise. | **Proved** |
| Lemma 3.3, exclusion of short cycles | `lem:girth`, starts line 1261 | `LowDegree.BoundedTreewidthPlantModel.no_shortCycles_of_lowDegree` | `LowDegree/Asymptotics/NoShortCycles.lean` | Exact simultaneous eventual statement for every integer `3 ≤ ℓ ≤ Dₙ`, for `0<c≤1`. | **Proved** |
| Lemma 4.1, isomorphism-triple count | `lem:isomorphism-triples`, starts line 1365 | `LowDegree.FiniteGraphShape.card_isomorphismTriplesIn`, `LowDegree.FiniteGraphShape.graphBetaWeight_eq_betaFromTriple` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact finite identities for concrete non-induced copies, `\|Tri(F)\|`, and `βₙ(F)`. | **Proved** |
| Lemma 4.2, restriction map injection | `lem:map-injection`, starts line 1418 | `LowDegree.FiniteGraphShape.restrictIsomorphismTriple_injective`, `LowDegree.FiniteGraphShape.copyCount_sq_mul_aut_le_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact concrete restriction map, injectivity, and product bound. | **Proved** |
| Lemma 4.3, aggregate restriction injection | `lem:aggregate-injection`, starts line 1455 | `LowDegree.AggregateGraphRestriction.FixedPieceClassDecomposition.encode_injective` | `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | Exact tagged disjoint-union injection for an arbitrary collection of parent shapes with specified compatible decompositions; no artificial finite-type restriction is imposed. | **Proved** |
| Lemma 4.4, bounded treewidth implies divisibility | `lem:decomposition`, starts line 1512 | `LowDegree.TreeDecomposition.isDivisible_of_hasTreewidthAtMost` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | Exact `(ℓ,3,k+1)` divisibility, using the arbitrary-graph treewidth convention. | **Proved** |
| Lemma 4.5, cluster expansion | `lem:cluster-expansion`, starts line 1527 | `LowDegree.clusterExpansion_bound` | `LowDegree/Main.lean` | Exact printed wrapper, including its redundant low-degree premise; `clusterExpansion_bound_core` is the premise-minimized helper. | **Proved** |
| Lemma 4.6, connected noised mass | `lem:connect-upper-bound`, starts line 1570 | `LowDegree.BoundedTreewidthPlantModel.connectedNoisedBetaMass_vanishes` | `LowDegree/Asymptotics/LargeConnectedBetaMass.lean` | Exact model-facing conclusion under the revised numerical treewidth/degree scale. | **Proved** |
| Lemma 4.7, no cycle after deletion | `lem:no-cycle`, starts line 1719 | `LowDegree.PercolatedAcyclic.BoundedTreewidthPlantModel.retainedPlantCycleProbability_vanishes` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | Exact vanishing of the retained-plant cycle-event probability. | **Proved** |
| Proposition 5.1, bounded-overlap edge decomposition | `prop:treewidth-division`, starts line 1886 | `LowDegree.TreeDecomposition.exists_boundedOverlap_orderedEdgeDecomposition` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | Exact finite existence theorem with piece sizes in `[ℓ,3ℓ]` and overlap at most `(k+1)(m-1)`. | **Proved** |
| Definition 5.2, tree decomposition and treewidth | unlabeled, starts line 1910 | `LowDegree.TreeDecomposition.Decomposition`, `LowDegree.TreeDecomposition.Decomposition.WidthAtMost`, `LowDegree.TreeDecomposition.treewidth` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact minimum-width definition for arbitrary finite graphs, hence also for the printed connected specialization. | **Proved** |
| Lemma 5.3, subcubic edge-owned refinement | `lem:decomposition-refinement`, starts line 1929 | `LowDegree.TreeDecomposition.exists_edgeOwnedRefinement_of_hasTreewidthAtMost` | `LowDegree/Combinatorics/EdgeOwnedRefinement.lean` | Exact finite edge-owned subcubic refinement, preserving the width bound. | **Proved** |
| Lemma 5.4, weighted subcubic-tree partition | `lem:partition-tree`, starts line 1977 | `LowDegree.WeightedTreePartitionTheorem.exists_vertexPartitionWitness` | `LowDegree/Combinatorics/WeightedTreePartitionTheorem.lean` | Exact label-preserving connected partition, with exact contraction quotient tree and weights in `[ℓ,3ℓ]`. | **Proved** |
| Lemma A.1, deterministic planted graphs | `lem:deterministic-planted-graphs`, starts line 2084 | `LowDegree.appendixA1_evenDegree_deterministicPlantWitness`; `LowDegree.appendixA1_deterministicPlantWitness`; `LowDegree.appendixA1_configurationModelEstimates` | `LowDegree/DeterministicConfigurationConstruction.lean`, `LowDegree/DeterministicConfigurationAsymptoticBridge.lean`, `LowDegree/DeterministicConfigurationSelection.lean` | Exact paper-facing wrapper for every even `D≥6`, `r∈(0,1/2)`, and `γ∈(0,1)`. It returns a nonempty `DeterministicPlantWitness D r gamma`, whose fields are the positive constants, maximum-degree bound, local sparsity, logarithmic real-girth bound, and edge-density limit printed in the lemma. | **Proved** |
| Theorem A.2, deterministic low-degree--statistical gap | `thm:deterministic-gap`, starts line 2115 | `LowDegree.deterministicGap_exists_threshold_uniform_noise`; `LowDegree.deterministicGap_exists_threshold`; `LowDegree.deterministicGap_of_witness` | `LowDegree/DeterministicGapTheorem.lean` | Exact fixed-witness formulation after Lemma A.1: produces an explicit `c₀>1` independent of the admissible noise rate, proves both asymptotic conclusions for every `c≥c₀`, and identifies the uniformly injected/noised law exactly with the padded planted-graph law. | **Proved** |
| Lemma A.3, deterministic connected-count bound | `lem:deterministic-connected-count`, starts line 2144 | `LowDegree.deterministicConnectedCount` | `LowDegree/DeterministicConnectedCount.lean` | Exact unconditional finite bound from support cardinality and maximum degree. The manuscript's `6≤D` and `e≥1` assumptions are retained; the doubled-edge-tour proof also establishes the connected-copy enumeration input internally. | **Proved** |
| Lemma A.4, configuration-model local sparsity | `lem:deterministic-configuration-local-sparsity`, starts line 2302 | `LowDegree.appendixConfigurationLocalSparsity_probability_tendsto_one`; `LowDegree.appendixConfigurationBadLocal_probability_vanishes`; `LowDegree.configurationInternalLocalSparsityFailure_vanishes` | `LowDegree/DeterministicConfigurationLocalSparsity.lean` | Exact canonical plant-size statement with explicit positive slack constant. The proof establishes the prescribed disjoint-pair product probability, the fixed-size witness count, the two-range union bound, and a stronger multigraph failure estimate before projecting to the simple graph. | **Proved** |
| Lemma A.5, few short configuration-model cycles | `lem:deterministic-configuration-short-cycles`, starts line 2374 | `LowDegree.appendixA5_evenDegree_fewShortCycles_probability_tendsto_one`; `LowDegree.appendixPlantSize_fewShortCycles_probability_tendsto_one`; `LowDegree.deterministicConfiguration_fewShortCycles_failure_vanishes` | `LowDegree/DeterministicConfigurationShortCycles.lean` | Exact paper-facing even-total-degree statement and the specialization `m_n=\lfloor n^r\rfloor`. The proof counts distinct-vertex cycle presentations, proves the prescribed-pair product probability, derives the displayed first-moment bound, and applies Markov at the manuscript's logarithmic cutoff. | **Proved** |

## Proof-critical definitions

These prose definitions are part of statement fidelity even though most are not numbered environments.

| Paper object | Lean object(s) | Module | Status |
|---|---|---|---|
| Fixed noise rates, `tw(Γₙ)log n=o(Dₙ)`, and the model-realized Theorem 1.1 profile/conclusion | `NoiseRate`, `TreewidthProductDegreeScale`, `BoundedTreewidthPlantModel.numericalTreewidth`, `FixedNoiseConclusion` | `LowDegree/Asymptotics/Basic.lean`, `LowDegree/Main.lean`, `LowDegree/BoundedTreewidthTheorem.lean` | **Formalized and used by the proved theorem** |
| `Q_n=G(n,c/n)`, deterministic plant kernel `P_n`, random injection, union with background | `SparseBernoulliFamily`, `AmbientEdge`, `permutedPlantEdges`, `erdosRenyiLaw`, `plantedLaw` | `LowDegree/PlantedModel.lean` | **Formalized at the density level, with exact `c/n` proved eventually** |
| Edge resampling/deletion and noised planted law | `edgeNoise`, `resampleLaw`, `noisedPlantedLaw`, `deletedPlantedLaw` | `LowDegree/Fourier.lean`, `LowDegree/PlantedModel.lean`, `LowDegree/DeletedPlant.lean` | **Formalized, including exact deletion-before-superposition/resampling equivalence** |
| Likelihood ratios `L_n`, `L_{n,ε}` | `plantedLikelihood`, `noisedLikelihood`, `plantedLikelihood_isLikelihoodRatio`, `noisedLikelihood_isLikelihoodRatio` | `LowDegree/PlantedModel.lean` | **Formalized** |
| Degree-`D` Fourier subspace and orthogonal projection | `lowDegreeProjection`, `fourierCoeff_lowDegreeProjection`, `lowDegreeProjection_norm_sq` | `LowDegree/Fourier.lean` | **Formalized in the finite Fourier basis** |
| Bernoulli characters `r_e`, `χ_S`, Fourier coefficients | `edgeCharacter`, `fourierCharacter`, `fourierCoeff` | `LowDegree/Fourier.lean` | **Formalized** |
| Embedded/concrete copies, `N_Γ(F)`, automorphisms, `(n)_v` | `FiniteGraphShape.ConcreteCopy`, `nonInducedCopyCount`, `copyIsomorphismEquivAutomorphism`, `fallingFactorial` | `LowDegree/Combinatorics/GraphCopies.lean`, `LowDegree/Combinatorics/EmbeddedCopies.lean`, `LowDegree/Asymptotics/LeadingTerm.lean` | **Formalized with non-induced copy semantics** |
| Exact and leading weights `α_n(F)`, `β_n(F)` | `alphaWeight`, `betaWeight`, `FiniteGraphShape.graphBetaWeight` | `LowDegree/Asymptotics/LeadingTerm.lean`, `LowDegree/Combinatorics/GraphCopies.lean` | **Formalized** |
| Ordered edge decomposition and compatibility data | `TreeDecomposition.OrderedEdgeDecomposition`, `AggregateGraphRestriction.FixedPieceClassDecomposition`, `AggregateGraphRestriction.FixedPieceClassDivision` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Formalized; compatible choices are carried as witness data** |
| Isomorphism triples and restriction/transport | `FiniteGraphShape.IsomorphismTripleIn`, `FiniteGraphShape.restrictIsomorphismTriple`, `AggregateGraphRestriction.FixedPieceClassDecomposition.encode` | `LowDegree/Combinatorics/GraphCopies.lean`, `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Formalized** |
| Vertex overlap | `TreeDecomposition.OrderedEdgeDecomposition.overlap` | `LowDegree/Combinatorics/TreeDecomposition.lean` | **Formalized** |
| `(l,C,a)`-divisibility | `TreeDecomposition.IsDivisible` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | **Formalized** |
| Connected noised mass `θ_{n,ε}` | `BoundedTreewidthPlantModel.connectedNoisedBetaMass` | `LowDegree/Asymptotics/ConnectedBetaMass.lean` | **Formalized** |
| Cycle collections and deletion-percolated plant | `CycleEmbedding`, `retainedPlantLaw`, `retainedPlantCycleProbability` | `LowDegree/SupercriticalPruning.lean`, `LowDegree/ForestTruncation.lean` | **Formalized** |
| Forest truncation that replaces a cyclic retained plant by the empty graph | `IsForestEdgeSet`, `forestTruncatedRetainedPlantLaw`, `forestTruncatedObservationLaw` | `LowDegree/ForestTruncation.lean` | **Formalized with the manuscript's whole-plant truncation semantics** |
| Tree bags, width, ownership, connected cluster contraction, quotient tree | `TreeDecomposition.Decomposition`, `TreeDecomposition.EdgeOwnedRefinementWitness`, `TreeDecomposition.ClusterQuotientWitness`, `WeightedTreePartitionTheorem.VertexPartitionWitness` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/EdgeOwnedRefinement.lean`, `LowDegree/Combinatorics/WeightedTreePartitionTheorem.lean` | **Formalized, including a label-preserving quotient** |
| Deterministic Appendix plant sequence, padded ambient graph, and scan statistic `M_n` | `DeterministicPlantWitness`, `appendixA1_evenDegree_deterministicPlantWitness`, `DeterministicPlantWitness.ambientGraph`, `deterministicInjectedPlantLaw`, `graphScanStatistic` | `LowDegree/DeterministicConfigurationBase.lean`, `LowDegree/DeterministicConfigurationConstruction.lean`, `LowDegree/DeterministicStatistical.lean`, `LowDegree/SupercriticalStatistical.lean` | **Formalized; the witness is constructed unconditionally** |

## Proof-critical identities and auxiliary lemmas

Overview equations 2.1 and 2.2 are expository versions of Eq. 4.4 and Proposition 5.1 respectively; they map to the same declarations rather than duplicate theorems.

| Paper identity or proof step | Source | Lean declaration | Module | Proof status |
|---|---|---|---|---|
| Revised product scale reduces to the positive-width scale after repairing zero-width cutoffs | proof setup for Theorem 1.1 | `LowDegree.TreewidthProductDegreeScale.repaired`, `LowDegree.zeroWidthRepairedDegreeCutoff` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Low-degree variational identity | Eq. 1.1, `eq:intro-low-degree-advantage` | `LowDegree.lowDegree_advantage_identity` | `LowDegree/LowDegreeAdvantage.lean` | **Proved** |
| Noise preserves the null law | prose, lines 213–219 and 600–609 | `LowDegree.resampleLaw_erdosRenyiLaw` | `LowDegree/PlantedModel.lean` | **Proved** |
| Noise multiplies a degree-`d` Fourier coefficient by `(1-ε)^d` | prose, lines 159–161 | `LowDegree.fourierCoeff_edgeNoise` | `LowDegree/Fourier.lean` | **Proved** |
| Resampling a monotone plant equals deletion before superposition | prose, lines 213–219 and 600–609 | `LowDegree.deletedPlantedLikelihood_eq_noisedLikelihood`, `LowDegree.deletedPlantedLaw_eq_noisedPlantedLaw` | `LowDegree/DeletedPlant.lean` | **Proved** |
| Bernoulli characters form an orthonormal basis | prose preceding Eq. 3.1 | `LowDegree.fourierCharacters_orthonormal`, `LowDegree.fourierExpansion` | `LowDegree/Fourier.lean` | **Proved in an equivalent finite-basis form** |
| Fourier expansion and degree projection | Eq. 3.1, `eq:fourier-expansion-1` | `LowDegree.fourierExpansion`, `LowDegree.fourierCoeff_lowDegreeProjection` | `LowDegree/Fourier.lean` | **Proved** |
| Parseval expression for the projected norm | Eq. 3.2, `eq:ldlr-1` | `LowDegree.lowDegreeProjection_norm_sq` | `LowDegree/Fourier.lean` | **Proved** |
| Fixed-copy conditional likelihood expansion | Eq. 3.3, `eq:conditioned-likelihood` | `LowDegree.forcedLikelihood_fourierExpansion` | `LowDegree/Fourier.lean` | **Proved** |
| Mixture likelihood coefficients | Eq. 3.4, `eq:likelihood-expansion` | `LowDegree.fourierCoeff_plantedLikelihood`, `LowDegree.fourierCoeff_noisedLikelihood` | `LowDegree/PlantedModel.lean` | **Proved** |
| Number of embedded copies `(n)_v/\|Aut(F)\|` | prose, lines 766–770 | `LowDegree.FiniteGraphShape.nonInducedCopyCount_top_eq_fallingFactorial_div_aut` | `LowDegree/Combinatorics/EmbeddedCopies.lean` | **Proved** |
| Containment probability `N_Γ(F)\|Aut(F)\|/(n)_v` | prose, lines 772–781 | `LowDegree.FiniteGraphShape.permutationContainmentProbability_concreteCopyEdges` | `LowDegree/Combinatorics/EmbeddedCopies.lean` | **Proved** |
| Exact classwise low-degree norm | Eq. 3.5, `eq:ldlr-2` | `LowDegree.plantedLowDegreeNormSq_sub_one_eq_sum_alphaWeights` | `LowDegree/Combinatorics/GraphShapeClasses.lean` | **Proved** |
| Exact full noised norm | Eq. 3.6, `eq:noise-lr` | `LowDegree.plantedNoisedNormSq_sub_one_eq_sum_noisedAlphaWeights` | `LowDegree/Combinatorics/GraphShapeClasses.lean` | **Proved** |
| Exact ratio `α/β=(1-c/n)^e n^v/(n)_v` and product form | proof of Lemma 3.1, lines 856–866 | `LowDegree.alpha_div_beta_exact`, `LowDegree.leadingRatio_eq_product` | `LowDegree/Asymptotics/LeadingTerm.lean` | **Proved** |
| Low-degree `β` mass is `o(1)` | Eq. 4.1, `eq:beta-low-degree` | `LowDegree.BoundedTreewidthPlantModel.lowDegreeBetaMass_vanishes` | `LowDegree/Asymptotics/BetaMass.lean` | **Proved** |
| `β`-mass target suffices for noised `L²` | Eq. 4.2, `eq:beta-noised-target` | `LowDegree.BoundedTreewidthPlantModel.noisedNormSq_tendsToOne_of_betaMass_vanishes` | `LowDegree/Asymptotics/BetaMass.lean` | **Proved** |
| Restriction/transport map | Eq. 4.3, `eq:isomorphism-map` | `LowDegree.FiniteGraphShape.restrictIsomorphismTriple` | `LowDegree/Combinatorics/GraphCopies.lean` | **Proved** |
| Overlap product bound `β(F)≤n^ov∏β(T_i)` | Eq. 4.4 / overview Eq. 2.1 | `LowDegree.FiniteGraphShape.graphBetaWeight_le_overlap_mul_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | **Proved for concrete non-induced graph copies** |
| Aggregate restriction injection over the disjoint union of all `F` | Lemma 4.3 | `LowDegree.AggregateGraphRestriction.FixedPieceClassDecomposition.encode_injective` | `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Proved** |
| Connected-component product injection and geometric-series estimate | proof of Lemma 4.5 | `LowDegree.GraphComponentExpansion.componentTriples_injective`, `LowDegree.BoundedTreewidthPlantModel.noisedBetaMass_le_geometric_connectedNoisedBetaMass` | `LowDegree/Combinatorics/GraphComponentExpansion.lean` | **Proved** |
| Select `l_n` with `3l_n≤D_n` and `(k_n+1)log n=o(l_n)` after zero-width repair | proof of Lemma 4.6 | `LowDegree.TreewidthDegreeScale.exists_intermediateScale` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Small connected-support contribution | Eq. 4.5, `eq:upper-bound-small` | `LowDegree.BoundedTreewidthPlantModel.smallConnectedNoisedBetaMass_vanishes` | `LowDegree/Asymptotics/ConnectedBetaMass.lean` | **Proved** |
| Large connected-support contribution | Eq. 4.6, `eq:upper-bound-big` | `LowDegree.BoundedTreewidthPlantModel.eventually_largeConnectedNoisedBetaMass_le_geometricTail` | `LowDegree/Asymptotics/LargeConnectedBetaMass.lean` | **Proved** |
| TV/chi-square inequality and sequence-level certificate | proof of Theorem 1.1, lines 1280–1285 | `LowDegree.FiniteLaw.tv_le_half_sqrt_chiSq`, `LowDegree.SecondMomentCertificate.ofLikelihood` | `LowDegree/Probability/Finite.lean`, `LowDegree/Main.lean` | **Proved** |
| Short-girth path uniqueness | proof of Lemma 4.7 | `LowDegree.PercolatedAcyclic.path_eq_of_no_cycle_copy_le` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Cycle encoding count `\|C_k(Γ_n)\|≤n^(k/r_n+1)` | proof of Lemma 4.7 | `LowDegree.PercolatedAcyclic.cycleCopy_card_le_checkpoint_pow` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Geometric survival-probability sum | proof of Lemma 4.7 | `LowDegree.PercolatedAcyclic.checkpoint_sum_le_exponential_envelope`, `LowDegree.PercolatedAcyclic.exponential_envelope_vanishes_of_log_isLittleO` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Forest truncation differs only on the cycle event | Eq. 4.7 setup, lines 1367–1386 | `LowDegree.noisedPlantedLaw_tv_forestTruncated_le_cycleProbability` | `LowDegree/ForestTruncation.lean` | **Proved** |
| Forest-truncated Fourier coefficients are dominated; cyclic supports vanish | lines 1392–1417 | `LowDegree.fourierCoeff_forestTruncatedLikelihood_le_noisedLikelihood`, `LowDegree.fourierCoeff_forestTruncatedLikelihood_eq_zero_of_cyclic` | `LowDegree/ForestTruncation.lean` | **Proved** |
| Tree-support noised mass target | Eq. 4.8, `eq:truncated-sum-goal` | `LowDegree.BoundedTreewidthPlantModel.forestNoisedBetaMass_vanishes_of_connectedForestNoisedBetaMass` | `LowDegree/Asymptotics/ForestComponentExpansion.lean` | **Proved** |
| Treewidth monotonicity under subgraphs | prose, lines 1445–1448 | `LowDegree.TreeDecomposition.treewidth_mono_subgraph` | `LowDegree/Combinatorics/TreeDecomposition.lean` | **Proved** |
| Overlap as cluster-incidence excess | Eq. 5.1, `eq:overlap-decomposition` | `LowDegree.TreeDecomposition.OrderedEdgeDecomposition.overlap_eq_sum_multiplicity_sub_one`, `vertexMultiplicity_eq_card_pieceClusters` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Cluster incidence bounded by quotient-subtree edges | Eq. 5.2, `eq:overlap-decomposition-edge` | `LowDegree.TreeDecomposition.ClusterQuotientWitness.multiplicity_sub_one_le_charge` | `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Each quotient interface repeats at most `k+1` graph vertices | proof of Proposition 5.1, lines 1596–1606 | `LowDegree.TreeDecomposition.ClusterQuotientWitness.charge_interface_bound` | `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Exact edge/support/degree transport under isolated padding | proof interface for Lemma A.1 | `ambientGraph_edgeCard_preserved`, `ambientGraph_hasSupportCardAtMost`, `ambientGraph_hasMaximumDegreeAtMost` | `LowDegree/DeterministicWitnessAdapters.lean` | **Proved** |
| Pulling an occurring shape back to the source plant | proof of Theorem A.2 | `FiniteGraphShape.pullbackMappedCopy`, `DeterministicPlantWitness.sourceCopyOfAmbientConcreteCopy`, `card_pullback_ambientConcreteCopyEdges` | `LowDegree/DeterministicWitnessAdapters.lean` | **Proved** |
| Local sparsity and logarithmic girth for every occurring low-degree connected shape | proof of Theorem A.2 | `eventually_occurringConnectedShape_restrictions` | `LowDegree/DeterministicWitnessAdapters.lean` | **Proved and instantiated by the unconditional A.1 witness** |
| Exact deterministic connected-shape sum and labelled-copy estimate | proof of Lemma A.3 | `connectedShapeTripleMass_eq_sum_copy_mul_labelledCopyCount`, `connectedEmbeddingCountBound_of_supportCard_maxDegree` | `LowDegree/DeterministicConnectedCount.lean` | **Proved** |
| Connected-copy enumeration bound | proof of Lemma A.3 | `connectedConcreteCopySumBound_of_supportCard_maxDegree` | `LowDegree/DeterministicConnectedCount.lean` | **Proved unconditionally by a doubled-edge-tour injection** |
| Zero-edge extension of the connected-shape bound | adapter for Theorem A.2's all-degree input | `connectedShapeTripleMass_zero` | `LowDegree/DeterministicConnectedCount.lean` | **Proved** |
| Connected-component cutoff expansion | proof of Theorem A.2 | `cutoffBetaMass_le_geometric_connectedCutoffBetaMass`, `cutoffBetaMass_vanishes_of_connected` | `LowDegree/Combinatorics/CutoffComponentExpansion.lean` | **Proved** |
| Tree and cyclic connected-fiber estimates | proof of Theorem A.2 | `deterministicTreeCutoffBetaMass_le_geometric`, `deterministicCyclicCutoffBetaMass_le_geometricTail` | `LowDegree/DeterministicLowDegree.lean` | **Proved under the explicit connected-count and occurrence hypotheses** |
| Deterministic scan-test conclusion | proof of Theorem A.2 | `deterministic_statisticalDistinguishability` | `LowDegree/DeterministicStatistical.lean` | **Proved from edge-density and scale hypotheses** |
| Uniform-injection/padded-graph model identification | model bridge for Theorem A.2 | `permutedPlantEdges_map_castLE`, `uniformlyInjected_dirac_eq_uniformlyPermuted_map_castLE`, `DeterministicPlantWitness.deterministicNoisedAlternativeLaw_eq` | `LowDegree/DeterministicModelBridge.lean` | **Proved as exact finite-law equalities** |
| Combined deterministic gap and explicit threshold | Theorem A.2 | `deterministicGap_of_witness`, `deterministicGap_exists_threshold`, `deterministicGap_exists_threshold_uniform_noise` | `LowDegree/DeterministicGapTheorem.lean` | **Proved; threshold is uniform over admissible noise rates** |
| Configuration projection, pruning, and deterministic girth preservation | construction following Lemmas A.4--A.5 | `Configuration.projectedGraph`, `shortCyclePrunedGraph`, `shortCyclePrunedGraph_hasRealGirthAtLeast` | `LowDegree/DeterministicConfiguration.lean` | **Proved** |
| Uniform finite configuration law and positive-probability selection principle | setup for Lemmas A.4--A.5 | `configurationPermutationLaw`, `randomConfiguration`, `FiniteLaw.exists_notMem_three_of_sum_prob_lt_one` | `LowDegree/DeterministicConfigurationProbability.lean` | **Proved** |
| Configuration-model estimates select good configurations and produce the exact A.1 witness | construction after Lemmas A.4--A.5 | `ConfigurationModelEstimates.exists_goodPermutation`, `ConfigurationModelEstimates.toConfigurationSelectionData`, `ConfigurationModelEstimates.toDeterministicPlantWitness` | `LowDegree/DeterministicConfigurationModelBridge.lean` | **Proved conditionally from the three explicit probability/loss estimates** |
| Unconditional assembly of the Appendix A.1 witness | Lemma A.1 | `appendixA1_configurationModelEstimates`, `appendixA1_deterministicPlantWitness`, `appendixA1_evenDegree_deterministicPlantWitness` | `LowDegree/DeterministicConfigurationConstruction.lean` | **Proved; the A.4, A.5, cycle-loss, and projection-defect hypotheses are discharged** |
| Configuration local-sparsity probability estimate | Lemma A.4 | `appendixConfigurationLocalSparsity_probability_tendsto_one`, `appendixConfigurationBadLocal_probability_vanishes`, `configurationInternalLocalSparsityFailure_vanishes` | `LowDegree/DeterministicConfigurationLocalSparsity.lean` | **Proved** |
| Configuration short-cycle expectation/Markov estimate | Lemma A.5 | `appendixA5_evenDegree_fewShortCycles_probability_tendsto_one`, `appendixPlantSize_fewShortCycles_probability_tendsto_one` | `LowDegree/DeterministicConfigurationShortCycles.lean` | **Proved** |
| Distinct-cycle presentations control pruning loss | bridge from Lemma A.5 to Lemma A.1 | `shortCycleEdges_card_cast_le_two_mul_sq_mul_shortCycleCountReal`, `appendixConfigurationBadCycle_probability_vanishes`, `appendixConfigurationShortCycleEdgeBudget_div_vanishes` | `LowDegree/DeterministicConfigurationShortCycles.lean`, `LowDegree/DeterministicConfigurationCutoffBridge.lean` | **Proved** |

Standard library ingredients used throughout include Parseval, Cauchy–Schwarz, Markov, binomial concentration, the union bound, `\binom{N}{K}≤(eN/K)^K`, elementary logarithm inequalities, falling-factorial estimates, and total-variation triangle/coupling bounds. These should be reused from Mathlib when available and wrapped locally only when the paper’s exact normalization differs.

## Faithfulness constraints and their Lean resolutions

| Constraint | Resolution in the current development | Status |
|---|---|---|
| Bernoulli domain for `G(n,c/n)` | `sparseBernoulliParameter` carries a legal finite parameter, while `eventually_sparseBernoulliParameter_p_eq` proves that it is exactly `c/n` on the asymptotic tail. | **Resolved** |
| Cross-referenced low-degree assumptions | Paper-facing theorem types explicitly carry `TendsToOne M.lowDegreeNormSq`, cutoff positivity, and the scale hypotheses they use. | **Resolved** |
| Minimal degree premise in Lemma 3.2 | `BoundedTreewidthPlantModel.degreeCutoff_pos` supplies degree one at every index; the proof does not assume an unstated stronger limit. | **Resolved** |
| Connected versus arbitrary treewidth | `TreeDecomposition.HasTreewidthAtMost` and `treewidth` are defined for arbitrary finite graphs; monotonicity under subgraphs is proved. | **Resolved** |
| Zero numerical treewidth in revised Theorem 1.1 | `plant_eq_bot_of_numericalTreewidth_eq_zero` identifies edgeless plants, and `zeroWidthRepairedDegreeCutoff` supplies the logarithmic scale without changing their likelihood quantities. | **Resolved** |
| Isolated vertices | A smaller plant is represented on `Fin n` by isolated padding, which contributes no ambient edges; `supportShape` strips isolated vertices from Fourier-support indexing graphs. | **Resolved** |
| Graph isomorphism classes | `AmbientSupportClass` gives finite orbit classes, and the classwise norm identities recover the exact copy-count/automorphism weights. | **Resolved** |
| Aggregate restriction across all parent shapes | `AggregateGraphRestriction.FixedPieceClassDecomposition.encode_injective` proves injectivity on the tagged disjoint union and recovers the parent class from its pieces without a finite-type assumption. | **Resolved** |
| Compatible decomposition choices | `FixedPieceClassDecomposition`, `FixedPieceClassDivision`, and the large-class division structures carry decompositions and piece tags as explicit witness data. | **Resolved** |
| Theorem 1.2 concludes TV only | `subcritical_lowDegree_to_tv` has exactly the printed TV conclusion and uses the forest-truncated comparison. | **Resolved** |
| Whole-plant forest truncation | `forestTruncatedRetainedPlantLaw` replaces a cyclic retained plant by the empty edge set; its coefficient domination and coupling bounds use that semantics. | **Resolved** |
| Revised Appendix quantifier order for `A` and `κ` | `DeterministicPlantWitness` chooses `A`, `κ`, and the graph sequence before exposing their four properties; `appendixA1_evenDegree_deterministicPlantWitness` constructs that package under the printed parameter order. | **Resolved** |
| Lemma A.1 at `n=1` | The TeX expression `A/\log n` is undefined at `n=1`, while its quantified set range is empty because `m_1=1`. The Lean local-sparsity field therefore records the mathematically active assertion for `n\ge2`; the construction patches the finite prefix explicitly. | **Resolved with an explicit domain guard** |
| Fixed parameters and filters | Asymptotic declarations use `atTop`, `Vanishes`, `TendsToOne`, `Omega`, and `TendstoInProbability` with paper parameters fixed outside the limit. | **Resolved** |
| Uniformity in Lemma 3.1 | `UniformlyTendsToOneOn` and the occurring-shape adapter state one uniform eventual bound over the changing support family. | **Resolved** |
| Finite support of graph sums | `AmbientSupportClass`, concrete-copy fibers, and explicit `Finset` regrouping make every paper sum finite. | **Resolved** |
| Redundant premise in Lemma 4.5 | `clusterExpansion_bound` preserves the printed premise; `clusterExpansion_bound_core` is the premise-minimized helper. | **Resolved** |
| Exact TV, factorial, copy, and automorphism normalizations | `FiniteLaw.tv`, `fallingFactorial`, `nonInducedCopyCount`, and `FiniteGraphShape.Automorphism` are used by the proved identities. | **Resolved** |
| Small-`n` denominators | Occurrence and ambient-cardinality lemmas provide `v(F)≤n`; the leading-term proofs carry the required nonzero hypotheses explicitly. | **Resolved** |
| Revised Theorem A.2 parameter dependence | `deterministicGap_exists_threshold_uniform_noise` constructs `c₀>1` from the Lemma A.1 witness before quantifying the noise rate, so the threshold depends on `D,r,γ` but not `ε`; the fixed-noise wrapper matches the manuscript's quantifier order. | **Resolved** |

## Suggested update policy

When a declaration is added, update only its **Proof status** (`Planned` → `Statement formalized` → `Proved`), and link the declaration if useful. Change **Statement fidelity** only after comparing the Lean type directly with the source snapshot above. Any intentional strengthening or normalization lemma should be recorded as an auxiliary result, not substituted silently for the paper-facing wrapper.
