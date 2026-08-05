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

- **Statement fidelity** records how the Lean declaration relates to the
  printed mathematical statement. “Exact + guards” means the same asymptotic
  assertion with domain facts that TeX leaves implicit, such as `c / n ≤ 1`
  eventually.
- **Proof status** records implementation progress only. **Proved** means the
  declaration has a Lean proof with no `sorry`, `admit`, or project axiom.

## Numbered statements

| Paper statement | Source label / lines | Lean declaration | Module | Statement fidelity | Proof status |
|---|---|---|---|---|---|
| Theorem 1.1, “Low-degree consequence for bounded-treewidth plants” | `thm:main`, 234–259 | `LowDegree.main_lowDegree_to_noisedL2_and_tv`; `LowDegree.BoundedTreewidthPlantModel.main_lowDegree_to_noisedL2_and_tv_statement_proved` | `LowDegree/BoundedTreewidthTheorem.lean` | Exact model-facing theorem, with `tw(Γₙ) ≤ kₙ`, positive `Dₙ`, and pointwise fixed-noise quantification. Both noised `L²=1+o(1)` and TV `=o(1)` are retained. | **Proved** |
| Theorem 1.2, “Critical and subcritical backgrounds” | `thm:subcritical`, 280–287 | `LowDegree.subcritical_lowDegree_to_tv` | `LowDegree/Asymptotics/ForestLargeConnectedBetaMass.lean` | Exact + Bernoulli guards. The conclusion is TV only, as printed. | **Proved** |
| Lemma 3.1, uniform leading-term comparison | `lem:leading-term`, 840–853 | `LowDegree.alpha_div_beta_tendsto_uniformly`, `LowDegree.alpha_div_graphBeta_tendsto_uniformly_on_occurringShapes` | `LowDegree/Asymptotics/LeadingTerm.lean`, `LowDegree/Asymptotics/ModelConsequences.lean` | Exact uniform little-`o` statement, including the adapter for nonempty support shapes that actually occur in the ambient plant; the eventual `1/2` and `2` bounds are also proved. | **Proved** |
| Lemma 3.2, edge-count consequence | `lem:edge`, 885–893 | `LowDegree.BoundedTreewidthPlantModel.edgeCount_isLittleO_sqrt` | `LowDegree/Asymptotics/ModelConsequences.lean` | Exact for the model-realized planted likelihood and projected norm; `degreeCutoff_pos` includes degree one (in fact at every index), and the sparse parameter is proved equal to `c/n` eventually. | **Proved** |
| Lemma 3.3, exclusion of short cycles | `lem:girth`, 919–929 | `LowDegree.BoundedTreewidthPlantModel.no_shortCycles_of_lowDegree` | `LowDegree/Asymptotics/NoShortCycles.lean` | Exact simultaneous eventual statement for every integer `3 ≤ l ≤ D_n`, proved from the concrete model Parseval sum for `0<c≤1`. | **Proved** |
| Lemma 4.1, isomorphism-triple count | `lem:isomorphism-triples`, 1023–1033 | `LowDegree.FiniteGraphShape.card_isomorphismTriplesIn`, `LowDegree.FiniteGraphShape.graphBetaWeight_eq_betaFromTriple` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact finite identities for concrete non-induced graph copies, `|Tri(F)|`, and `β_n(F)`. | **Proved** |
| Lemma 4.2, restriction map injection | `lem:map-injection`, 1076–1083 | `LowDegree.FiniteGraphShape.restrictIsomorphismTriple_injective`, `LowDegree.FiniteGraphShape.copyCount_sq_mul_aut_le_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | Exact concrete restriction/transport map, injectivity proof, and expanded copy-count product bound. | **Proved** |
| Lemma 4.3, bounded treewidth implies divisibility | `lem:decomposition`, 1136–1139 | `LowDegree.TreeDecomposition.isDivisible_of_hasTreewidthAtMost` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | Exact `(l,3,k+1)` divisibility, using the arbitrary-graph treewidth convention. | **Proved** |
| Lemma 4.4, cluster expansion | `lem:cluster-expansion`, 1150–1159 | `LowDegree.clusterExpansion_bound` | `LowDegree/Main.lean` | Exact printed wrapper, including its redundant low-degree premise; `clusterExpansion_bound_core` is the premise-minimized helper. | **Proved** |
| Lemma 4.5, connected noised mass | `lem:connect-upper-bound`, 1193–1201 | `LowDegree.BoundedTreewidthPlantModel.connectedNoisedBetaMass_vanishes` | `LowDegree/Asymptotics/LargeConnectedBetaMass.lean` | Exact model-facing connected-mass conclusion, using the selected bounded-overlap divisions and the treewidth/degree scale. | **Proved** |
| Lemma 4.6, no cycle after deletion | `lem:no-cycle`, 1291–1302 | `LowDegree.PercolatedAcyclic.BoundedTreewidthPlantModel.retainedPlantCycleProbability_vanishes` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | Exact vanishing of the retained-plant cycle-event probability. | **Proved** |
| Proposition 5.1, bounded-overlap edge decomposition | `prop:treewidth-division`, 1449–1464 | `LowDegree.TreeDecomposition.exists_boundedOverlap_orderedEdgeDecomposition` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | Exact finite existence theorem with piece sizes in `[l,3l]` and overlap at most `(k+1)(m-1)`. | **Proved** |
| Definition 5.2, tree decomposition and treewidth | unlabeled, 1473–1490 | `LowDegree.TreeDecomposition.Decomposition`, `LowDegree.TreeDecomposition.Decomposition.WidthAtMost`, `LowDegree.TreeDecomposition.treewidth` | `LowDegree/Combinatorics/TreeDecomposition.lean` | Exact minimum-width definition for arbitrary finite graphs, hence also for the printed connected specialization. | **Proved** |
| Lemma 5.3, subcubic edge-owned refinement | `lem:decomposition-refinement`, 1492–1505 | `LowDegree.TreeDecomposition.exists_edgeOwnedRefinement_of_hasTreewidthAtMost` | `LowDegree/Combinatorics/EdgeOwnedRefinement.lean` | Exact finite edge-owned subcubic refinement, preserving the width bound. | **Proved** |
| Lemma 5.4, partition of a weighted subcubic tree | `lem:partition-tree`, 1540–1548 | `LowDegree.WeightedTreePartitionTheorem.exists_vertexPartitionWitness` | `LowDegree/Combinatorics/WeightedTreePartitionTheorem.lean` | Exact label-preserving partition: connected original-vertex fibers, exact contraction quotient tree, and weights in `[l,3l]`. | **Proved** |
| Theorem A.1, randomized supercritical gap | `thm:supercritical-gap`, 1666–1680 | `LowDegree.appendix_supercritical_gap_canonical` | `LowDegree/SupercriticalGapTheorem.lean` | Exact canonical theorem for the actual twice-truncated, uniformly injected plant. One `c₀=c₀(λ,r,γ)>1`, chosen before `ε`, works for every admissible noise rate and every fixed `c≥c₀`; both the low-degree `L²=1+o(1)` and noised TV `=1-o(1)` conclusions are packaged together, with `Dₙ=ω(log n)`. | **Proved** |
| Lemma A.2, local-sparsity event | `lem:supercritical-local-sparsity`, 1687–1694 | `LowDegree.exists_localSparsitySlackConstant`, `LowDegree.sparseErdosRenyi_localSparsity_tendsToOne` | `LowDegree/SupercriticalLocalSparsity.lean` | Exact existential choice `A=A(λ,r,γ)` with probability `1-o(1)`. | **Proved** |
| Lemma A.3, edge density after pruning | `lem:supercritical-pruning`, 1833–1840 | `LowDegree.appendix_locallyTruncatedPruned_edgeDensity_tendstoInProbability` | `LowDegree/SupercriticalCanonicalScales.lean` | Exact twice-truncated conclusion at the canonical scales, built from Bernoulli edge-density concentration, short-cycle pruning, and the rare local-sparsity truncation. | **Proved** |

## Proof-critical definitions

These prose definitions are part of statement fidelity even though most are not numbered environments.

| Paper object | Lean object(s) | Module | Status |
|---|---|---|---|
| Fixed noise rates, `(kₙ+1)log n=o(Dₙ)`, and the model-realized Theorem 1.1 profile/conclusion | `NoiseRate`, `TreewidthDegreeScale`, `BoundedTreewidthPlantModel`, `FixedNoiseConclusion` | `LowDegree/Asymptotics/Basic.lean`, `LowDegree/Main.lean`, `LowDegree/BoundedTreewidthTheorem.lean` | **Formalized and used by the proved theorem** |
| `Q_n=G(n,c/n)`, deterministic plant kernel `P_n`, random injection, union with background | `SparseBernoulliFamily`, `AmbientEdge`, `permutedPlantEdges`, `erdosRenyiLaw`, `plantedLaw` | `LowDegree/PlantedModel.lean` | **Formalized at the density level, with exact `c/n` proved eventually** |
| Edge resampling/deletion and noised planted law | `edgeNoise`, `resampleLaw`, `noisedPlantedLaw`, `deletedPlantedLaw` | `LowDegree/Fourier.lean`, `LowDegree/PlantedModel.lean`, `LowDegree/DeletedPlant.lean` | **Formalized, including exact deletion-before-superposition/resampling equivalence** |
| Likelihood ratios `L_n`, `L_{n,ε}` | `plantedLikelihood`, `noisedLikelihood`, `plantedLikelihood_isLikelihoodRatio`, `noisedLikelihood_isLikelihoodRatio` | `LowDegree/PlantedModel.lean` | **Formalized** |
| Degree-`D` Fourier subspace and orthogonal projection | `lowDegreeProjection`, `fourierCoeff_lowDegreeProjection`, `lowDegreeProjection_norm_sq` | `LowDegree/Fourier.lean` | **Formalized in the finite Fourier basis** |
| Bernoulli characters `r_e`, `χ_S`, Fourier coefficients | `edgeCharacter`, `fourierCharacter`, `fourierCoeff` | `LowDegree/Fourier.lean` | **Formalized** |
| Embedded/concrete copies, `N_Γ(F)`, automorphisms, `(n)_v` | `FiniteGraphShape.ConcreteCopy`, `nonInducedCopyCount`, `copyIsomorphismEquivAutomorphism`, `fallingFactorial` | `LowDegree/Combinatorics/GraphCopies.lean`, `LowDegree/Combinatorics/EmbeddedCopies.lean`, `LowDegree/Asymptotics/LeadingTerm.lean` | **Formalized with non-induced copy semantics** |
| Exact and leading weights `α_n(F)`, `β_n(F)` | `alphaWeight`, `betaWeight`, `FiniteGraphShape.graphBetaWeight` | `LowDegree/Asymptotics/LeadingTerm.lean`, `LowDegree/Combinatorics/GraphCopies.lean` | **Formalized** |
| Ordered edge decomposition and compatibility data | `TreeDecomposition.OrderedEdgeDecomposition`, `AggregateGraphRestriction.FixedPieceClassDivision` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Formalized; compatible choices are carried as witness data** |
| Isomorphism triples and restriction/transport | `FiniteGraphShape.IsomorphismTripleIn`, `FiniteGraphShape.restrictIsomorphismTriple`, `AggregateGraphRestriction.FixedPieceClassDivision.encode` | `LowDegree/Combinatorics/GraphCopies.lean`, `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Formalized** |
| Vertex overlap | `TreeDecomposition.OrderedEdgeDecomposition.overlap` | `LowDegree/Combinatorics/TreeDecomposition.lean` | **Formalized** |
| `(l,C,a)`-divisibility | `TreeDecomposition.IsDivisible` | `LowDegree/Combinatorics/BoundedOverlapDivision.lean` | **Formalized** |
| Connected noised mass `θ_{n,ε}` | `BoundedTreewidthPlantModel.connectedNoisedBetaMass` | `LowDegree/Asymptotics/ConnectedBetaMass.lean` | **Formalized** |
| Cycle collections and deletion-percolated plant | `CycleEmbedding`, `retainedPlantLaw`, `retainedPlantCycleProbability` | `LowDegree/SupercriticalPruning.lean`, `LowDegree/ForestTruncation.lean` | **Formalized** |
| Forest truncation that replaces a cyclic retained plant by the empty graph | `IsForestEdgeSet`, `forestTruncatedRetainedPlantLaw`, `forestTruncatedObservationLaw` | `LowDegree/ForestTruncation.lean` | **Formalized with the manuscript's whole-plant truncation semantics** |
| Tree bags, width, ownership, connected cluster contraction, quotient tree | `TreeDecomposition.Decomposition`, `TreeDecomposition.EdgeOwnedRefinementWitness`, `TreeDecomposition.ClusterQuotientWitness`, `WeightedTreePartitionTheorem.VertexPartitionWitness` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/EdgeOwnedRefinement.lean`, `LowDegree/Combinatorics/WeightedTreePartitionTheorem.lean` | **Formalized, including a label-preserving quotient** |
| Appendix `E_n`, `Ĥ_n`, `H_n^tr`, `P_n^sc`, and scan statistic `M_n` | `localSparsityEvent`, `shortCyclePrunedEdges`, `twiceTruncatedPlantLawAt`, `appendixInjectedTruncatedPlantLaw`, `graphScanStatistic` | `LowDegree/SupercriticalLocalSparsity.lean`, `LowDegree/SupercriticalStatistical.lean` | **Formalized** |

## Proof-critical identities and auxiliary lemmas

Overview equations 2.1 and 2.2 are expository versions of Eq. 4.4 and Proposition 5.1 respectively; they map to the same declarations rather than duplicate theorems.

| Paper identity or proof step | Source | Lean declaration | Module | Proof status |
|---|---|---|---|---|
| Scale condition implies `Dₙ=ω(log n)` | prose following Theorem 1.1, lines 261–275 | `LowDegree.TreewidthDegreeScale.degree_isOmega_log` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Low-degree variational identity | Eq. 1.1, `eq:intro-low-degree-advantage` | `LowDegree.lowDegree_advantage_identity` | `LowDegree/LowDegreeAdvantage.lean` | **Proved** |
| Noise preserves the null law | prose, lines 213–219 and 600–609 | `LowDegree.resampleLaw_erdosRenyiLaw` | `LowDegree/PlantedModel.lean` | **Proved** |
| Noise multiplies a degree-`d` Fourier coefficient by `(1-ε)^d` | prose, lines 159–161 | `LowDegree.fourierCoeff_edgeNoise` | `LowDegree/Fourier.lean` | **Proved** |
| Resampling a monotone plant equals deletion before superposition | prose, lines 213–219 and 600–609 | `LowDegree.deletedPlantedLikelihood_eq_noisedLikelihood`, `LowDegree.deletedPlantedLaw_eq_noisedPlantedLaw` | `LowDegree/DeletedPlant.lean` | **Proved** |
| Bernoulli characters form an orthonormal basis | prose preceding Eq. 3.1 | `LowDegree.fourierCharacters_orthonormal`, `LowDegree.fourierExpansion` | `LowDegree/Fourier.lean` | **Proved in an equivalent finite-basis form** |
| Fourier expansion and degree projection | Eq. 3.1, `eq:fourier-expansion-1` | `LowDegree.fourierExpansion`, `LowDegree.fourierCoeff_lowDegreeProjection` | `LowDegree/Fourier.lean` | **Proved** |
| Parseval expression for the projected norm | Eq. 3.2, `eq:ldlr-1` | `LowDegree.lowDegreeProjection_norm_sq` | `LowDegree/Fourier.lean` | **Proved** |
| Fixed-copy conditional likelihood expansion | Eq. 3.3, `eq:conditioned-likelihood` | `LowDegree.forcedLikelihood_fourierExpansion` | `LowDegree/Fourier.lean` | **Proved** |
| Mixture likelihood coefficients | Eq. 3.4, `eq:likelihood-expansion` | `LowDegree.fourierCoeff_plantedLikelihood`, `LowDegree.fourierCoeff_noisedLikelihood` | `LowDegree/PlantedModel.lean` | **Proved** |
| Number of embedded copies `(n)_v/|Aut(F)|` | prose, lines 766–770 | `LowDegree.FiniteGraphShape.nonInducedCopyCount_top_eq_fallingFactorial_div_aut` | `LowDegree/Combinatorics/EmbeddedCopies.lean` | **Proved** |
| Containment probability `N_Γ(F)|Aut(F)|/(n)_v` | prose, lines 772–781 | `LowDegree.FiniteGraphShape.permutationContainmentProbability_concreteCopyEdges` | `LowDegree/Combinatorics/EmbeddedCopies.lean` | **Proved** |
| Exact classwise low-degree norm | Eq. 3.5, `eq:ldlr-2` | `LowDegree.plantedLowDegreeNormSq_sub_one_eq_sum_alphaWeights` | `LowDegree/Combinatorics/GraphShapeClasses.lean` | **Proved** |
| Exact full noised norm | Eq. 3.6, `eq:noise-lr` | `LowDegree.plantedNoisedNormSq_sub_one_eq_sum_noisedAlphaWeights` | `LowDegree/Combinatorics/GraphShapeClasses.lean` | **Proved** |
| Exact ratio `α/β=(1-c/n)^e n^v/(n)_v` and product form | proof of Lemma 3.1, lines 856–866 | `LowDegree.alpha_div_beta_exact`, `LowDegree.leadingRatio_eq_product` | `LowDegree/Asymptotics/LeadingTerm.lean` | **Proved** |
| Low-degree `β` mass is `o(1)` | Eq. 4.1, `eq:beta-low-degree` | `LowDegree.BoundedTreewidthPlantModel.lowDegreeBetaMass_vanishes` | `LowDegree/Asymptotics/BetaMass.lean` | **Proved** |
| `β`-mass target suffices for noised `L²` | Eq. 4.2, `eq:beta-noised-target` | `LowDegree.BoundedTreewidthPlantModel.noisedNormSq_tendsToOne_of_betaMass_vanishes` | `LowDegree/Asymptotics/BetaMass.lean` | **Proved** |
| Restriction/transport map | Eq. 4.3, `eq:isomorphism-map` | `LowDegree.FiniteGraphShape.restrictIsomorphismTriple` | `LowDegree/Combinatorics/GraphCopies.lean` | **Proved** |
| Overlap product bound `β(F)≤n^ov∏β(T_i)` | Eq. 4.4 / overview Eq. 2.1 | `LowDegree.FiniteGraphShape.graphBetaWeight_le_overlap_mul_prod` | `LowDegree/Combinatorics/GraphCopies.lean` | **Proved for concrete non-induced graph copies** |
| Aggregate restriction injection over the disjoint union of all `F` | prose in Lemma 4.5 proof, lines 1244–1256 | `LowDegree.AggregateGraphRestriction.FixedPieceClassDivision.encode_injective` | `LowDegree/Combinatorics/AggregateGraphRestriction.lean` | **Proved** |
| Connected-component product injection and geometric-series estimate | proof of Lemma 4.4 | `LowDegree.GraphComponentExpansion.componentTriples_injective`, `LowDegree.BoundedTreewidthPlantModel.noisedBetaMass_le_geometric_connectedNoisedBetaMass` | `LowDegree/Combinatorics/GraphComponentExpansion.lean` | **Proved** |
| Select `l_n` with `3l_n≤D_n` and `(k_n+1)log n=o(l_n)` | proof of Lemma 4.5, lines 1203–1209 | `LowDegree.TreewidthDegreeScale.exists_intermediateScale` | `LowDegree/Asymptotics/Basic.lean` | **Proved** |
| Small connected-support contribution | Eq. 4.5, `eq:upper-bound-small` | `LowDegree.BoundedTreewidthPlantModel.smallConnectedNoisedBetaMass_vanishes` | `LowDegree/Asymptotics/ConnectedBetaMass.lean` | **Proved** |
| Large connected-support contribution | Eq. 4.6, `eq:upper-bound-big` | `LowDegree.BoundedTreewidthPlantModel.eventually_largeConnectedNoisedBetaMass_le_geometricTail` | `LowDegree/Asymptotics/LargeConnectedBetaMass.lean` | **Proved** |
| TV/chi-square inequality and sequence-level certificate | proof of Theorem 1.1, lines 1280–1285 | `LowDegree.FiniteLaw.tv_le_half_sqrt_chiSq`, `LowDegree.SecondMomentCertificate.ofLikelihood` | `LowDegree/Probability/Finite.lean`, `LowDegree/Main.lean` | **Proved** |
| Short-girth path uniqueness | proof of Lemma 4.6, lines 1311–1318 | `LowDegree.PercolatedAcyclic.path_eq_of_no_cycle_copy_le` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Cycle encoding count `|C_k(Γ_n)|≤n^(k/r_n+1)` | proof of Lemma 4.6, lines 1320–1343 | `LowDegree.PercolatedAcyclic.cycleCopy_card_le_checkpoint_pow` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Geometric survival-probability sum | proof of Lemma 4.6, lines 1344–1361 | `LowDegree.PercolatedAcyclic.checkpoint_sum_le_exponential_envelope`, `LowDegree.PercolatedAcyclic.exponential_envelope_vanishes_of_log_isLittleO` | `LowDegree/Asymptotics/PercolatedAcyclic.lean` | **Proved** |
| Forest truncation differs only on the cycle event | Eq. 4.7 setup, lines 1367–1386 | `LowDegree.noisedPlantedLaw_tv_forestTruncated_le_cycleProbability` | `LowDegree/ForestTruncation.lean` | **Proved** |
| Forest-truncated Fourier coefficients are dominated; cyclic supports vanish | lines 1392–1417 | `LowDegree.fourierCoeff_forestTruncatedLikelihood_le_noisedLikelihood`, `LowDegree.fourierCoeff_forestTruncatedLikelihood_eq_zero_of_cyclic` | `LowDegree/ForestTruncation.lean` | **Proved** |
| Tree-support noised mass target | Eq. 4.8, `eq:truncated-sum-goal` | `LowDegree.BoundedTreewidthPlantModel.forestNoisedBetaMass_vanishes_of_connectedForestNoisedBetaMass` | `LowDegree/Asymptotics/ForestComponentExpansion.lean` | **Proved** |
| Treewidth monotonicity under subgraphs | prose, lines 1445–1448 | `LowDegree.TreeDecomposition.treewidth_mono_subgraph` | `LowDegree/Combinatorics/TreeDecomposition.lean` | **Proved** |
| Overlap as cluster-incidence excess | Eq. 5.1, `eq:overlap-decomposition` | `LowDegree.TreeDecomposition.OrderedEdgeDecomposition.overlap_eq_sum_multiplicity_sub_one`, `vertexMultiplicity_eq_card_pieceClusters` | `LowDegree/Combinatorics/TreeDecomposition.lean`, `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Cluster incidence bounded by quotient-subtree edges | Eq. 5.2, `eq:overlap-decomposition-edge` | `LowDegree.TreeDecomposition.ClusterQuotientWitness.multiplicity_sub_one_le_charge` | `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Each quotient interface repeats at most `k+1` graph vertices | proof of Proposition 5.1, lines 1596–1606 | `LowDegree.TreeDecomposition.ClusterQuotientWitness.charge_interface_bound` | `LowDegree/Combinatorics/ClusterInterfaceCharging.lean` | **Proved** |
| Local-sparsity event | Eq. A.1, `eq:supercritical-local-sparsity` | `LowDegree.localSparsityEvent`, `LowDegree.mem_localSparsityEvent_iff_real` | `LowDegree/SupercriticalLocalSparsity.lean` | **Formalized** |
| Local-density union bound | Eq. A.4, `eq:supercritical-local-union-bound` | `LowDegree.bernoulliProductLaw_prob_localSparsityFailureEvent_le`, `LowDegree.bernoulliProductLaw_prob_localSparsityFailureEvent_le_twoRange` | `LowDegree/SupercriticalLocalSparsity.lean` | **Proved** |
| Exact randomized-plant low-degree Parseval sum | Eq. A.5, `eq:supercritical-parseval` | `LowDegree.appendixLowDegreeNormSq_sub_one_eq_sum_nonempty`, `LowDegree.appendixLowDegreeNormSq_sub_one_eq_sum_supportClasses` | `LowDegree/SupercriticalLowDegree.lean` | **Proved for the actual appendix law** |
| Randomized containment upper bound | Eq. A.6, `eq:supercritical-containment` | `LowDegree.uniformlyInjected_twiceTruncated_containment_le_original`, `LowDegree.uniformlyInjected_erdosRenyi_containment_eq_pow_mul_fitProbability`, `LowDegree.uniformPermutationLaw_prob_ambientSupportFitEvent_le_pow_div`, `LowDegree.appendixA6PowBound_actual` | `LowDegree/SupercriticalInjectionBounds.lean`, `LowDegree/SupercriticalLowDegree.lean` | **Proved for the actual appendix law** |
| Local excess restriction | Eq. A.7, `eq:supercritical-excess` | `LowDegree.eventually_positive_appendixContainment_localSparsity` | `LowDegree/SupercriticalShapeRestrictions.lean` | **Proved for the actual appendix law** |
| Girth/vertex restriction | Eq. A.8, `eq:supercritical-girth-restriction` | `LowDegree.appendixCycleCutoff_lt_supportShape_vertexCount_of_positive_containment` | `LowDegree/SupercriticalShapeRestrictions.lean` | **Proved for the actual appendix law** |
| Supercritical graph-enumeration bound | Eq. A.9, `eq:supercritical-enumeration` | `LowDegree.appendixA9Bound_of_A6PowBound` | `LowDegree/SupercriticalLowDegree.lean` | **Proved from (A.5)--(A.8) for the actual appendix law** |
| Factorial/binomial graph-count bound | Eq. A.10, `eq:supercritical-counting-bound` | `LowDegree.appendixGraphCountingFactor_le` | `LowDegree/SupercriticalCountingBound.lean` | **Proved** |
| Forest-like part of low-degree sum | Eq. A.11, `eq:super-critical-sum-1` | `LowDegree.sum_appendixA9ForestEdges_le` | `LowDegree/SupercriticalLowDegree.lean` | **Proved** |
| Cyclic/excess part of low-degree sum | Eq. A.12, `eq:super-critical-sum-2` | `LowDegree.sum_appendixA9CyclicEdges_le`, `LowDegree.appendixEnumerationEnvelope_vanishes` | `LowDegree/SupercriticalLowDegree.lean` | **Proved** |
| Expected number of edges removed by short-cycle pruning is polylogarithmic | proof of Lemma A.3, lines 1842–1854 | `LowDegree.expected_shortCyclePruning_removedEdges_le_envelope` | `LowDegree/SupercriticalPruning.lean` | **Proved** |
| Pruning removes `o_P(m_n)` edges | proof of Lemma A.3 | `LowDegree.shortCyclePruning_removedEdges_isLittleOInProbability` | `LowDegree/SupercriticalPruning.lean` | **Proved** |
| Null scan-statistic tail tends to zero | proof of Eq. A.3, lines 1861–1898 | `LowDegree.appendix_nullScan_vanishes` | `LowDegree/SupercriticalStatistical.lean` | **Proved** |
| Planted scan-statistic power tends to one | proof of Eq. A.3, lines 1899–1910 | `LowDegree.appendix_plantedScan_tendsToOne` | `LowDegree/SupercriticalStatistical.lean` | **Proved** |

Standard library ingredients used throughout include Parseval, Cauchy–Schwarz, Markov, binomial concentration, the union bound, `\binom{N}{K}≤(eN/K)^K`, elementary logarithm inequalities, falling-factorial estimates, and total-variation triangle/coupling bounds. These should be reused from Mathlib when available and wrapped locally only when the paper’s exact normalization differs.

## Faithfulness constraints and their Lean resolutions

| Constraint | Resolution in the current development | Status |
|---|---|---|
| Bernoulli domain for `G(n,c/n)` | `sparseBernoulliParameter` carries a legal finite parameter, while `eventually_sparseBernoulliParameter_p_eq` proves that it is exactly `c/n` on the asymptotic tail. | **Resolved** |
| Cross-referenced low-degree assumptions | Paper-facing theorem types explicitly carry `TendsToOne M.lowDegreeNormSq`, cutoff positivity, and the scale hypotheses they use. | **Resolved** |
| Minimal degree premise in Lemma 3.2 | `BoundedTreewidthPlantModel.degreeCutoff_pos` supplies degree one at every index; the proof does not assume an unstated stronger limit. | **Resolved** |
| Connected versus arbitrary treewidth | `TreeDecomposition.HasTreewidthAtMost` and `treewidth` are defined for arbitrary finite graphs; monotonicity under subgraphs is proved. | **Resolved** |
| Isolated vertices | A smaller plant is represented on `Fin n` by isolated padding, which contributes no ambient edges; `supportShape` strips isolated vertices from Fourier-support indexing graphs. | **Resolved** |
| Graph isomorphism classes | `AmbientSupportClass` gives finite orbit classes, and the classwise norm identities recover the exact copy-count/automorphism weights. | **Resolved** |
| Aggregate restriction across all parent shapes | `AggregateGraphRestriction.FixedPieceClassDivision.encode_injective` proves injectivity on the tagged disjoint union and recovers the parent class from its pieces. | **Resolved** |
| Compatible decomposition choices | `FixedPieceClassDivision` and the large-class division structures carry decompositions and piece tags as explicit witness data. | **Resolved** |
| Theorem 1.2 concludes TV only | `subcritical_lowDegree_to_tv` has exactly the printed TV conclusion and uses the forest-truncated comparison. | **Resolved** |
| Whole-plant forest truncation | `forestTruncatedRetainedPlantLaw` replaces a cyclic retained plant by the empty edge set; its coefficient domination and coupling bounds use that semantics. | **Resolved** |
| Appendix choice of `A` before truncation | `localSparsitySlackConstant`, `twiceTruncatedPlantEdgesAt`, and the canonical appendix laws make this dependence explicit. | **Resolved** |
| Fixed parameters and filters | Asymptotic declarations use `atTop`, `Vanishes`, `TendsToOne`, `Omega`, and `TendstoInProbability` with paper parameters fixed outside the limit. | **Resolved** |
| Uniformity in Lemma 3.1 | `UniformlyTendsToOneOn` and the occurring-shape adapter state one uniform eventual bound over the changing support family. | **Resolved** |
| Finite support of graph sums | `AmbientSupportClass`, concrete-copy fibers, and explicit `Finset` regrouping make every paper sum finite. | **Resolved** |
| Redundant premise in Lemma 4.4 | `clusterExpansion_bound` preserves the printed premise; `clusterExpansion_bound_core` is the premise-minimized helper. | **Resolved** |
| Exact TV, factorial, copy, and automorphism normalizations | `FiniteLaw.tv`, `fallingFactorial`, `nonInducedCopyCount`, and `FiniteGraphShape.Automorphism` are used by the proved identities. | **Resolved** |
| Small-`n` denominators | Occurrence and ambient-cardinality lemmas provide `v(F)≤n`; the leading-term proofs carry the required nonzero hypotheses explicitly. | **Resolved** |
| Theorem A.1 parameter dependence | `appendix_supercritical_gap_canonical` chooses `c₀` before quantifying `ε`; its witness is supplied by the ε-free theorem `appendix_lowDegreeIndistinguishability` and therefore depends only on `(λ,r,γ)`. | **Resolved** |

## Suggested update policy

When a declaration is added, update only its **Proof status** (`Planned` → `Statement formalized` → `Proved`), and link the declaration if useful. Change **Statement fidelity** only after comparing the Lean type directly with the source snapshot above. Any intentional strengthening or normalization lemma should be recorded as an auxiliary result, not substituted silently for the paper-facing wrapper.
