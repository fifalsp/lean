import LowDegree.SupercriticalSupportRestrictions
import LowDegree.SupercriticalCanonicalScales
import LowDegree.Combinatorics.AcyclicEdgeBound
import LowDegree.Asymptotics.PercolatedAcyclic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Finset.Preimage

/-!
# Shape restrictions for the injected twice-truncated appendix plant

This module pulls positive containment under the actual uniformly injected
twice-truncated law back to a concrete Erdős--Rényi sample and injection.
It then records the local-sparsity and short-cycle consequences used in
Appendix equations A.7--A.8.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Positive random-plant containment is witnessed by a positive-mass plant
sample which contains the prescribed support. -/
theorem exists_mass_pos_superset_of_containmentProbability_pos
    {E : Type*} [Fintype E] [DecidableEq E]
    (p : FiniteLaw (Finset E)) (S : Finset E)
    (hpos : 0 < randomPlantContainmentProbability p S) :
    ∃ A : Finset E, 0 < p.mass A ∧ S ⊆ A := by
  unfold randomPlantContainmentProbability FiniteLaw.prob at hpos
  rw [Finset.sum_pos_iff_of_nonneg] at hpos
  · rcases hpos with ⟨A, hAevent, hAmass⟩
    refine ⟨A, hAmass, ?_⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hAevent
  · exact fun A _hA ↦ p.mass_nonneg A

/-- A positive containment coefficient for the actual injected appendix law
comes from a concrete Erdős--Rényi sample and a concrete vertex injection.
The prescribed ambient support is contained in the injected twice-truncated
edge set of that sample. -/
theorem exists_appendix_source_witness_of_containmentProbability_pos
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (S : Finset (AmbientEdge n))
    (hpos : 0 < randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S) :
    ∃ (x : BooleanConfiguration
          (AmbientEdge (appendixPlantSize r n)))
        (perm : Equiv.Perm (Fin n)),
      0 < (erdosRenyiLaw
        (n := appendixPlantSize r n)
        (sparseBernoulliParameter lam (appendixPlantSize r n))).mass x ∧
      S ⊆ embedAmbientEdgeSet
        ((Fin.castLEEmb
          (appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)).trans
            perm.toEmbedding)
        (twiceTruncatedPlantEdgesAt lam r gamma
          (appendixPlantSize r) appendixCycleCutoff n x) := by
  let hfit : appendixPlantSize r n ≤ n :=
    appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n
  let sourceLaw : FiniteLaw
      (Finset (AmbientEdge (appendixPlantSize r n))) :=
    twiceTruncatedPlantLawAt lam r gamma
      (appendixPlantSize r) appendixCycleCutoff n
  obtain ⟨B, hBmass, hSB⟩ :=
    exists_mass_pos_superset_of_containmentProbability_pos
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S hpos
  have hBmass' : 0 < (uniformlyInjectedPlantLaw hfit sourceLaw).mass B := by
    simpa only [appendixInjectedTruncatedPlantLaw, hfit, sourceLaw] using hBmass
  unfold uniformlyInjectedPlantLaw at hBmass'
  obtain ⟨z, hzB, hzmass⟩ :=
    FiniteLaw.exists_preimage_of_map_mass_pos _ _ hBmass'
  have hsourceMass : 0 < sourceLaw.mass z.1 := by
    rw [FiniteLaw.product_mass] at hzmass
    by_contra hnot
    have hzero : sourceLaw.mass z.1 = 0 :=
      le_antisymm (le_of_not_gt hnot) (sourceLaw.mass_nonneg z.1)
    rw [hzero, zero_mul] at hzmass
    exact lt_irrefl 0 hzmass
  unfold sourceLaw twiceTruncatedPlantLawAt at hsourceMass
  obtain ⟨x, hxedges, hxmass⟩ :=
    FiniteLaw.exists_preimage_of_map_mass_pos _ _ hsourceMass
  refine ⟨x, z.2, hxmass, ?_⟩
  have hSB' : S ⊆ embedAmbientEdgeSet
      ((Fin.castLEEmb hfit).trans z.2.toEmbedding) z.1 := by
    simpa only [hzB] using hSB
  simpa only [hfit, hxedges] using hSB'

/-! ## Pulling a concrete support back through an injection -/

/-- Membership in the complete graph on a vertex finset is equivalent to
both endpoints belonging to that finset. -/
theorem mem_ambientEdgesOn_iff {m : ℕ} (U : Finset (Fin m))
    (e : AmbientEdge m) :
    e ∈ ambientEdgesOn U ↔ ∀ v ∈ e.1, v ∈ U := by
  constructor
  · intro he v hv
    rw [ambientEdgesOn, Finset.mem_map] at he
    rcases he with ⟨a, _ha, hea⟩
    have hvmap : v ∈ Sym2.map Subtype.val a.1 := by
      have hea' := congrArg Subtype.val hea
      change Sym2.map Subtype.val a.1 = e.1 at hea'
      rw [hea']
      exact hv
    rw [Sym2.mem_map] at hvmap
    rcases hvmap with ⟨u, _hu, huv⟩
    rw [← huv]
    exact u.property
  · intro hvertices
    rw [ambientEdgesOn, Finset.mem_map]
    let a' : (⊤ : SimpleGraph U).edgeSet :=
      ⟨e.1.attachWith hvertices, by
        simpa only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
          ← Sym2.isDiag_map Subtype.val_injective,
          Sym2.attachWith_map_subtypeVal] using e.property⟩
    refine ⟨a', Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact Sym2.attachWith_map_subtypeVal _

/-- The incident vertices of an ambient edge support. -/
noncomputable def ambientSupportVertexFinset {m : ℕ}
    (S : Finset (AmbientEdge m)) : Finset (Fin m) :=
  (ambientSupportGraph S).support.toFinset

@[simp]
theorem card_ambientSupportVertexFinset {m : ℕ}
    (S : Finset (AmbientEdge m)) :
    (ambientSupportVertexFinset S).card =
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount := by
  calc
    (ambientSupportVertexFinset S).card =
        (ambientSupportGraph S).support.ncard := by
      exact (Set.ncard_eq_toFinset_card'
        (ambientSupportGraph S).support).symm
    _ = (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount :=
      (FiniteGraphShape.supportShape_vertexCount_eq_ncard _).symm

/-- Every support edge has both endpoints among its incident vertices. -/
theorem support_subset_ambientEdgesOn_supportVertexFinset {m : ℕ}
    (S : Finset (AmbientEdge m)) :
    S ⊆ ambientEdgesOn (ambientSupportVertexFinset S) := by
  intro e he
  rw [mem_ambientEdgesOn_iff]
  intro v hv
  unfold ambientSupportVertexFinset
  rw [Set.mem_toFinset, SimpleGraph.mem_support]
  rw [Sym2.mem_iff_exists] at hv
  rcases hv with ⟨w, hepair⟩
  have hvw : v ≠ w := by
    intro hvw
    subst w
    have htop : ¬e.1.IsDiag :=
      (⊤ : SimpleGraph (Fin m)).not_isDiag_of_mem_edgeSet e.property
    apply htop
    rw [hepair, Sym2.mk_isDiag_iff]
  let e' : AmbientEdge m := ⟨s(v, w), by simpa using hvw⟩
  have he'e : e' = e := by
    apply Subtype.ext
    exact hepair.symm
  refine ⟨w, ?_⟩
  rw [← SimpleGraph.mem_edgeSet]
  change (e' : Sym2 (Fin m)) ∈ (ambientSupportGraph S).edgeSet
  rw [mem_ambientSupportGraph_edgeSet_iff]
  simpa only [he'e] using he

/-- If a support is contained in an injected edge set, each of its incident
vertices lies in the image of the vertex injection. -/
theorem supportVertexFinset_subset_range_of_subset_embed
    {m n : ℕ} (φ : Fin m ↪ Fin n)
    (A : Finset (AmbientEdge m)) (S : Finset (AmbientEdge n))
    (hS : S ⊆ embedAmbientEdgeSet φ A) :
    ∀ v ∈ ambientSupportVertexFinset S, v ∈ Set.range φ := by
  intro v hv
  unfold ambientSupportVertexFinset at hv
  rw [Set.mem_toFinset, SimpleGraph.mem_support] at hv
  rcases hv with ⟨w, hvw⟩
  let e : AmbientEdge n := ⟨s(v, w), hvw.ne⟩
  have heS : e ∈ S := by
    rw [← mem_ambientSupportGraph_edgeSet_iff]
    exact hvw
  have hemap := hS heS
  rw [embedAmbientEdgeSet, Finset.mem_map] at hemap
  rcases hemap with ⟨a, _ha, hea⟩
  have hvmap : v ∈ Sym2.map φ a.1 := by
    have hea' := congrArg Subtype.val hea
    change Sym2.map φ a.1 = e.1 at hea'
    rw [hea']
    simp [e]
  rw [Sym2.mem_map] at hvmap
  rcases hvmap with ⟨u, _hu, huv⟩
  exact ⟨u, huv⟩

/-- Edge support pulled back through an injective vertex map. -/
noncomputable def pullbackAmbientEdgeSet {m n : ℕ} (φ : Fin m ↪ Fin n)
    (S : Finset (AmbientEdge n)) : Finset (AmbientEdge m) :=
  S.preimage (ambientEdgeEmbeddingOfVertexEmbedding φ)
    (ambientEdgeEmbeddingOfVertexEmbedding φ).injective.injOn

@[simp]
theorem mem_pullbackAmbientEdgeSet {m n : ℕ} (φ : Fin m ↪ Fin n)
    (S : Finset (AmbientEdge n)) (e : AmbientEdge m) :
    e ∈ pullbackAmbientEdgeSet φ S ↔
      ambientEdgeEmbeddingOfVertexEmbedding φ e ∈ S := by
  simp [pullbackAmbientEdgeSet]

/-- Pullback is contained in any source edge set whose image contains the
ambient support. -/
theorem pullbackAmbientEdgeSet_subset {m n : ℕ} (φ : Fin m ↪ Fin n)
    {A : Finset (AmbientEdge m)} {S : Finset (AmbientEdge n)}
    (hS : S ⊆ embedAmbientEdgeSet φ A) :
    pullbackAmbientEdgeSet φ S ⊆ A := by
  exact Finset.preimage_subset hS

/-- Mapping the pullback recovers a support known to lie in the image. -/
theorem embed_pullbackAmbientEdgeSet_eq {m n : ℕ} (φ : Fin m ↪ Fin n)
    {A : Finset (AmbientEdge m)} {S : Finset (AmbientEdge n)}
    (hS : S ⊆ embedAmbientEdgeSet φ A) :
    embedAmbientEdgeSet φ (pullbackAmbientEdgeSet φ S) = S := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [embedAmbientEdgeSet, Finset.mem_map] at he
    rcases he with ⟨a, ha, rfl⟩
    exact (mem_pullbackAmbientEdgeSet φ S a).mp ha
  · intro e he
    have hem := hS he
    rw [embedAmbientEdgeSet, Finset.mem_map] at hem ⊢
    rcases hem with ⟨a, ha, hea⟩
    exact ⟨a, (mem_pullbackAmbientEdgeSet φ S a).mpr (hea ▸ he), hea⟩

theorem card_pullbackAmbientEdgeSet {m n : ℕ} (φ : Fin m ↪ Fin n)
    {A : Finset (AmbientEdge m)} {S : Finset (AmbientEdge n)}
    (hS : S ⊆ embedAmbientEdgeSet φ A) :
    (pullbackAmbientEdgeSet φ S).card = S.card := by
  calc
    (pullbackAmbientEdgeSet φ S).card =
        (embedAmbientEdgeSet φ (pullbackAmbientEdgeSet φ S)).card := by
      rw [card_embedAmbientEdgeSet]
    _ = S.card := by rw [embed_pullbackAmbientEdgeSet_eq φ hS]

/-- A concrete nonempty support uses at most twice as many incident vertices
as edges. -/
theorem supportShape_vertexCount_le_twice_card {m : ℕ}
    (S : Finset (AmbientEdge m)) :
    (FiniteGraphShape.supportShape
      (ambientSupportGraph S)).vertexCount ≤ 2 * S.card := by
  let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
  have hdegree : ∀ v : F.Vertex, 1 ≤ F.graph.degree v := by
    intro v
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hnmem : v ∉ F.graph.support :=
      (F.graph.degree_eq_zero_iff_notMem_support v).mp hzero
    apply hnmem
    rw [F.support_eq_univ]
    exact Set.mem_univ v
  have hsum : (∑ _v : F.Vertex, 1) ≤
      ∑ v : F.Vertex, F.graph.degree v :=
    Finset.sum_le_sum fun v _hv ↦ hdegree v
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  have hedgeCount : F.graph.edgeFinset.card = S.card := by
    calc
      F.graph.edgeFinset.card = F.edgeCount := by
        rw [FiniteGraphShape.edgeCount_eq_ncard,
          ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
          ← SimpleGraph.edgeFinset_card]
      _ = (F.concreteCopyEdges (supportConcreteCopy S)).card :=
        (F.card_concreteCopyEdges (supportConcreteCopy S)).symm
      _ = S.card := by rw [concreteCopyEdges_supportConcreteCopy]
  change F.vertexCount ≤ 2 * S.card
  simpa [FiniteGraphShape.vertexCount, hedgeCount] using hsum

/-- Fixed-`n` A.7 estimate after exposing a concrete source sample and
injection. -/
theorem supportShape_localSparsity_bound_of_appendix_source
    (lam r gamma : ℝ) (n D : ℕ)
    (φ : Fin (appendixPlantSize r n) ↪ Fin n)
    (x : BooleanConfiguration
      (AmbientEdge (appendixPlantSize r n)))
    (S : Finset (AmbientEdge n)) (hSnonempty : S.Nonempty)
    (hS : S ⊆ embedAmbientEdgeSet φ
      (twiceTruncatedPlantEdgesAt lam r gamma
        (appendixPlantSize r) appendixCycleCutoff n x))
    (hD : S.card ≤ D)
    (hscale : (((2 * D : ℕ) : ℝ)) ≤
      (appendixPlantSize r n : ℝ) ^ gamma)
    (hlog : 0 < Real.log (n : ℝ))
    (hA : 0 ≤ localSparsitySlackConstant lam r gamma) :
    (S.card : ℝ) ≤
      (1 + localSparsitySlackConstant lam r gamma /
        Real.log (n : ℝ)) *
      ((FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount : ℝ) := by
  let sourceEdges := twiceTruncatedPlantEdgesAt lam r gamma
    (appendixPlantSize r) appendixCycleCutoff n x
  let T := pullbackAmbientEdgeSet φ S
  let U := ambientSupportVertexFinset S
  let V : Finset (Fin (appendixPlantSize r n)) :=
    U.preimage φ φ.injective.injOn
  have hTsub : T ⊆ sourceEdges :=
    pullbackAmbientEdgeSet_subset φ hS
  have hTcard : T.card = S.card :=
    card_pullbackAmbientEdgeSet φ hS
  have hTnonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hTempty
    have : T.card = 0 := by rw [hTempty, Finset.card_empty]
    rw [hTcard] at this
    exact hSnonempty.card_pos.ne' this
  have hUrange : ∀ u ∈ U, u ∈ Set.range φ :=
    supportVertexFinset_subset_range_of_subset_embed φ sourceEdges S hS
  have hmapV : V.map φ = U := by
    apply Finset.Subset.antisymm
    · intro u hu
      rw [Finset.mem_map] at hu
      rcases hu with ⟨v, hv, rfl⟩
      exact (Finset.mem_preimage.mp hv)
    · intro u hu
      rcases hUrange u hu with ⟨v, rfl⟩
      rw [Finset.mem_map]
      exact ⟨v, Finset.mem_preimage.mpr hu, rfl⟩
  have hVcard : V.card =
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount := by
    calc
      V.card = (V.map φ).card := by rw [Finset.card_map]
      _ = U.card := by rw [hmapV]
      _ = _ := card_ambientSupportVertexFinset S
  have hTonV : T ⊆ ambientEdgesOn V := by
    intro e he
    rw [mem_ambientEdgesOn_iff]
    intro v hv
    rw [Finset.mem_preimage]
    have heS : ambientEdgeEmbeddingOfVertexEmbedding φ e ∈ S :=
      (mem_pullbackAmbientEdgeSet φ S e).mp he
    have heU := support_subset_ambientEdgesOn_supportVertexFinset S heS
    exact (mem_ambientEdgesOn_iff U _).mp heU (φ v)
      ((Sym2.mem_map).mpr ⟨v, hv, rfl⟩)
  have hV2 : 2 ≤ V.card := by
    by_contra hnot
    have hVlt : V.card < 2 := Nat.lt_of_not_ge hnot
    have hambientCard : (ambientEdgesOn V).card = 0 := by
      rw [card_ambientEdgesOn, Nat.choose_eq_zero_of_lt hVlt]
    have hcardle := Finset.card_le_card hTonV
    rw [hambientCard] at hcardle
    exact hTnonempty.card_pos.not_ge hcardle
  have hVcutoff : V.card ≤ localSparsityPowerCutoff
      (appendixPlantSize r n) gamma := by
    apply Nat.le_floor
    calc
      (V.card : ℝ) =
          ((FiniteGraphShape.supportShape
            (ambientSupportGraph S)).vertexCount : ℝ) := by
        exact_mod_cast hVcard
      _ ≤ ((2 * S.card : ℕ) : ℝ) := by
        exact_mod_cast supportShape_vertexCount_le_twice_card S
      _ ≤ ((2 * D : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hD
      _ ≤ (appendixPlantSize r n : ℝ) ^ gamma := hscale
  have hlocal : x ∈ localSparsityEvent n (appendixPlantSize r n)
      (localSparsityPowerCutoff (appendixPlantSize r n) gamma)
      (localSparsitySlackConstant lam r gamma) := by
    exact mem_localSparsityEvent_of_nonempty_subset_twiceTruncated
      lam r gamma (appendixPlantSize r) appendixCycleCutoff n x
      T hTnonempty hTsub
  have hslack : 0 ≤ localSparsitySlackConstant lam r gamma /
      Real.log (n : ℝ) := div_nonneg hA hlog.le
  have hlocalV := (mem_localSparsityEvent_iff_real hslack x).mp
    hlocal V hV2 hVcutoff
  have hpresent : T ⊆ presentAmbientEdges x :=
    hTsub.trans (twiceTruncatedPlantEdgesAt_subset_present
      lam r gamma (appendixPlantSize r) appendixCycleCutoff n x)
  have hcount : T.card ≤ localEdgeCount x V :=
    card_le_localEdgeCount_of_subset x T V hpresent hTonV
  calc
    (S.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hTcard.symm
    _ ≤ (localEdgeCount x V : ℝ) := by exact_mod_cast hcount
    _ ≤ (1 + localSparsitySlackConstant lam r gamma /
          Real.log (n : ℝ)) * (V.card : ℝ) := hlocalV
    _ = (1 + localSparsitySlackConstant lam r gamma /
          Real.log (n : ℝ)) *
        ((FiniteGraphShape.supportShape
          (ambientSupportGraph S)).vertexCount : ℝ) := by rw [hVcard]

/-- **Appendix A.7 at the actual injected twice-truncated law.**

Eventually, every nonempty support of degree at most the canonical cutoff
whose containment coefficient is positive satisfies the manuscript's
local-sparsity edge/vertex inequality. -/
theorem eventually_positive_appendixContainment_localSparsity
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset (AmbientEdge n),
      S.Nonempty → S.card ≤ appendixDegreeCutoff n →
      0 < randomPlantContainmentProbability
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S →
      (S.card : ℝ) ≤
        (1 + localSparsitySlackConstant lam r gamma /
          Real.log (n : ℝ)) *
        ((FiniteGraphShape.supportShape
          (ambientSupportGraph S)).vertexCount : ℝ) := by
  have hA : 0 ≤ localSparsitySlackConstant lam r gamma :=
    (localSparsitySlackConstant_pos lam hr.1 hgamma.2).le
  filter_upwards
      [eventually_two_appendixDegreeCutoff_le_appendixPlantSize_rpow
        hr.1 hgamma.1,
       Filter.eventually_gt_atTop (1 : ℕ)] with n hscale hn
  intro S hSnonempty hD hpos
  obtain ⟨x, perm, _hxmass, hS⟩ :=
    exists_appendix_source_witness_of_containmentProbability_pos
      lam r gamma hr n S hpos
  let hfit : appendixPlantSize r n ≤ n :=
    appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n
  let φ : Fin (appendixPlantSize r n) ↪ Fin n :=
    (Fin.castLEEmb hfit).trans perm.toEmbedding
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hn
  exact supportShape_localSparsity_bound_of_appendix_source
    lam r gamma n (appendixDegreeCutoff n) φ x S hSnonempty
    (by simpa only [φ, hfit] using hS) hD hscale hlog hA

/-! ## Cyclic shapes and short-cycle pruning -/

/-- A nonempty support shape with at least as many edges as vertices
contains an explicitly embedded cycle whose length is at most its vertex
count. -/
theorem exists_cycleEmbedding_of_supportShape_vertexCount_le_edgeCount
    {n : ℕ} (S : Finset (AmbientEdge n)) (hS : S.Nonempty)
    (hcyclic :
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount ≤
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).edgeCount) :
    ∃ (k : ℕ) (f : CycleEmbedding n k),
      3 ≤ k ∧
      k ≤ (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount ∧
      cycleEmbeddingEdges f ⊆ S := by
  let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
  let copy := supportConcreteCopy S
  have hedgeCount : F.edgeCount = S.card := by
    calc
      F.edgeCount = (F.concreteCopyEdges copy).card :=
        (F.card_concreteCopyEdges copy).symm
      _ = S.card := by
        dsimp [copy]
        rw [concreteCopyEdges_supportConcreteCopy]
  have hedge : 0 < F.edgeCount := by
    rw [hedgeCount]
    exact hS.card_pos
  have hnotAcyclic : ¬F.graph.IsAcyclic :=
    F.not_isAcyclic_of_vertexCount_le_edgeCount hedge hcyclic
  obtain ⟨v, cycle, hcycle, _hgirth⟩ :=
    SimpleGraph.exists_girth_eq_length.mpr hnotAcyclic
  let k := cycle.length
  have hk3 : 3 ≤ k := hcycle.three_le_length
  have htailLength : cycle.support.tail.length = k := by
    dsimp [k]
    rw [List.length_tail, cycle.length_support]
    omega
  have hkVertex : k ≤ F.vertexCount := by
    rw [← htailLength]
    change cycle.support.tail.length ≤ Fintype.card F.Vertex
    exact hcycle.2.length_le_card
  let cycleCopy : SimpleGraph.Copy
      (SimpleGraph.cycleGraph k) F.graph := by
    dsimp [k]
    exact PercolatedAcyclic.cycleCopyOfIsCycle hcycle
  let shapeIso : F.graph ≃g copy.1.coe := Classical.choice copy.2
  let f : CycleEmbedding n k :=
    (cycleCopy.toEmbedding.trans shapeIso.toEquiv.toEmbedding).trans
      copy.1.coeCopy.toEmbedding
  refine ⟨k, f, hk3, hkVertex, ?_⟩
  intro e he
  rw [cycleEmbeddingEdges, Finset.mem_map] at he
  rcases he with ⟨a, ha, hea⟩
  rw [← concreteCopyEdges_supportConcreteCopy S,
    F.mem_concreteCopyEdges]
  have haAdj : (SimpleGraph.cycleGraph k).Adj a.1.out.1 a.1.out.2 := by
    have haedge : a.1 ∈ (SimpleGraph.cycleGraph k).edgeSet := a.2
    rw [← SimpleGraph.mem_edgeSet]
    simpa only [a.1.out_eq] using haedge
  have hFAdj : F.graph.Adj
      (cycleCopy a.1.out.1) (cycleCopy a.1.out.2) :=
    cycleCopy.toHom.map_rel' haAdj
  have hcopyAdj : copy.1.coe.Adj
      (shapeIso (cycleCopy a.1.out.1))
      (shapeIso (cycleCopy a.1.out.2)) :=
    shapeIso.map_rel_iff.mpr hFAdj
  have hambientAdj : copy.1.Adj
      (shapeIso (cycleCopy a.1.out.1)).1
      (shapeIso (cycleCopy a.1.out.2)).1 := hcopyAdj
  have heval := congrArg Subtype.val hea
  change Sym2.map f a.1 = e.1 at heval
  rw [← heval]
  change Sym2.map f a.1 ∈ copy.1.edgeSet
  rw [← a.1.out_eq, Sym2.map_mk]
  exact hambientAdj

/-- Short-cycle pruning remains valid after an injective relabelling of the
twice-truncated source plant. -/
theorem cycleEmbeddingEdges_not_subset_embeddedTwiceTruncated
    (lam r gamma : ℝ) (n : ℕ)
    (x : BooleanConfiguration
      (AmbientEdge (appendixPlantSize r n)))
    (φ : Fin (appendixPlantSize r n) ↪ Fin n)
    {k : ℕ} (f : CycleEmbedding n k)
    (hk3 : 3 ≤ k) (hkg : k ≤ appendixCycleCutoff n) :
    ¬cycleEmbeddingEdges f ⊆ embedAmbientEdgeSet φ
      (twiceTruncatedPlantEdgesAt lam r gamma
        (appendixPlantSize r) appendixCycleCutoff n x) := by
  intro hcycleSub
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk3
  have hj' : k = j + 3 := by omega
  clear hj
  subst k
  let sourceEdges := twiceTruncatedPlantEdgesAt lam r gamma
    (appendixPlantSize r) appendixCycleCutoff n x
  have hrange : ∀ i : Fin (j + 3), ∃ u, φ u = f i := by
    intro i
    have hiSupport : i ∈ (SimpleGraph.cycleGraph (j + 3)).support := by
      rw [← SimpleGraph.degree_pos_iff_mem_support]
      have hdegree : (SimpleGraph.cycleGraph (j + 3)).degree i = 2 :=
        SimpleGraph.cycleGraph_degree_three_le
      rw [hdegree]
      norm_num
    rw [SimpleGraph.mem_support] at hiSupport
    rcases hiSupport with ⟨w, hiw⟩
    let a : (SimpleGraph.cycleGraph (j + 3)).edgeSet :=
      ⟨s(i, w), hiw⟩
    let e : AmbientEdge n := (cycleEmbeddingCopy f).mapEdgeSet a
    have heCycle : e ∈ cycleEmbeddingEdges f := by
      rw [cycleEmbeddingEdges, Finset.mem_map]
      exact ⟨a, Finset.mem_univ _, rfl⟩
    have heImage := hcycleSub heCycle
    rw [embedAmbientEdgeSet, Finset.mem_map] at heImage
    rcases heImage with ⟨b, _hb, hbe⟩
    have hfi : f i ∈ e.1 := by
      change f i ∈ Sym2.map f s(i, w)
      exact (Sym2.mem_map).mpr ⟨i, by simp, rfl⟩
    have hfiMap : f i ∈ Sym2.map φ b.1 := by
      have hbe' := congrArg Subtype.val hbe
      change Sym2.map φ b.1 = e.1 at hbe'
      rwa [hbe']
    rw [Sym2.mem_map] at hfiMap
    rcases hfiMap with ⟨u, _hu, huf⟩
    exact ⟨u, huf⟩
  let liftVertex : Fin (j + 3) → Fin (appendixPlantSize r n) :=
    fun i ↦ Classical.choose (hrange i)
  have hlift (i : Fin (j + 3)) : φ (liftVertex i) = f i :=
    Classical.choose_spec (hrange i)
  let sourceCycle : CycleEmbedding (appendixPlantSize r n) (j + 3) :=
    { toFun := liftVertex
      inj' := by
        intro i i' hii'
        apply f.injective
        rw [← hlift i, ← hlift i', hii'] }
  have hsourceSub : cycleEmbeddingEdges sourceCycle ⊆ sourceEdges := by
    intro e he
    rw [cycleEmbeddingEdges, Finset.mem_map] at he
    rcases he with ⟨a, _ha, hea⟩
    let ambientE : AmbientEdge n :=
      ambientEdgeEmbeddingOfVertexEmbedding φ e
    have hambientCycle : ambientE ∈ cycleEmbeddingEdges f := by
      rw [cycleEmbeddingEdges, Finset.mem_map]
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      have hea' := congrArg Subtype.val hea
      change Sym2.map sourceCycle a.1 = e.1 at hea'
      change Sym2.map f a.1 = Sym2.map φ e.1
      rw [← hea']
      induction a.1 using Sym2.inductionOn with
      | _ u v =>
          simp only [Sym2.map_pair_eq]
          change s(f u, f v) =
            s(φ (liftVertex u), φ (liftVertex v))
          rw [hlift u, hlift v]
    have hambientSource := hcycleSub hambientCycle
    rw [embedAmbientEdgeSet, Finset.mem_map] at hambientSource
    rcases hambientSource with ⟨b, hb, hbe⟩
    have : b = e := by
      apply (ambientEdgeEmbeddingOfVertexEmbedding φ).injective
      exact hbe
    simpa only [this] using hb
  exact cycleEmbeddingEdges_not_subset_twiceTruncated
    lam r gamma (appendixPlantSize r) appendixCycleCutoff n (j + 3)
    x sourceCycle (by omega) hkg hsourceSub

/-- **Appendix A.8 at the actual injected twice-truncated law.**

If a nonempty support with positive containment has at least as many edges
as incident vertices, then its vertex count is strictly larger than the
short-cycle pruning cutoff. -/
theorem appendixCycleCutoff_lt_supportShape_vertexCount_of_positive_containment
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (S : Finset (AmbientEdge n)) (hSnonempty : S.Nonempty)
    (hpos : 0 < randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S)
    (hcyclic :
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount ≤
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).edgeCount) :
    appendixCycleCutoff n <
      (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount := by
  obtain ⟨k, f, hk3, hkVertex, hcycleS⟩ :=
    exists_cycleEmbedding_of_supportShape_vertexCount_le_edgeCount
      S hSnonempty hcyclic
  by_contra hnot
  have hkg : k ≤ appendixCycleCutoff n :=
    hkVertex.trans (Nat.le_of_not_gt hnot)
  obtain ⟨x, perm, _hxmass, hSsource⟩ :=
    exists_appendix_source_witness_of_containmentProbability_pos
      lam r gamma hr n S hpos
  let hfit : appendixPlantSize r n ≤ n :=
    appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n
  let φ : Fin (appendixPlantSize r n) ↪ Fin n :=
    (Fin.castLEEmb hfit).trans perm.toEmbedding
  apply cycleEmbeddingEdges_not_subset_embeddedTwiceTruncated
    lam r gamma n x φ f hk3 hkg
  exact hcycleS.trans (by simpa only [φ, hfit] using hSsource)

/-- Combined eventually quantified A.7--A.8 restriction for the supports
appearing in the canonical low-degree sum. -/
theorem eventually_positive_appendixContainment_shapeRestrictions
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset (AmbientEdge n),
      S.Nonempty → S.card ≤ appendixDegreeCutoff n →
      0 < randomPlantContainmentProbability
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S →
      ((S.card : ℝ) ≤
          (1 + localSparsitySlackConstant lam r gamma /
            Real.log (n : ℝ)) *
          ((FiniteGraphShape.supportShape
            (ambientSupportGraph S)).vertexCount : ℝ)) ∧
        ((FiniteGraphShape.supportShape
            (ambientSupportGraph S)).vertexCount ≤
          (FiniteGraphShape.supportShape
            (ambientSupportGraph S)).edgeCount →
          appendixCycleCutoff n <
            (FiniteGraphShape.supportShape
              (ambientSupportGraph S)).vertexCount) := by
  filter_upwards
      [eventually_positive_appendixContainment_localSparsity
        lam r gamma hr hgamma] with n hlocal
  intro S hSnonempty hD hpos
  refine ⟨hlocal S hSnonempty hD hpos, ?_⟩
  intro hcyclic
  exact appendixCycleCutoff_lt_supportShape_vertexCount_of_positive_containment
    lam r gamma hr n S hSnonempty hpos hcyclic

end

end LowDegree
