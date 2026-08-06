import LowDegree.Combinatorics.GraphShapeClasses
import LowDegree.SupercriticalStatistical

/-!
# Support restrictions for the twice-truncated appendix plant

This module records the pointwise facts behind Appendix equations (A.6)--
(A.8): twice truncation only removes original Erdős--Rényi edges, a nonempty
surviving support certifies the local-sparsity event, and no explicitly
embedded cycle up to the pruning cutoff can survive.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Short-cycle pruning only removes present edges. -/
theorem shortCyclePrunedEdges_subset_present (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) :
    shortCyclePrunedEdges m g x ⊆ presentAmbientEdges x := by
  intro e he
  exact (Finset.mem_sdiff.mp he).1

/-- The twice-truncated plant is a subgraph of the short-cycle-pruned plant. -/
theorem twiceTruncatedPlantEdgesAt_subset_shortCyclePruned
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) :
    twiceTruncatedPlantEdgesAt lam r gamma m g n x ⊆
      shortCyclePrunedEdges (m n) (g n) x := by
  unfold twiceTruncatedPlantEdgesAt
  split
  · exact Finset.Subset.rfl
  · exact Finset.empty_subset _

/-- Both appendix modifications only delete edges of the original random
graph. -/
theorem twiceTruncatedPlantEdgesAt_subset_present
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) :
    twiceTruncatedPlantEdgesAt lam r gamma m g n x ⊆
      presentAmbientEdges x :=
  (twiceTruncatedPlantEdgesAt_subset_shortCyclePruned
    lam r gamma m g n x).trans
      (shortCyclePrunedEdges_subset_present (m n) (g n) x)

/-- A nonempty support surviving the twice truncation forces the original
sample to lie in the local-sparsity event. -/
theorem mem_localSparsityEvent_of_nonempty_subset_twiceTruncated
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n)))
    (S : Finset (AmbientEdge (m n))) (hS : S.Nonempty)
    (hsub : S ⊆ twiceTruncatedPlantEdgesAt lam r gamma m g n x) :
    x ∈ localSparsityEvent n (m n)
      (localSparsityPowerCutoff (m n) gamma)
      (localSparsitySlackConstant lam r gamma) := by
  by_contra hbad
  have hempty :
      twiceTruncatedPlantEdgesAt lam r gamma m g n x = ∅ := by
    simp [twiceTruncatedPlantEdgesAt, hbad]
  obtain ⟨e, he⟩ := hS
  have := hsub he
  simpa [hempty] using this

/-- Every embedded cycle in the pruning range loses at least one edge. -/
theorem cycleEmbeddingEdges_not_subset_shortCyclePruned
    {m g k : ℕ} (x : BooleanConfiguration (AmbientEdge m))
    (f : CycleEmbedding m k) (hk3 : 3 ≤ k) (hkg : k ≤ g) :
    ¬cycleEmbeddingEdges f ⊆ shortCyclePrunedEdges m g x := by
  intro hsub
  have hpresent :
      x ∈ allPresentEvent (cycleEmbeddingEdges f) := by
    rw [mem_allPresentEvent]
    intro e he
    exact mem_presentAmbientEdges x e |>.mp
      (shortCyclePrunedEdges_subset_present m g x (hsub he))
  have hcard : (cycleEmbeddingEdges f).card = k :=
    card_cycleEmbeddingEdges hk3 f
  have hnonempty : (cycleEmbeddingEdges f).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  obtain ⟨e, he⟩ := hnonempty
  have hremoved : e ∈ shortCycleRemovedEdges m g x := by
    unfold shortCycleRemovedEdges
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk3, hkg⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨f, Finset.mem_univ f, ?_⟩
    simp [presentCycleEdges, hpresent, he]
  exact (Finset.mem_sdiff.mp (hsub he)).2 hremoved

/-- Consequently, no embedded cycle of length in `[3,gₙ]` is contained in a
twice-truncated appendix plant sample. -/
theorem cycleEmbeddingEdges_not_subset_twiceTruncated
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n k : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n)))
    (f : CycleEmbedding (m n) k) (hk3 : 3 ≤ k) (hkg : k ≤ g n) :
    ¬cycleEmbeddingEdges f ⊆
      twiceTruncatedPlantEdgesAt lam r gamma m g n x := by
  intro hsub
  exact cycleEmbeddingEdges_not_subset_shortCyclePruned x f hk3 hkg
    (hsub.trans
      (twiceTruncatedPlantEdgesAt_subset_shortCyclePruned
        lam r gamma m g n x))

/-! ## Canonical vertex set of a concrete support -/

namespace FiniteGraphShape

/-- Ambient vertices occupied by a concrete graph copy. -/
noncomputable def concreteCopyVertexFinset {n : ℕ}
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) : Finset (Fin n) :=
  copy.1.verts.toFinset

/-- A concrete copy occupies exactly the abstract shape's number of
vertices. -/
@[simp]
theorem card_concreteCopyVertexFinset {n : ℕ}
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (F.concreteCopyVertexFinset copy).card = F.vertexCount := by
  calc
    (F.concreteCopyVertexFinset copy).card = copy.1.verts.ncard := by
      exact (Set.ncard_eq_toFinset_card' copy.1.verts).symm
    _ = Fintype.card copy.1.verts := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    _ = F.vertexCount := by
      unfold vertexCount
      exact (Fintype.card_congr (F.chosenIso copy).toEquiv).symm

/-- Every edge of a concrete copy has both endpoints in its occupied vertex
set. -/
theorem concreteCopyEdges_subset_ambientEdgesOn_vertexFinset {n : ℕ}
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    F.concreteCopyEdges copy ⊆
      ambientEdgesOn (F.concreteCopyVertexFinset copy) := by
  intro e he
  have hedge : (e : Sym2 (Fin n)) ∈ copy.1.edgeSet :=
    (F.mem_concreteCopyEdges copy e).mp he
  let U := F.concreteCopyVertexFinset copy
  let hverts : ∀ v ∈ e.1, v ∈ U := fun v hv ↦ by
    change v ∈ copy.1.verts.toFinset
    rw [Set.mem_toFinset]
    exact copy.1.mem_verts_of_mem_edge hedge hv
  rw [ambientEdgesOn, Finset.mem_map]
  let a' : (⊤ : SimpleGraph U).edgeSet :=
    ⟨e.1.attachWith hverts, by
      simpa only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
        ← Sym2.isDiag_map Subtype.val_injective,
        Sym2.attachWith_map_subtypeVal] using e.property⟩
  refine ⟨a', Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact Sym2.attachWith_map_subtypeVal _

end FiniteGraphShape

/-- Every nonempty ambient support has a canonical vertex set of size equal
to its support-shape vertex count and containing all support edges. -/
theorem exists_vertexFinset_card_eq_supportShape_vertexCount
    {n : ℕ} (S : Finset (AmbientEdge n)) :
    ∃ U : Finset (Fin n),
      U.card = (FiniteGraphShape.supportShape
        (ambientSupportGraph S)).vertexCount ∧
      S ⊆ ambientEdgesOn U := by
  let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
  let copy := supportConcreteCopy S
  refine ⟨F.concreteCopyVertexFinset copy, ?_, ?_⟩
  · exact F.card_concreteCopyVertexFinset copy
  · rw [← concreteCopyEdges_supportConcreteCopy S]
    exact F.concreteCopyEdges_subset_ambientEdgesOn_vertexFinset copy

/-- A support contained in the present edges on `U` contributes at most the
local edge count on `U`. -/
theorem card_le_localEdgeCount_of_subset
    {m : ℕ} (x : BooleanConfiguration (AmbientEdge m))
    (S : Finset (AmbientEdge m)) (U : Finset (Fin m))
    (hpresent : S ⊆ presentAmbientEdges x)
    (hvertices : S ⊆ ambientEdgesOn U) :
    S.card ≤ localEdgeCount x U := by
  unfold localEdgeCount
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter]
  exact ⟨hvertices he, (mem_presentAmbientEdges x e).mp (hpresent he)⟩

namespace FiniteLaw

/-- Mapping the left coordinate before forming a product is the same as
mapping the product pair. -/
theorem map_product_left
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (q : FiniteLaw C) (f : A → B) :
    (p.map f).product q =
      (p.product q).map (fun z ↦ (f z.1, z.2)) := by
  apply FiniteLaw.ext_mass
  funext z
  simp only [product_mass, map_mass]
  rw [Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hf : f a = z.1 <;> simp [hf, Prod.ext_iff]

/-- Functoriality of finite-law pushforwards. -/
theorem map_map
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (f : A → B) (g : B → C) :
    (p.map f).map g = p.map (g ∘ f) := by
  apply FiniteLaw.ext_mass
  funext z
  simp only [map_mass]
  calc
    (∑ b : B, if g b = z then
        ∑ a : A, if f a = b then p.mass a else 0 else 0) =
        ∑ b : B, ∑ a : A,
          if g b = z then
            (if f a = b then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hgb : g b = z <;> simp [hgb]
    _ = ∑ a : A, ∑ b : B,
          if g b = z then
            (if f a = b then p.mass a else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a : A, if (g ∘ f) a = z then p.mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      have hsingle :
          (∑ b : B, if g b = z then
              (if f a = b then p.mass a else 0) else 0) =
            (if g (f a) = z then p.mass a else 0) := by
        rw [Finset.sum_eq_single (f a)]
        · simp
        · intro b _hb hba
          simp [Ne.symm hba]
        · simp
      simpa only [Function.comp_apply] using hsingle

end FiniteLaw

/-- A generic pointwise deletion map can only decrease every random-plant
containment probability. -/
theorem randomPlantContainmentProbability_map_le_of_subset
    {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω]
    (p : FiniteLaw Ω) (original truncated : Ω → Finset E)
    (hsubset : ∀ x, truncated x ⊆ original x) (S : Finset E) :
    randomPlantContainmentProbability (p.map truncated) S ≤
      randomPlantContainmentProbability (p.map original) S := by
  unfold randomPlantContainmentProbability
  rw [FiniteLaw.prob_map, FiniteLaw.prob_map]
  apply FiniteLaw.prob_mono
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.trans (hsubset x)

/-- Equation (A.6), before the explicit Erdős--Rényi/injection evaluation:
twice truncation is dominated by the original plant's containment
probability for every fixed support. -/
theorem twiceTruncatedPlantLawAt_containment_le_original
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (S : Finset (AmbientEdge (m n))) :
    randomPlantContainmentProbability
        (twiceTruncatedPlantLawAt lam r gamma m g n) S ≤
      randomPlantContainmentProbability
        ((erdosRenyiLaw (n := m n)
          (sparseBernoulliParameter lam (m n))).map presentAmbientEdges) S := by
  unfold twiceTruncatedPlantLawAt
  exact randomPlantContainmentProbability_map_le_of_subset
    (erdosRenyiLaw (n := m n)
      (sparseBernoulliParameter lam (m n)))
    presentAmbientEdges
    (twiceTruncatedPlantEdgesAt lam r gamma m g n)
    (twiceTruncatedPlantEdgesAt_subset_present lam r gamma m g n) S

end

end LowDegree
