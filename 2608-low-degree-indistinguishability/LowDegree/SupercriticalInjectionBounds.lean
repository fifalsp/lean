import LowDegree.SupercriticalSupportRestrictions

/-!
# Uniform-injection containment bounds for Appendix A

This module isolates the injection step in Appendix equation (A.6).  The
first theorem says that applying a pointwise edge-deletion map before a
uniform vertex injection can only decrease every ambient containment
probability.  The subsequent specializations apply it to the original sparse
Erdős--Rényi plant and to the twice-truncated appendix plant.
-/

namespace LowDegree

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Mapping a pointwise smaller source edge set through a fixed vertex
embedding again gives a smaller ambient edge set. -/
theorem embedAmbientEdgeSet_mono {m n : ℕ} (f : Fin m ↪ Fin n)
    {A B : Finset (AmbientEdge m)} (hAB : A ⊆ B) :
    embedAmbientEdgeSet f A ⊆ embedAmbientEdgeSet f B := by
  unfold embedAmbientEdgeSet
  exact Finset.map_subset_map.mpr hAB

/-- **Uniform-injection form of Appendix equation (A.6).**

If `truncated x ⊆ original x` for every source sample, then after applying
the same uniform injection into `Fin n`, every fixed ambient support is no
more likely to occur under the truncated plant. -/
theorem uniformlyInjectedPlantLaw_containment_mono_of_pointwise_subset
    {m n : ℕ} (hfit : m ≤ n) {Omega : Type*} [Fintype Omega]
    (p : FiniteLaw Omega)
    (original truncated : Omega → Finset (AmbientEdge m))
    (hsubset : ∀ x, truncated x ⊆ original x)
    (S : Finset (AmbientEdge n)) :
    randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit (p.map truncated)) S ≤
      randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit (p.map original)) S := by
  let q := uniformPermutationLaw n
  let originalInjected : Omega × Equiv.Perm (Fin n) →
      Finset (AmbientEdge n) := fun z ↦
    embedAmbientEdgeSet
      ((Fin.castLEEmb hfit).trans z.2.toEmbedding) (original z.1)
  let truncatedInjected : Omega × Equiv.Perm (Fin n) →
      Finset (AmbientEdge n) := fun z ↦
    embedAmbientEdgeSet
      ((Fin.castLEEmb hfit).trans z.2.toEmbedding) (truncated z.1)
  have htruncatedLaw :
      uniformlyInjectedPlantLaw hfit (p.map truncated) =
        (p.product q).map truncatedInjected := by
    unfold uniformlyInjectedPlantLaw truncatedInjected
    rw [FiniteLaw.map_product_left, FiniteLaw.map_map]
    rfl
  have horiginalLaw :
      uniformlyInjectedPlantLaw hfit (p.map original) =
        (p.product q).map originalInjected := by
    unfold uniformlyInjectedPlantLaw originalInjected
    rw [FiniteLaw.map_product_left, FiniteLaw.map_map]
    rfl
  rw [htruncatedLaw, horiginalLaw]
  exact randomPlantContainmentProbability_map_le_of_subset
    (p.product q) originalInjected truncatedInjected
    (fun z ↦ embedAmbientEdgeSet_mono _ (hsubset z.1)) S

/-- Sparse Erdős--Rényi specialization of the uniform-injection
monotonicity theorem. -/
theorem uniformlyInjected_sparseErdosRenyi_containment_mono
    {m n : ℕ} (hfit : m ≤ n) (lam : ℝ)
    (truncated : BooleanConfiguration (AmbientEdge m) →
      Finset (AmbientEdge m))
    (hsubset : ∀ x, truncated x ⊆ presentAmbientEdges x)
    (S : Finset (AmbientEdge n)) :
    randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit
          ((erdosRenyiLaw (n := m) (sparseBernoulliParameter lam m)).map
            truncated)) S ≤
      randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit
          ((erdosRenyiLaw (n := m) (sparseBernoulliParameter lam m)).map
            presentAmbientEdges)) S := by
  exact uniformlyInjectedPlantLaw_containment_mono_of_pointwise_subset
    hfit (erdosRenyiLaw (n := m) (sparseBernoulliParameter lam m))
      presentAmbientEdges truncated hsubset S

/-! ## Exact containment for the untruncated injected source -/

/-- Relabelling the complete graph on the canonical first `m` vertices has
exactly the same ambient edge set as composing the canonical inclusion with
that relabelling. -/
theorem permutedPlantEdges_mappedTop_castLE
    {m n : ℕ} (hfit : m ≤ n) (sigma : Equiv.Perm (Fin n)) :
    permutedPlantEdges
        ((⊤ : SimpleGraph (Fin m)).map (Fin.castLEEmb hfit)) sigma =
      embedAmbientEdgeSet
        ((Fin.castLEEmb hfit).trans sigma.toEmbedding) Finset.univ := by
  classical
  ext e
  rw [mem_permutedPlantEdges_iff]
  simp only [permutedPlant, SimpleGraph.map_map,
    SimpleGraph.edgeSet_map]
  constructor
  · rintro ⟨a, ha, hea⟩
    let a' : AmbientEdge m := ⟨a, ha⟩
    rw [embedAmbientEdgeSet, Finset.mem_map]
    refine ⟨a', Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact hea
  · intro he
    rw [embedAmbientEdgeSet, Finset.mem_map] at he
    rcases he with ⟨a, _ha, hae⟩
    refine ⟨a.1, a.2, ?_⟩
    exact congrArg Subtype.val hae

namespace FiniteGraphShape

/-- Every vertex of a support-stripped graph copy in an embedded complete
graph lies in the embedding's vertex range. -/
theorem mappedTopCopy_vertex_mem_range
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (copy : SimpleGraph.Copy F.graph
      ((⊤ : SimpleGraph (Fin m)).map f)) (v : F.Vertex) :
    copy v ∈ Set.range f := by
  have hvSupport : v ∈ F.graph.support := by
    rw [F.support_eq_univ]
    exact Set.mem_univ v
  rw [SimpleGraph.mem_support] at hvSupport
  rcases hvSupport with ⟨w, hvw⟩
  have hmap := copy.toHom.map_rel' hvw
  rw [SimpleGraph.map_adj] at hmap
  rcases hmap with ⟨u, _u', _huu', hu, _hu'⟩
  exact ⟨u, hu⟩

/-- The source vertex selected for a vertex of a copy in an embedded
complete graph. -/
noncomputable def mappedTopCopySourceVertex
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (copy : SimpleGraph.Copy F.graph
      ((⊤ : SimpleGraph (Fin m)).map f)) (v : F.Vertex) : Fin m :=
  Classical.choose (F.mappedTopCopy_vertex_mem_range f copy v)

@[simp]
theorem map_mappedTopCopySourceVertex
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (copy : SimpleGraph.Copy F.graph
      ((⊤ : SimpleGraph (Fin m)).map f)) (v : F.Vertex) :
    f (F.mappedTopCopySourceVertex f copy v) = copy v :=
  Classical.choose_spec (F.mappedTopCopy_vertex_mem_range f copy v)

/-- Label a concrete copy by an automorphism of the abstract shape. -/
noncomputable def mappedTopConcreteAutCopy
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (z : F.ConcreteCopy ((⊤ : SimpleGraph (Fin m)).map f) ×
      F.Automorphism) :
    SimpleGraph.Copy F.graph ((⊤ : SimpleGraph (Fin m)).map f) :=
  (concreteCopyToAmbientCopy z.1).comp z.2.toCopy

@[simp]
theorem mappedTopConcreteAutCopy_toSubgraph
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (z : F.ConcreteCopy ((⊤ : SimpleGraph (Fin m)).map f) ×
      F.Automorphism) :
    (F.mappedTopConcreteAutCopy f z).toSubgraph = z.1.1 := by
  rcases z with ⟨copy, a⟩
  let e : F.graph ≃g copy.1.coe := (chosenIso copy).comp a
  have heq :
      (concreteCopyToAmbientCopy copy).comp a.toCopy =
        copy.1.coeCopy.comp e.toCopy := by
    apply SimpleGraph.Copy.ext
    intro v
    rfl
  rw [mappedTopConcreteAutCopy, heq]
  exact isoToAmbientCopy_toSubgraph copy e

/-- Encode a concrete copy together with one abstract labelling by its
source-vertex map into `Fin m`. -/
noncomputable def mappedTopConcreteAutCode
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n) :
    (F.ConcreteCopy ((⊤ : SimpleGraph (Fin m)).map f) ×
      F.Automorphism) → (F.Vertex → Fin m) := fun z v ↦
  F.mappedTopCopySourceVertex f (F.mappedTopConcreteAutCopy f z) v

/-- Different concrete copies or different abstract labellings give
different source-vertex maps. -/
theorem mappedTopConcreteAutCode_injective
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n) :
    Function.Injective (F.mappedTopConcreteAutCode f) := by
  rintro ⟨source, a⟩ ⟨target, b⟩ hcode
  have hlabel : F.mappedTopConcreteAutCopy f (source, a) =
      F.mappedTopConcreteAutCopy f (target, b) := by
    apply SimpleGraph.Copy.ext
    intro v
    rw [← F.map_mappedTopCopySourceVertex f
        (F.mappedTopConcreteAutCopy f (source, a)) v,
      ← F.map_mappedTopCopySourceVertex f
        (F.mappedTopConcreteAutCopy f (target, b)) v]
    exact congrArg f (congrFun hcode v)
  have hsource : source = target := by
    apply Subtype.ext
    rw [← F.mappedTopConcreteAutCopy_toSubgraph f (source, a),
      ← F.mappedTopConcreteAutCopy_toSubgraph f (target, b)]
    exact congrArg SimpleGraph.Copy.toSubgraph hlabel
  subst target
  have hab : a = b := by
    apply RelIso.ext
    intro v
    apply (concreteCopyToAmbientCopy source).injective
    have hv := congrArg
      (fun copy : SimpleGraph.Copy F.graph
          ((⊤ : SimpleGraph (Fin m)).map f) ↦ copy v) hlabel
    simpa only [mappedTopConcreteAutCopy,
      SimpleGraph.Copy.comp_apply, SimpleGraph.Iso.toCopy,
      SimpleGraph.Copy.toHom_apply] using hv
  subst b
  rfl

/-- The orbit numerator for the canonical embedded complete graph is at
most the number `m^v` of arbitrary maps of the shape's vertices into the
source vertex set. -/
theorem nonInducedCopyCount_mappedTop_mul_aut_le_pow
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n) :
    F.nonInducedCopyCount ((⊤ : SimpleGraph (Fin m)).map f) *
        Fintype.card F.Automorphism ≤
      m ^ F.vertexCount := by
  calc
    F.nonInducedCopyCount ((⊤ : SimpleGraph (Fin m)).map f) *
        Fintype.card F.Automorphism =
        Nat.card (F.ConcreteCopy ((⊤ : SimpleGraph (Fin m)).map f) ×
          F.Automorphism) := by
      simp [FiniteGraphShape.nonInducedCopyCount,
        Nat.card_eq_fintype_card]
    _ ≤ Nat.card (F.Vertex → Fin m) :=
      Nat.card_le_card_of_injective _
        (F.mappedTopConcreteAutCode_injective f)
    _ = m ^ F.vertexCount := by
      simp [Nat.card_eq_fintype_card, FiniteGraphShape.vertexCount]

end FiniteGraphShape

/-- Pull an ambient support back through an injective vertex map.  Edges
outside the image have no preimage. -/
noncomputable def injectionPullbackAmbientEdgeSet {m n : ℕ} (f : Fin m ↪ Fin n)
    (S : Finset (AmbientEdge n)) : Finset (AmbientEdge m) :=
  S.preimage (ambientEdgeEmbeddingOfVertexEmbedding f)
    (ambientEdgeEmbeddingOfVertexEmbedding f).injective.injOn

/-- A support fits a vertex injection when every one of its edges lies in
the embedded complete source graph. -/
def AmbientSupportFitsEmbedding {m n : ℕ} (f : Fin m ↪ Fin n)
    (S : Finset (AmbientEdge n)) : Prop :=
  S ⊆ embedAmbientEdgeSet f Finset.univ

theorem embed_injectionPullbackAmbientEdgeSet_eq_of_fits
    {m n : ℕ} (f : Fin m ↪ Fin n) (S : Finset (AmbientEdge n))
    (hfits : AmbientSupportFitsEmbedding f S) :
    embedAmbientEdgeSet f (injectionPullbackAmbientEdgeSet f S) = S := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [embedAmbientEdgeSet, Finset.mem_map] at he
    rcases he with ⟨a, ha, rfl⟩
    exact Finset.mem_preimage.mp ha
  · intro e he
    have heRange := hfits he
    rw [embedAmbientEdgeSet, Finset.mem_map] at heRange ⊢
    rcases heRange with ⟨a, _ha, hae⟩
    refine ⟨a, ?_, hae⟩
    rw [injectionPullbackAmbientEdgeSet, Finset.mem_preimage]
    simpa only [hae] using he

theorem card_injectionPullbackAmbientEdgeSet_of_fits
    {m n : ℕ} (f : Fin m ↪ Fin n) (S : Finset (AmbientEdge n))
    (hfits : AmbientSupportFitsEmbedding f S) :
    (injectionPullbackAmbientEdgeSet f S).card = S.card := by
  rw [← card_embedAmbientEdgeSet f (injectionPullbackAmbientEdgeSet f S),
    embed_injectionPullbackAmbientEdgeSet_eq_of_fits f S hfits]

theorem subset_embed_present_iff_fits_and_injectionPullback_subset
    {m n : ℕ} (f : Fin m ↪ Fin n) (S : Finset (AmbientEdge n))
    (x : BooleanConfiguration (AmbientEdge m)) :
    S ⊆ embedAmbientEdgeSet f (presentAmbientEdges x) ↔
      AmbientSupportFitsEmbedding f S ∧
        injectionPullbackAmbientEdgeSet f S ⊆ presentAmbientEdges x := by
  constructor
  · intro h
    constructor
    · exact h.trans (embedAmbientEdgeSet_mono f (Finset.subset_univ _))
    · unfold injectionPullbackAmbientEdgeSet
      unfold embedAmbientEdgeSet at h
      exact Finset.preimage_subset h
  · rintro ⟨hfits, hpull⟩
    rw [← embed_injectionPullbackAmbientEdgeSet_eq_of_fits f S hfits]
    exact embedAmbientEdgeSet_mono f hpull

/-- Conditional on one fixed vertex injection, a support which fits the
image is present in the injected Erdős--Rényi source with probability
`p^|S|`; a support which does not fit has probability zero. -/
theorem erdosRenyi_prob_support_subset_embedded_present
    {m n : ℕ} (theta : BernoulliParameter) (f : Fin m ↪ Fin n)
    (S : Finset (AmbientEdge n)) :
    (erdosRenyiLaw (n := m) theta).prob
        (FiniteLaw.event fun x ↦
          S ⊆ embedAmbientEdgeSet f (presentAmbientEdges x)) =
      if AmbientSupportFitsEmbedding f S then theta.p ^ S.card else 0 := by
  classical
  by_cases hfits : AmbientSupportFitsEmbedding f S
  · rw [if_pos hfits]
    have hevent :
        (FiniteLaw.event fun x : BooleanConfiguration (AmbientEdge m) ↦
          S ⊆ embedAmbientEdgeSet f (presentAmbientEdges x)) =
        allPresentEvent (injectionPullbackAmbientEdgeSet f S) := by
      ext x
      rw [FiniteLaw.mem_event, mem_allPresentEvent,
        subset_embed_present_iff_fits_and_injectionPullback_subset]
      simp only [hfits, true_and]
      constructor
      · intro hsub e he
        exact (mem_presentAmbientEdges x e).mp (hsub he)
      · intro hall e he
        exact (mem_presentAmbientEdges x e).mpr (hall e he)
    rw [hevent, erdosRenyiLaw,
      bernoulliProductLaw_prob_allPresent,
      card_injectionPullbackAmbientEdgeSet_of_fits f S hfits]
  · rw [if_neg hfits]
    have hevent :
        (FiniteLaw.event fun x : BooleanConfiguration (AmbientEdge m) ↦
          S ⊆ embedAmbientEdgeSet f (presentAmbientEdges x)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [FiniteLaw.mem_event,
        subset_embed_present_iff_fits_and_injectionPullback_subset] at hx
      exact hfits hx.1
    rw [hevent]
    simp [FiniteLaw.prob]

namespace FiniteLaw

/-- Fiber decomposition of a product-law event, conditioning on the right
coordinate. -/
theorem product_prob_fibers_right
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : FiniteLaw B) (s : Finset B)
    (event : B → Finset A) :
    (p.product q).prob
        (FiniteLaw.event fun z : A × B ↦ z.2 ∈ s ∧ z.1 ∈ event z.2) =
      ∑ b ∈ s, q.mass b * p.prob (event b) := by
  classical
  unfold FiniteLaw.prob FiniteLaw.event
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ b ∈ (Finset.univ.filter fun b : B ↦ b ∈ s),
          ∑ a ∈ (Finset.univ.filter fun a : A ↦ a ∈ event b),
            q.mass b * p.mass a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hbs : b ∈ s
      · simp only [hbs, true_and, if_true, FiniteLaw.product_mass]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      · simp [hbs]
    _ = ∑ b ∈ s, ∑ a ∈ event b, q.mass b * p.mass a := by simp
    _ = ∑ b ∈ s, q.mass b * ∑ a ∈ event b, p.mass a := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
    _ = ∑ b ∈ s, q.mass b * p.prob (event b) := rfl

end FiniteLaw

/-- Permutations for which the canonical `m`-vertex injection contains a
fixed ambient support. -/
noncomputable def ambientSupportFitEvent {m n : ℕ} (hfit : m ≤ n)
    (S : Finset (AmbientEdge n)) : Finset (Equiv.Perm (Fin n)) :=
  FiniteLaw.event fun sigma ↦
    AmbientSupportFitsEmbedding
      ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S

/-- Every event under the uniform permutation law has probability equal to
its cardinality divided by the number of ambient permutations. -/
theorem uniformPermutationLaw_prob_eq_card_div
    (n : ℕ) (event : Finset (Equiv.Perm (Fin n))) :
    (uniformPermutationLaw n).prob event =
      (event.card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  unfold FiniteLaw.prob uniformPermutationLaw uniformPermutationWeight
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]

/-- The injection-fit factor in Appendix equation (A.6) is bounded by
`m^v/(n)_v`, where `v` is the number of incident vertices of the support. -/
theorem uniformPermutationLaw_prob_ambientSupportFitEvent_le_pow_div
    {m n : ℕ} (hfit : m ≤ n) (S : Finset (AmbientEdge n)) :
    (uniformPermutationLaw n).prob (ambientSupportFitEvent hfit S) ≤
      (m : ℝ) ^
          (FiniteGraphShape.supportShape
            (ambientSupportGraph S)).vertexCount /
        fallingFactorial n
          (FiniteGraphShape.supportShape
            (ambientSupportGraph S)).vertexCount := by
  let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
  let copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
    supportConcreteCopy S
  let plant : SimpleGraph (Fin n) :=
    (⊤ : SimpleGraph (Fin m)).map (Fin.castLEEmb hfit)
  have hevent : ambientSupportFitEvent hfit S =
      FiniteLaw.event fun sigma : Equiv.Perm (Fin n) ↦
        F.concreteCopyEdges copy ⊆ permutedPlantEdges plant sigma := by
    ext sigma
    simp only [ambientSupportFitEvent, FiniteLaw.mem_event,
      AmbientSupportFitsEmbedding,
      F, copy, concreteCopyEdges_supportConcreteCopy, plant,
      permutedPlantEdges_mappedTop_castLE]
  rw [uniformPermutationLaw_prob_eq_card_div, hevent]
  have hcount :
      (FiniteLaw.event fun sigma : Equiv.Perm (Fin n) ↦
        F.concreteCopyEdges copy ⊆
          permutedPlantEdges plant sigma).card =
      permutationContainmentCount plant (F.concreteCopyEdges copy) := by
    congr 1
    ext sigma
    simp [FiniteLaw.event]
  rw [hcount]
  change (permutationContainmentCount plant
      (F.concreteCopyEdges copy) : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤
      (m : ℝ) ^ F.vertexCount / fallingFactorial n F.vertexCount
  rw [F.permutationContainmentProbability_concreteCopyEdges plant copy]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast F.nonInducedCopyCount_mappedTop_mul_aut_le_pow
      (Fin.castLEEmb hfit)
  · unfold fallingFactorial
    positivity

set_option maxHeartbeats 800000 in
/-- Exact factorization for an untruncated uniformly injected Erdős--Rényi
source: the edge-presence factor is `p^|S|`, and the remaining factor is
precisely the probability that the random injection contains the support's
vertices. -/
theorem uniformlyInjected_erdosRenyi_containment_eq_pow_mul_fitProbability
    {m n : ℕ} (hfit : m ≤ n) (theta : BernoulliParameter)
    (S : Finset (AmbientEdge n)) :
    randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit
          ((erdosRenyiLaw (n := m) theta).map presentAmbientEdges)) S =
      theta.p ^ S.card *
        (uniformPermutationLaw n).prob (ambientSupportFitEvent hfit S) := by
  let p := erdosRenyiLaw (n := m) theta
  let q := uniformPermutationLaw n
  let generated :
      (BooleanConfiguration (AmbientEdge m) × Equiv.Perm (Fin n)) →
        Finset (AmbientEdge n) := fun z ↦
    embedAmbientEdgeSet
      ((Fin.castLEEmb hfit).trans z.2.toEmbedding) (presentAmbientEdges z.1)
  have hinjected :
      uniformlyInjectedPlantLaw hfit (p.map presentAmbientEdges) =
        (p.product q).map generated := by
    unfold uniformlyInjectedPlantLaw generated
    rw [FiniteLaw.map_product_left, FiniteLaw.map_map]
    rfl
  rw [show erdosRenyiLaw (n := m) theta = p by rfl, hinjected]
  unfold randomPlantContainmentProbability
  rw [FiniteLaw.prob_map]
  let sourceEvent : Equiv.Perm (Fin n) →
      Finset (BooleanConfiguration (AmbientEdge m)) := fun sigma ↦
    FiniteLaw.event fun x ↦
      S ⊆ embedAmbientEdgeSet
        ((Fin.castLEEmb hfit).trans sigma.toEmbedding)
          (presentAmbientEdges x)
  have hproduct :
      (p.product q).prob
          (Finset.univ.filter fun z ↦ generated z ∈
            Finset.univ.filter fun A : Finset (AmbientEdge n) ↦ S ⊆ A) =
        ∑ sigma : Equiv.Perm (Fin n),
          q.mass sigma * p.prob (sourceEvent sigma) := by
    simpa only [FiniteLaw.event, Finset.mem_filter, Finset.mem_univ,
      true_and, sourceEvent, generated] using
      (FiniteLaw.product_prob_fibers_right p q Finset.univ sourceEvent)
  refine Eq.trans (congrArg (p.product q).prob (by
    ext z
    simp)) (hproduct.trans ?_)
  have hconditional (sigma : Equiv.Perm (Fin n)) :
      p.prob (sourceEvent sigma) =
        if AmbientSupportFitsEmbedding
            ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S then
          theta.p ^ S.card else 0 := by
    simpa only [p, sourceEvent] using
      erdosRenyi_prob_support_subset_embedded_present theta
        ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S
  simp_rw [hconditional]
  unfold ambientSupportFitEvent FiniteLaw.prob FiniteLaw.event
  rw [Finset.sum_filter]
  calc
    (∑ sigma : Equiv.Perm (Fin n),
        q.mass sigma *
          (if AmbientSupportFitsEmbedding
              ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S then
            theta.p ^ S.card else 0)) =
        ∑ sigma : Equiv.Perm (Fin n),
          if AmbientSupportFitsEmbedding
              ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S then
            q.mass sigma * theta.p ^ S.card else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      split <;> simp_all
    _ = ∑ sigma ∈ Finset.univ.filter (fun sigma : Equiv.Perm (Fin n) ↦
          AmbientSupportFitsEmbedding
            ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S),
          q.mass sigma * theta.p ^ S.card := by
      rw [Finset.sum_ite]
      simp
    _ = (∑ sigma ∈ Finset.univ.filter
          (fun sigma : Equiv.Perm (Fin n) ↦
            AmbientSupportFitsEmbedding
              ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S),
          q.mass sigma) * theta.p ^ S.card := by
      rw [Finset.sum_mul]
    _ = theta.p ^ S.card *
        ∑ sigma ∈ Finset.univ.filter
          (fun sigma : Equiv.Perm (Fin n) ↦
            AmbientSupportFitsEmbedding
              ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S),
          q.mass sigma := by ring
    _ = theta.p ^ S.card *
        ∑ sigma : Equiv.Perm (Fin n),
          if AmbientSupportFitsEmbedding
              ((Fin.castLEEmb hfit).trans sigma.toEmbedding) S then
            (uniformPermutationLaw n).mass sigma else 0 := by
      congr 1
      rw [Finset.sum_ite]
      simp [q]

/-- Appendix equation (A.6) for the actual twice-truncated source plant,
before evaluating the original uniformly injected Erdős--Rényi
containment probability. -/
theorem uniformlyInjected_twiceTruncated_containment_le_original
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n N : ℕ)
    (hfit : m n ≤ N) (S : Finset (AmbientEdge N)) :
    randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit
          (twiceTruncatedPlantLawAt lam r gamma m g n)) S ≤
      randomPlantContainmentProbability
        (uniformlyInjectedPlantLaw hfit
          ((erdosRenyiLaw (n := m n)
            (sparseBernoulliParameter lam (m n))).map
              presentAmbientEdges)) S := by
  simpa only [twiceTruncatedPlantLawAt] using
    uniformlyInjected_sparseErdosRenyi_containment_mono
      hfit lam (twiceTruncatedPlantEdgesAt lam r gamma m g n)
      (twiceTruncatedPlantEdgesAt_subset_present lam r gamma m g n) S

end

end LowDegree
