import LowDegree.Asymptotics.BetaMass
import LowDegree.Asymptotics.SubcriticalEndgame
import LowDegree.Combinatorics.GraphShapeClasses

/-!
# Forest-restricted exact and leading masses

The forest-truncated likelihood has no Fourier mass on cyclic supports, and
all its remaining coefficients are dominated by the coefficients of the
ordinary noised likelihood.  This file performs that comparison without any
informal appeal to graph isomorphism classes, then transfers the resulting
exact class sum to the paper's leading `β` weights.
-/

namespace LowDegree

open Asymptotics Filter Topology
open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Finite Fourier comparison -/

/-- Removing the constant Fourier coefficient from the forest-truncated
second moment leaves exactly the sum over nonempty supports. -/
theorem forestTruncatedNormSq_sub_one_eq_sum_nonempty
    {n : ℕ} (theta : BernoulliParameter) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    bernoulliInner theta
        (forestTruncatedLikelihood theta noise plant)
        (forestTruncatedLikelihood theta noise plant) - 1 =
      ∑ S : Finset (AmbientEdge n) with S.Nonempty,
        (fourierCoeff theta
          (forestTruncatedLikelihood theta noise plant) S) ^ 2 := by
  let weight : Finset (AmbientEdge n) → ℝ := fun S ↦
    (fourierCoeff theta
      (forestTruncatedLikelihood theta noise plant) S) ^ 2
  have hempty : weight ∅ = 1 := by
    dsimp [weight]
    rw [fourierCoeff_empty]
    have hmean : bernoulliExpectation theta
        (forestTruncatedLikelihood theta noise plant) = 1 := by
      exact bernoulliExpectation_randomForcedLikelihood theta
        (forestTruncatedRetainedPlantLaw noise plant)
    rw [hmean, one_pow]
  have hempty_mem : (∅ : Finset (AmbientEdge n)) ∈
      (Finset.univ : Finset (Finset (AmbientEdge n))) := Finset.mem_univ _
  rw [fourierParseval_sq]
  change (∑ S : Finset (AmbientEdge n), weight S) - 1 = _
  have hsplit : (∑ S : Finset (AmbientEdge n), weight S) =
      (∑ S ∈ (Finset.univ : Finset (Finset (AmbientEdge n))).erase ∅,
        weight S) + weight ∅ :=
    (Finset.sum_erase_add Finset.univ weight hempty_mem).symm
  rw [hsplit, hempty]
  have herase :
      (Finset.univ : Finset (Finset (AmbientEdge n))).erase ∅ =
        Finset.univ.filter (fun S : Finset (AmbientEdge n) ↦ S.Nonempty) := by
    ext S
    simp [Finset.nonempty_iff_ne_empty]
  rw [herase]
  simp only [add_sub_cancel_right]
  rfl

theorem fourierCoeff_forestTruncatedLikelihood_nonneg
    {n : ℕ} (theta : BernoulliParameter) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) :
    0 ≤ fourierCoeff theta
      (forestTruncatedLikelihood theta noise plant) S := by
  rw [forestTruncatedLikelihood, fourierCoeff_randomForcedLikelihood]
  exact mul_nonneg
    (randomPlantContainmentProbability_nonneg _ _)
    (pow_nonneg theta.forcedWeight_pos.le _)

theorem fourierCoeff_noisedLikelihood_nonneg
    {n : ℕ} (theta : BernoulliParameter) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) :
    0 ≤ fourierCoeff theta (noisedLikelihood theta noise plant) S := by
  rw [← randomForcedLikelihood_retainedPlantLaw_eq_noisedLikelihood,
    fourierCoeff_randomForcedLikelihood]
  exact mul_nonneg
    (randomPlantContainmentProbability_nonneg _ _)
    (pow_nonneg theta.forcedWeight_pos.le _)

/-- The two spanning support-graph definitions used by the Fourier quotient
and by forest truncation are definitionally the same graph. -/
theorem graphOfAmbientEdges_eq_ambientSupportGraph
    {n : ℕ} (S : Finset (AmbientEdge n)) :
    graphOfAmbientEdges S = ambientSupportGraph S := by
  rfl

/-- If the edge support of a concrete copy is a forest, then its abstract
shape is acyclic.  This is the one direction needed to discard every class
whose shape contains a cycle. -/
theorem FiniteGraphShape.isAcyclic_of_isForest_concreteCopy
    {n : ℕ} (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hforest : IsForestEdgeSet (F.concreteCopyEdges copy)) :
    F.graph.IsAcyclic := by
  let edges := F.concreteCopyEdges copy
  have hambient : (ambientSupportGraph edges).IsAcyclic := by
    rw [← graphOfAmbientEdges_eq_ambientSupportGraph]
    exact hforest
  let inclusion : copy.1.coe →g ambientSupportGraph edges :=
    { toFun := fun v ↦ v.1
      map_rel' := by
        intro a b hab
        have htop : (⊤ : SimpleGraph (Fin n)).Adj a.1 b.1 :=
          copy.1.adj_sub hab
        let e : AmbientEdge n := ⟨s(a.1, b.1), htop⟩
        have he : e ∈ edges := by
          rw [show edges = F.concreteCopyEdges copy by rfl,
            F.mem_concreteCopyEdges]
          exact hab
        have hedge :=
          (mem_ambientSupportGraph_edgeSet_iff edges e).2 he
        exact hedge }
  have hinj : Function.Injective inclusion := by
    intro a b hab
    exact Subtype.ext hab
  have hcopy : copy.1.coe.IsAcyclic := hambient.comap inclusion hinj
  exact (F.chosenIso copy).isAcyclic_iff.mpr hcopy

/-- Exact noised class mass restricted to acyclic graph shapes. -/
noncomputable def forestNoisedExactClassMass
    {n : ℕ} (theta : BernoulliParameter) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) : ℝ :=
  ∑ C : AmbientSupportClass n with C.shape.graph.IsAcyclic,
    (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
      (((1 - theta.p) / theta.p) ^ C.shape.edgeCount *
        ((C.shape.nonInducedCopyCount plant : ℝ) ^ 2 *
          (Fintype.card C.shape.Automorphism : ℝ)) /
            fallingFactorial n C.shape.vertexCount)

/-- Parseval plus coefficient domination bounds the forest-truncated excess
by the exact noised mass over acyclic graph classes. -/
theorem forestTruncatedNormSq_sub_one_le_forestNoisedExactClassMass
    {n : ℕ} (theta : BernoulliParameter) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    bernoulliInner theta
        (forestTruncatedLikelihood theta noise plant)
        (forestTruncatedLikelihood theta noise plant) - 1 ≤
      forestNoisedExactClassMass theta noise plant := by
  rw [forestTruncatedNormSq_sub_one_eq_sum_nonempty]
  let restrictedWeight : Finset (AmbientEdge n) → ℝ := fun S ↦
    if IsForestEdgeSet S then
      (fourierCoeff theta (noisedLikelihood theta noise plant) S) ^ 2
    else 0
  calc
    (∑ S : Finset (AmbientEdge n) with S.Nonempty,
        (fourierCoeff theta
          (forestTruncatedLikelihood theta noise plant) S) ^ 2) ≤
        ∑ S : Finset (AmbientEdge n) with S.Nonempty,
          restrictedWeight S := by
      apply Finset.sum_le_sum
      intro S _hS
      by_cases hforest : IsForestEdgeSet S
      · rw [show restrictedWeight S =
            (fourierCoeff theta
              (noisedLikelihood theta noise plant) S) ^ 2 by
            simp [restrictedWeight, hforest]]
        apply (sq_le_sq₀
          (fourierCoeff_forestTruncatedLikelihood_nonneg
            theta noise plant S)
          (fourierCoeff_noisedLikelihood_nonneg theta noise plant S)).2
        exact fourierCoeff_forestTruncatedLikelihood_le_noisedLikelihood
          theta noise plant S
      · rw [fourierCoeff_forestTruncatedLikelihood_eq_zero_of_cyclic
          theta noise plant S hforest]
        simp [restrictedWeight, hforest]
    _ = ∑ C : AmbientSupportClass n,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          restrictedWeight (C.shape.concreteCopyEdges copy) :=
      sum_nonempty_ambientSupports_eq_sum_concreteCopyClasses restrictedWeight
    _ ≤ ∑ C : AmbientSupportClass n with C.shape.graph.IsAcyclic,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff theta (noisedLikelihood theta noise plant)
            (C.shape.concreteCopyEdges copy)) ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro C _hC
      by_cases hacyclic : C.shape.graph.IsAcyclic
      · rw [if_pos hacyclic]
        apply Finset.sum_le_sum
        intro copy _hcopy
        by_cases hforest :
            IsForestEdgeSet (C.shape.concreteCopyEdges copy)
        · simp [restrictedWeight, hforest]
        · simp only [restrictedWeight, if_neg hforest]
          exact sq_nonneg _
      · rw [if_neg hacyclic]
        apply Finset.sum_nonpos
        intro copy _hcopy
        have hnotForest :
            ¬IsForestEdgeSet (C.shape.concreteCopyEdges copy) := by
          intro hforest
          exact hacyclic
            (C.shape.isAcyclic_of_isForest_concreteCopy copy hforest)
        simp [restrictedWeight, hnotForest]
    _ = forestNoisedExactClassMass theta noise plant := by
      unfold forestNoisedExactClassMass
      apply Finset.sum_congr rfl
      intro C _hC
      exact C.shape.sum_fourierCoeff_sq_noised_over_concreteCopies
        theta noise plant C.representativeCopy

/-! ## Transfer to leading beta weights -/

namespace BoundedTreewidthPlantModel

/-- Leading noised mass restricted to acyclic graph classes. -/
noncomputable def forestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with C.shape.graph.IsAcyclic,
    (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
      C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

private theorem forest_shape_edgeCount_le_plant_of_occurs
    {n : ℕ} (F : FiniteGraphShape)
    (plant : SimpleGraph (Fin n))
    (hcopy : 0 < F.nonInducedCopyCount plant) :
    F.edgeCount ≤ plant.edgeFinset.card := by
  have hcard : 0 < Fintype.card (F.ConcreteCopy plant) := hcopy
  obtain ⟨copy⟩ := Fintype.card_pos_iff.mp hcard
  let emb : F.graph.edgeSet ↪ plant.edgeSet :=
    (F.concreteCopyToAmbientCopy copy).mapEdgeSet
  have hle := Fintype.card_le_of_embedding emb
  calc
    F.edgeCount = Fintype.card F.graph.edgeSet := by
      rw [F.edgeCount_eq_ncard, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card]
    _ ≤ Fintype.card plant.edgeSet := hle
    _ = plant.edgeFinset.card := SimpleGraph.edgeFinset_card.symm

/-- Eventual exact-to-leading comparison, now only over forest classes. -/
theorem eventually_forestNoisedExactClassMass_le_two_mul_betaMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate) :
    ∀ᶠ n in atTop,
      forestNoisedExactClassMass (M.parameter n) noise (M.plant n) ≤
        2 * M.forestNoisedBetaMass noise n := by
  let d := M.occurrenceEdgeEnvelope
  have hd : (fun n ↦ (d n : ℝ)) =o[atTop]
      (fun n ↦ Real.sqrt (n : ℝ)) :=
    M.occurrenceEdgeEnvelope_isLittleO_sqrt hlow
  have hcompare := alpha_beta_eventually_between_half_and_two
    M.backgroundDensity M.backgroundDensity_pos hd
  have hp := eventually_sparseBernoulliParameter_p_eq
    M.backgroundDensity_pos
  filter_upwards [hcompare, hp] with n hn hpn
  unfold forestNoisedExactClassMass forestNoisedBetaMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  by_cases hocc : 0 < C.shape.nonInducedCopyCount (M.plant n)
  · have hedge : 0 < C.shape.edgeCount := by
      rw [C.shape_edgeCount_eq_representative_card]
      exact Finset.card_pos.mpr C.representative.2
    let datum : LeadingTermDatum n :=
      C.shape.leadingTermDatumOfOccurrence (M.plant n) hedge hocc
    have hFed : datum.edgeCount ≤ d n := by
      change C.shape.edgeCount ≤
        max 1 (M.plant n).edgeFinset.card
      exact (forest_shape_edgeCount_le_plant_of_occurs
        C.shape (M.plant n) hocc).trans (Nat.le_max_right _ _)
    have hupper := (hn datum hFed).2
    dsimp [datum, FiniteGraphShape.leadingTermDatumOfOccurrence] at hupper
    have hnoise : 0 ≤
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) :=
      pow_nonneg (sub_nonneg.mpr noise.2.2.le) _
    have hmul := mul_le_mul_of_nonneg_left hupper hnoise
    rw [show (M.parameter n).p = M.backgroundDensity / (n : ℝ) from hpn]
    change
      (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          alphaWeight M.backgroundDensity n C.shape.edgeCount
            C.shape.vertexCount (C.shape.nonInducedCopyCount (M.plant n))
              (Fintype.card C.shape.Automorphism) ≤
        2 * ((1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight M.backgroundDensity n (M.plant n))
    change
      (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          alphaWeight M.backgroundDensity n C.shape.edgeCount
            C.shape.vertexCount (C.shape.nonInducedCopyCount (M.plant n))
              (Fintype.card C.shape.Automorphism) ≤
        2 * ((1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          betaWeight M.backgroundDensity n C.shape.edgeCount
            C.shape.vertexCount (C.shape.nonInducedCopyCount (M.plant n))
              (Fintype.card C.shape.Automorphism))
    nlinarith
  · have hzero : C.shape.nonInducedCopyCount (M.plant n) = 0 :=
      Nat.eq_zero_of_not_pos hocc
    simp [FiniteGraphShape.graphBetaWeight, betaWeight, alphaWeight, hzero]

/-- Vanishing of the forest-restricted leading mass closes the actual
forest-truncated second moment. -/
theorem forestTruncatedNormSq_tendsToOne_of_betaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate)
    (hbeta : Vanishes (M.forestNoisedBetaMass noise)) :
    TendsToOne (M.forestTruncatedNormSq noise) := by
  apply tendsToOne_iff_vanishes_sub.mpr
  have hnonneg : ∀ n,
      0 ≤ M.forestTruncatedNormSq noise n - 1 := by
    intro n
    rw [forestTruncatedNormSq,
      forestTruncatedNormSq_sub_one_eq_sum_nonempty]
    exact Finset.sum_nonneg fun S _ ↦ sq_nonneg _
  have hexact :=
    M.eventually_forestNoisedExactClassMass_le_two_mul_betaMass hlow noise
  have hupper : ∀ᶠ n in atTop,
      M.forestTruncatedNormSq noise n - 1 ≤
        2 * M.forestNoisedBetaMass noise n := by
    filter_upwards [hexact] with n hn
    exact (forestTruncatedNormSq_sub_one_le_forestNoisedExactClassMass
      (M.parameter n) noise (M.plant n)).trans hn
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper
    (hbeta.const_mul 2)

end BoundedTreewidthPlantModel

end

end LowDegree
