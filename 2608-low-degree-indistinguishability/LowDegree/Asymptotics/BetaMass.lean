import LowDegree.Asymptotics.ModelConsequences
import LowDegree.Combinatorics.GraphShapeClasses

/-!
# Low-degree exact mass to leading `β` mass

This file formalizes Equation (4.1).  It combines the duplicate-free class
regrouping of Equation (3.5), the concrete edge-count consequence of Lemma
3.2, and the uniform comparison in Lemma 3.1.
-/

namespace LowDegree

open Asymptotics Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace BoundedTreewidthPlantModel

/-- A degree envelope large enough for every nonempty shape occurring in the
plant. -/
def occurrenceEdgeEnvelope (M : BoundedTreewidthPlantModel) (n : ℕ) : ℕ :=
  max 1 (M.plant n).edgeFinset.card

/-- The finite leading-weight mass over all nonempty support classes in the
degree-`Dₙ` projection. -/
noncomputable def lowDegreeBetaMass
    (M : BoundedTreewidthPlantModel) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ M.degreeCutoff n,
    C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

/-- The full leading `β` mass after weighting every class by its squared
noise eigenvalue.  This is the target in Equation (4.2). -/
noncomputable def noisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n,
    (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
      C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

/-- An occurring shape has no more edges than its ambient plant. -/
private theorem shape_edgeCount_le_plant_of_occurs
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

/-- The occurrence envelope is still `o(√n)` under the concrete
low-degree hypothesis. -/
theorem occurrenceEdgeEnvelope_isLittleO_sqrt
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    (fun n ↦ (M.occurrenceEdgeEnvelope n : ℝ)) =o[atTop]
      (fun n ↦ Real.sqrt (n : ℝ)) := by
  have hedge := M.edgeCount_isLittleO_sqrt hlow
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    by
      simpa only [Real.sqrt_eq_rpow] using
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          tendsto_natCast_atTop_atTop
  have hone : (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun n ↦ Real.sqrt (n : ℝ)) := by
    rw [isLittleO_const_left_of_ne one_ne_zero]
    exact hsqrt.congr' <| Eventually.of_forall fun n ↦
      (Real.norm_of_nonneg (Real.sqrt_nonneg (n : ℝ))).symm
  have hsum := hone.add hedge
  have hmajor :
      (fun n ↦ (M.occurrenceEdgeEnvelope n : ℝ)) =O[atTop]
        (fun n ↦ 1 + ((M.plant n).edgeFinset.card : ℝ)) := by
    apply Eventually.isBigO
    exact Eventually.of_forall fun n ↦ by
      have hnat : max 1 (M.plant n).edgeFinset.card ≤
          1 + (M.plant n).edgeFinset.card := by omega
      exact_mod_cast hnat
  exact hmajor.trans_isLittleO hsum

/-- Leading weights are nonnegative. -/
private theorem graphBetaWeight_nonneg
    (M : BoundedTreewidthPlantModel) (n : ℕ)
    (F : FiniteGraphShape) :
    0 ≤ F.graphBetaWeight M.backgroundDensity n (M.plant n) := by
  unfold FiniteGraphShape.graphBetaWeight betaWeight
  exact mul_nonneg
    (div_nonneg
      (div_nonneg (pow_nonneg (Nat.cast_nonneg n) F.edgeCount)
        (pow_nonneg (Nat.cast_nonneg n) F.vertexCount))
      (pow_nonneg M.backgroundDensity_pos.le F.edgeCount))
    (mul_nonneg (sq_nonneg (F.nonInducedCopyCount (M.plant n) : ℝ))
      (Nat.cast_nonneg _))

/-- Uniform eventual comparison summed over all degree-restricted occurring
classes.  Classes absent from the plant contribute zero on both sides. -/
theorem eventually_lowDegreeBetaMass_le_two_mul_exactMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    ∀ᶠ n in atTop,
      M.lowDegreeBetaMass n ≤ 2 * (M.lowDegreeNormSq n - 1) := by
  let d := M.occurrenceEdgeEnvelope
  have hd : (fun n ↦ (d n : ℝ)) =o[atTop]
      (fun n ↦ Real.sqrt (n : ℝ)) :=
    M.occurrenceEdgeEnvelope_isLittleO_sqrt hlow
  have hcompare := alpha_beta_eventually_between_half_and_two
    M.backgroundDensity M.backgroundDensity_pos hd
  have hp := eventually_sparseBernoulliParameter_p_eq
    M.backgroundDensity_pos
  filter_upwards [hcompare, hp] with n hn hpn
  unfold lowDegreeBetaMass
  rw [BoundedTreewidthPlantModel.lowDegreeNormSq,
    plantedLowDegreeNormSq_sub_one_eq_sum_alphaWeights
      (M.parameter n) (M.plant n) (M.degreeCutoff n)
      M.backgroundDensity hpn]
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
      exact (shape_edgeCount_le_plant_of_occurs C.shape (M.plant n) hocc).trans
        (Nat.le_max_right _ _)
    have hhalf := (hn datum hFed).1
    change C.shape.graphBetaWeight M.backgroundDensity n (M.plant n) ≤
      2 * alphaWeight M.backgroundDensity n C.shape.edgeCount
        C.shape.vertexCount (C.shape.nonInducedCopyCount (M.plant n))
          (Fintype.card C.shape.Automorphism)
    change betaWeight M.backgroundDensity n C.shape.edgeCount
        C.shape.vertexCount (C.shape.nonInducedCopyCount (M.plant n))
          (Fintype.card C.shape.Automorphism) ≤ _
    dsimp [datum, FiniteGraphShape.leadingTermDatumOfOccurrence] at hhalf
    linarith
  · have hzero : C.shape.nonInducedCopyCount (M.plant n) = 0 :=
      Nat.eq_zero_of_not_pos hocc
    simp [FiniteGraphShape.graphBetaWeight, betaWeight, alphaWeight, hzero]

/-- **Equation (4.1).**  The total leading `β` mass in the low-degree
range is `o(1)` for the concrete planted model. -/
theorem lowDegreeBetaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    Vanishes M.lowDegreeBetaMass := by
  have hupper := M.eventually_lowDegreeBetaMass_le_two_mul_exactMass hlow
  have hright : Vanishes (fun n ↦ 2 * (M.lowDegreeNormSq n - 1)) :=
    hlow.sub_one.const_mul 2
  have hnonneg : ∀ n, 0 ≤ M.lowDegreeBetaMass n := by
    intro n
    exact Finset.sum_nonneg fun C _ ↦ graphBetaWeight_nonneg M n C.shape
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper hright

/-- Equation (4.2)'s pointwise transfer: eventually the exact full noised
second-moment excess is at most twice its leading `β` target. -/
theorem eventually_noisedNormSq_sub_one_le_two_mul_noisedBetaMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate) :
    ∀ᶠ n in atTop,
      M.noisedNormSq noise n - 1 ≤ 2 * M.noisedBetaMass noise n := by
  let d := M.occurrenceEdgeEnvelope
  have hd : (fun n ↦ (d n : ℝ)) =o[atTop]
      (fun n ↦ Real.sqrt (n : ℝ)) :=
    M.occurrenceEdgeEnvelope_isLittleO_sqrt hlow
  have hcompare := alpha_beta_eventually_between_half_and_two
    M.backgroundDensity M.backgroundDensity_pos hd
  have hp := eventually_sparseBernoulliParameter_p_eq
    M.backgroundDensity_pos
  filter_upwards [hcompare, hp] with n hn hpn
  rw [BoundedTreewidthPlantModel.noisedNormSq,
    plantedNoisedNormSq_sub_one_eq_sum_noisedAlphaWeights
      (M.parameter n) noise (M.plant n) M.backgroundDensity hpn]
  unfold noisedBetaMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _hC
  by_cases hocc : 0 < C.shape.nonInducedCopyCount (M.plant n)
  · have hedge : 0 < C.shape.edgeCount := by
      rw [C.shape_edgeCount_eq_representative_card]
      exact Finset.card_pos.mpr C.representative.2
    let datum : LeadingTermDatum n :=
      C.shape.leadingTermDatumOfOccurrence (M.plant n) hedge hocc
    have hFed : datum.edgeCount ≤ d n := by
      change C.shape.edgeCount ≤
        max 1 (M.plant n).edgeFinset.card
      exact (shape_edgeCount_le_plant_of_occurs C.shape (M.plant n) hocc).trans
        (Nat.le_max_right _ _)
    have hupper := (hn datum hFed).2
    dsimp [datum, FiniteGraphShape.leadingTermDatumOfOccurrence] at hupper
    have hnoise : 0 ≤
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) :=
      pow_nonneg (sub_nonneg.mpr noise.2.2.le) _
    have hmul := mul_le_mul_of_nonneg_left hupper hnoise
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

/-- If the leading noised `β` target vanishes, then the actual noised
likelihood ratio has second moment `1+o(1)`. -/
theorem noisedNormSq_tendsToOne_of_betaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate)
    (hbeta : Vanishes (M.noisedBetaMass noise)) :
    TendsToOne (M.noisedNormSq noise) := by
  apply tendsToOne_iff_vanishes_sub.mpr
  have hnonneg : ∀ n, 0 ≤ M.noisedNormSq noise n - 1 :=
    fun n ↦ sub_nonneg.mpr (one_le_plantedNoisedNormSq
      (M.parameter n) noise (M.plant n))
  have hupper :=
    M.eventually_noisedNormSq_sub_one_le_two_mul_noisedBetaMass hlow noise
  have hright : Vanishes (fun n ↦ 2 * M.noisedBetaMass noise n) :=
    hbeta.const_mul 2
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper hright

end BoundedTreewidthPlantModel

end

end LowDegree
