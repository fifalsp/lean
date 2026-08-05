import LowDegree.RandomPlant

/-!
# Projected second moments for random planted edge sets

This is the finite Fourier identity used in Equation (A.5).  It applies to
any law on finite forced edge sets, including the pruned and locally truncated
supercritical plant.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Degree-`D` projection of a random-plant likelihood. -/
noncomputable def randomForcedLowDegreeLikelihood
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) (D : ℕ) :
    BooleanConfiguration E → ℝ :=
  lowDegreeProjection theta D (randomForcedLikelihood theta plant)

/-- Squared projected norm for a random planted-set mixture. -/
noncomputable def randomForcedLowDegreeNormSq
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) (D : ℕ) : ℝ :=
  bernoulliInner theta
    (randomForcedLowDegreeLikelihood theta plant D)
    (randomForcedLowDegreeLikelihood theta plant D)

/-- Parseval formula for the random-plant projected second moment. -/
theorem randomForcedLowDegreeNormSq_eq_sum
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) (D : ℕ) :
    randomForcedLowDegreeNormSq theta plant D =
      ∑ S : Finset E with S.card ≤ D,
        (randomPlantContainmentProbability plant S *
          theta.forcedWeight ^ S.card) ^ 2 := by
  rw [randomForcedLowDegreeNormSq, randomForcedLowDegreeLikelihood,
    lowDegreeProjection_norm_sq]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [fourierCoeff_randomForcedLikelihood]

/-- The empty support contributes exactly one. -/
theorem randomPlant_emptySupport_contribution
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) :
    (randomPlantContainmentProbability plant ∅ * theta.forcedWeight ^ 0) ^ 2 = 1 := by
  have hempty : randomPlantContainmentProbability plant ∅ = 1 := by
    unfold randomPlantContainmentProbability FiniteLaw.prob
    simpa using plant.sum_mass
  simp [hempty]

/-- **Equation (A.5), support-level exact form.**

Subtracting the constant character leaves precisely the sum over nonempty
supports of degree at most `D`. -/
theorem randomForcedLowDegreeNormSq_sub_one_eq_sum_nonempty
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) (D : ℕ) :
    randomForcedLowDegreeNormSq theta plant D - 1 =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        (randomPlantContainmentProbability plant S *
          theta.forcedWeight ^ S.card) ^ 2 := by
  rw [randomForcedLowDegreeNormSq_eq_sum]
  let allSupports : Finset (Finset E) :=
    Finset.univ.filter fun S ↦ S.card ≤ D
  let nonemptySupports : Finset (Finset E) :=
    Finset.univ.filter fun S ↦ S.card ≤ D ∧ S.Nonempty
  have hempty_mem : (∅ : Finset E) ∈ allSupports := by
    simp [allSupports]
  have hdecomp : allSupports = insert ∅ nonemptySupports := by
    ext S
    by_cases hS : S = ∅
    · subst S
      simp [allSupports, nonemptySupports]
    · have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      simp [allSupports, nonemptySupports, hS, hnonempty]
  change (∑ S ∈ allSupports,
      (randomPlantContainmentProbability plant S *
        theta.forcedWeight ^ S.card) ^ 2) - 1 = _
  rw [hdecomp, Finset.sum_insert]
  · simp only [Finset.card_empty]
    rw [randomPlant_emptySupport_contribution]
    simp [nonemptySupports]
  · simp [nonemptySupports]

/-- Every projected random-plant second moment is at least one. -/
theorem one_le_randomForcedLowDegreeNormSq
    (theta : BernoulliParameter) (plant : FiniteLaw (Finset E)) (D : ℕ) :
    1 ≤ randomForcedLowDegreeNormSq theta plant D := by
  rw [← sub_nonneg,
    randomForcedLowDegreeNormSq_sub_one_eq_sum_nonempty]
  exact Finset.sum_nonneg fun S _ ↦ sq_nonneg _

end

end LowDegree
