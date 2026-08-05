import LowDegree.PlantedModel
import LowDegree.Probability.Convergence

/-!
# Random finite planted edge sets

The deterministic plant in `PlantedModel.lean` becomes random after edge
deletion and, in the subcritical proof, after forest truncation.  This file
provides the common finite-mixture layer.  A random retained plant is simply a
`FiniteLaw (Finset E)`.  Its observation likelihood is the mixture of the
fixed-set forcing likelihoods.

The main identity says that the Fourier coefficient at `S` is the probability
that the random plant contains `S`, multiplied by the usual Bernoulli forcing
weight.  The final section treats truncation by any hereditary property.  It
therefore applies to acyclicity once edge sets are interpreted as graphs.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace FiniteLaw

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

/-- Push a finite law forward through a function. -/
noncomputable def map (p : FiniteLaw Ω) (f : Ω → Ω') : FiniteLaw Ω' where
  mass y := ∑ x, if f x = y then p.mass x else 0
  mass_nonneg y := Finset.sum_nonneg fun x _ ↦ by
    split <;> simp_all [p.mass_nonneg]
  sum_mass := by
    calc
      (∑ y, ∑ x, if f x = y then p.mass x else 0) =
          ∑ x, ∑ y, if f x = y then p.mass x else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ x, p.mass x := by simp
      _ = 1 := p.sum_mass

@[simp]
theorem map_mass (p : FiniteLaw Ω) (f : Ω → Ω') (y : Ω') :
    (p.map f).mass y = ∑ x, if f x = y then p.mass x else 0 :=
  rfl

/-- Expectation under a pushforward law. -/
theorem expect_map (p : FiniteLaw Ω) (f : Ω → Ω') (g : Ω' → ℝ) :
    (p.map f).expect g = p.expect (fun x ↦ g (f x)) := by
  simp only [expect, map_mass]
  calc
    (∑ y, (∑ x, if f x = y then p.mass x else 0) * g y) =
        ∑ y, ∑ x, (if f x = y then p.mass x else 0) * g y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (if f x = y then p.mass x else 0) * g y := by
          rw [Finset.sum_comm]
    _ = ∑ x, p.mass x * g (f x) := by simp

/-- Events pull back under a finite-law pushforward. -/
theorem prob_map (p : FiniteLaw Ω) (f : Ω → Ω') (event : Finset Ω') :
    (p.map f).prob event =
      p.prob (Finset.univ.filter fun x : Ω ↦ f x ∈ event) := by
  classical
  unfold prob
  simp only [map_mass]
  calc
    (∑ y ∈ event, ∑ x, if f x = y then p.mass x else 0) =
        ∑ x, ∑ y ∈ event, if f x = y then p.mass x else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x, if f x ∈ event then p.mass x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : f x ∈ event <;> simp [hx]
    _ = ∑ x ∈ Finset.univ.filter (fun x : Ω ↦ f x ∈ event), p.mass x := by
          rw [Finset.sum_ite]
          simp

end FiniteLaw

section Mixture

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Likelihood ratio obtained by first sampling a finite forced coordinate set
and then forcing every coordinate in that set to be present. -/
noncomputable def randomForcedLikelihood
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (x : BooleanConfiguration E) : ℝ :=
  ∑ A : Finset E, plant.mass A * forcedLikelihood θ A x

theorem randomForcedLikelihood_nonneg
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (x : BooleanConfiguration E) :
    0 ≤ randomForcedLikelihood θ plant x := by
  exact Finset.sum_nonneg fun A _ ↦
    mul_nonneg (plant.mass_nonneg A) (forcedLikelihood_nonneg θ A x)

/-- The containment probability of a support in a random finite plant. -/
noncomputable def randomPlantContainmentProbability
    (plant : FiniteLaw (Finset E)) (S : Finset E) : ℝ :=
  plant.prob (Finset.univ.filter fun A : Finset E ↦ S ⊆ A)

theorem randomPlantContainmentProbability_nonneg
    (plant : FiniteLaw (Finset E)) (S : Finset E) :
    0 ≤ randomPlantContainmentProbability plant S := by
  unfold randomPlantContainmentProbability FiniteLaw.prob
  exact Finset.sum_nonneg fun A _ ↦ plant.mass_nonneg A

/-- Exact Fourier coefficient of a random forced-set mixture. -/
theorem fourierCoeff_randomForcedLikelihood
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (S : Finset E) :
    fourierCoeff θ (randomForcedLikelihood θ plant) S =
      randomPlantContainmentProbability plant S * θ.forcedWeight ^ S.card := by
  have hlinear := bernoulliInner_finset_sum_left
    (E := E) θ (Finset.univ : Finset (Finset E)) plant.mass
      (forcedLikelihood θ) (fourierCharacter θ S)
  change fourierCoeff θ (randomForcedLikelihood θ plant) S = _
  rw [show fourierCoeff θ (randomForcedLikelihood θ plant) S =
      ∑ A : Finset E, plant.mass A *
        fourierCoeff θ (forcedLikelihood θ A) S by
      simpa only [randomForcedLikelihood, fourierCoeff] using hlinear]
  simp_rw [fourierCoeff_forcedLikelihood]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  unfold randomPlantContainmentProbability FiniteLaw.prob
  rw [Finset.sum_mul]

/-- Every random forced-set mixture is normalized under the null law. -/
theorem bernoulliExpectation_randomForcedLikelihood
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E)) :
    bernoulliExpectation θ (randomForcedLikelihood θ plant) = 1 := by
  rw [← fourierCoeff_empty, fourierCoeff_randomForcedLikelihood]
  simp [randomPlantContainmentProbability, FiniteLaw.prob, plant.sum_mass]

/-- The observation law generated by a random forced edge set. -/
noncomputable def randomForcedLaw
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E)) :
    FiniteLaw (BooleanConfiguration E) where
  mass x := bernoulliProductMass θ x * randomForcedLikelihood θ plant x
  mass_nonneg x := mul_nonneg (bernoulliProductMass_nonneg θ x)
    (randomForcedLikelihood_nonneg θ plant x)
  sum_mass := by
    simpa only [bernoulliExpectation] using
      bernoulliExpectation_randomForcedLikelihood θ plant

@[simp]
theorem randomForcedLaw_mass
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (x : BooleanConfiguration E) :
    (randomForcedLaw θ plant).mass x =
      (bernoulliProductLaw θ).mass x * randomForcedLikelihood θ plant x :=
  rfl

theorem randomForcedLikelihood_isLikelihoodRatio
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E)) :
    FiniteLaw.IsLikelihoodRatio (randomForcedLaw θ plant)
      (bernoulliProductLaw θ) (randomForcedLikelihood θ plant) := by
  intro x
  rfl

end Mixture

section HereditaryTruncation

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Replace a sampled plant by the empty set when it fails `good`.  This is
the exact all-or-nothing truncation used for forests in Theorem 1.2. -/
noncomputable def truncatePlantSet (good : Finset E → Prop) (A : Finset E) : Finset E :=
  if good A then A else ∅

/-- Pushforward distribution of the all-or-nothing truncation. -/
noncomputable def truncatePlantLaw
    (plant : FiniteLaw (Finset E)) (good : Finset E → Prop) :
    FiniteLaw (Finset E) :=
  plant.map (truncatePlantSet good)

theorem truncatePlantSet_subset (good : Finset E → Prop) (A : Finset E) :
    truncatePlantSet good A ⊆ A := by
  unfold truncatePlantSet
  split <;> simp_all

theorem truncatePlantSet_good
    (good : Finset E → Prop) (hempty : good ∅) (A : Finset E) :
    good (truncatePlantSet good A) := by
  unfold truncatePlantSet
  split <;> simp_all

/-- Truncation can only decrease every containment probability. -/
theorem randomPlantContainmentProbability_truncate_le
    (plant : FiniteLaw (Finset E)) (good : Finset E → Prop) (S : Finset E) :
    randomPlantContainmentProbability (truncatePlantLaw plant good) S ≤
      randomPlantContainmentProbability plant S := by
  classical
  unfold randomPlantContainmentProbability truncatePlantLaw
  rw [FiniteLaw.prob_map]
  apply FiniteLaw.prob_mono
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  exact hA.trans (truncatePlantSet_subset good A)

/-- If `good` is hereditary, no truncated sample can contain a bad support. -/
theorem randomPlantContainmentProbability_truncate_eq_zero_of_not_good
    (plant : FiniteLaw (Finset E)) (good : Finset E → Prop)
    (hempty : good ∅)
    (hhereditary : ∀ {A B : Finset E}, A ⊆ B → good B → good A)
    (S : Finset E) (hSbad : ¬good S) :
    randomPlantContainmentProbability (truncatePlantLaw plant good) S = 0 := by
  classical
  unfold randomPlantContainmentProbability truncatePlantLaw
  rw [FiniteLaw.prob_map]
  unfold FiniteLaw.prob
  apply Finset.sum_eq_zero
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
  exfalso
  exact hSbad
    (hhereditary hA (truncatePlantSet_good good hempty A))

/-- Fourier domination under hereditary all-or-nothing truncation. -/
theorem fourierCoeff_truncated_randomForcedLikelihood_le
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (good : Finset E → Prop) (S : Finset E) :
    fourierCoeff θ
        (randomForcedLikelihood θ (truncatePlantLaw plant good)) S ≤
      fourierCoeff θ (randomForcedLikelihood θ plant) S := by
  rw [fourierCoeff_randomForcedLikelihood,
    fourierCoeff_randomForcedLikelihood]
  exact mul_le_mul_of_nonneg_right
    (randomPlantContainmentProbability_truncate_le plant good S)
    (pow_nonneg θ.forcedWeight_pos.le _)

/-- Fourier coefficients of bad supports vanish after hereditary truncation. -/
theorem fourierCoeff_truncated_randomForcedLikelihood_eq_zero_of_not_good
    (θ : BernoulliParameter) (plant : FiniteLaw (Finset E))
    (good : Finset E → Prop) (hempty : good ∅)
    (hhereditary : ∀ {A B : Finset E}, A ⊆ B → good B → good A)
    (S : Finset E) (hSbad : ¬good S) :
    fourierCoeff θ
        (randomForcedLikelihood θ (truncatePlantLaw plant good)) S = 0 := by
  rw [fourierCoeff_randomForcedLikelihood,
    randomPlantContainmentProbability_truncate_eq_zero_of_not_good
      plant good hempty hhereditary S hSbad,
    zero_mul]

end HereditaryTruncation

end

end LowDegree
