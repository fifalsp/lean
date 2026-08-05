import LowDegree.PlantedModel

/-!
# Deleting planted edges before superposition

For a fixed forced edge set `A`, independently retain each edge with
probability `1 - ε`, and then force only the retained subset `R`.  This file
defines the resulting subset-mixture likelihood and proves, pointwise, that it
is exactly the edge-noise operator applied to the original forcing likelihood.

Averaging the fixed-set identity over ambient permutations shows that deleting
the planted graph before superposition has exactly the same likelihood, and
hence the same finite law, as resampling all edges after superposition.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

private theorem sum_prod_configuration_deleted
    {E : Type*} [Fintype E] [DecidableEq E] (g : E → Bool → ℝ) :
    ∑ x : BooleanConfiguration E, ∏ e, g e (x e) =
      ∏ e, ∑ b : Bool, g e b := by
  simpa using (Fintype.prod_sum g).symm

/-- The probability weight of retaining exactly `R` from the forced set `A`.
For `R ⊆ A`, this is `(1-ε)^|R| ε^(|A|-|R|)`. -/
def deletionWeight (ε : ℝ) (A R : Finset E) : ℝ :=
  (1 - ε) ^ R.card * ε ^ (A.card - R.card)

/-- The fixed-plant likelihood after independently deleting each planted edge
with probability `ε` before superposition. -/
def deletedForcedLikelihood (θ : BernoulliParameter) (ε : ℝ)
    (A : Finset E) (x : BooleanConfiguration E) : ℝ :=
  ∑ R ∈ A.powerset, deletionWeight ε A R * forcedLikelihood θ R x

/-- The independent-deletion weights on the powerset of `A` sum to one. -/
theorem sum_deletionWeight (ε : ℝ) (A : Finset E) :
    ∑ R ∈ A.powerset, deletionWeight ε A R = 1 := by
  classical
  have h := Finset.prod_add (fun _ : E ↦ (1 - ε : ℝ)) (fun _ ↦ ε) A
  rw [show (∏ _ ∈ A, ((1 - ε) + ε : ℝ)) = 1 by simp] at h
  calc
    (∑ R ∈ A.powerset, deletionWeight ε A R) =
        ∑ R ∈ A.powerset,
          (∏ _ ∈ R, (1 - ε : ℝ)) * ∏ _ ∈ A \ R, ε := by
            apply Finset.sum_congr rfl
            intro R hR
            have hRA : R ⊆ A := Finset.mem_powerset.mp hR
            simp only [deletionWeight, Finset.prod_const,
              Finset.card_sdiff_of_subset hRA]
    _ = 1 := h.symm

/-- Deletion weights are nonnegative at a valid deletion rate. -/
theorem deletionWeight_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A R : Finset E) :
    0 ≤ deletionWeight ε A R := by
  exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hε1) _)
    (pow_nonneg hε0 _)

/-- The subset mixture factors into one independent contribution per planted
edge. -/
theorem deletedForcedLikelihood_eq_prod (θ : BernoulliParameter) (ε : ℝ)
    (A : Finset E) (x : BooleanConfiguration E) :
    deletedForcedLikelihood θ ε A x =
      ∏ e ∈ A, ((1 - ε) * (BernoulliParameter.bitValue (x e) / θ.p) + ε) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro R hR
  have hRA : R ⊆ A := Finset.mem_powerset.mp hR
  simp only [deletionWeight, forcedLikelihood]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset hRA]
  ring

/-- Resampling one forced-bit likelihood gives the convex combination of its
old value and one. -/
theorem sum_bitNoiseMass_mul_forcedBit (θ : BernoulliParameter) (ε : ℝ)
    (a : Bool) :
    ∑ b : Bool, θ.bitNoiseMass ε a b *
        (BernoulliParameter.bitValue b / θ.p) =
      (1 - ε) * (BernoulliParameter.bitValue a / θ.p) + ε := by
  calc
    (∑ b : Bool, θ.bitNoiseMass ε a b *
        (BernoulliParameter.bitValue b / θ.p)) =
        ∑ b : Bool, θ.bitNoiseMass ε a b *
          (1 + θ.forcedWeight * θ.oneCharacter b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [θ.bitValue_div_p_eq_one_add]
    _ = (∑ b : Bool, θ.bitNoiseMass ε a b) +
        θ.forcedWeight *
          ∑ b : Bool, θ.bitNoiseMass ε a b * θ.oneCharacter b := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = 1 + θ.forcedWeight * ((1 - ε) * θ.oneCharacter a) := by
      rw [θ.sum_bitNoiseMass, θ.sum_bitNoiseMass_mul_oneCharacter]
    _ = (1 - ε) * (BernoulliParameter.bitValue a / θ.p) + ε := by
      rw [θ.bitValue_div_p_eq_one_add]
      ring

/-- The edge-noise image of a fixed forcing likelihood has the same product
formula as independent deletion before superposition. -/
theorem edgeNoise_forcedLikelihood_eq_prod
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : ℝ)
    (A : Finset E) (x : BooleanConfiguration E) :
    edgeNoise θ ε (forcedLikelihood θ A) x =
      ∏ e ∈ A, ((1 - ε) * (BernoulliParameter.bitValue (x e) / θ.p) + ε) := by
  classical
  unfold edgeNoise bernoulliNoiseTransition forcedLikelihood
  calc
    (∑ y : BooleanConfiguration E,
        (∏ e, θ.bitNoiseMass ε (x e) (y e)) *
          ∏ e ∈ A, BernoulliParameter.bitValue (y e) / θ.p) =
        ∑ y : BooleanConfiguration E, ∏ e,
          θ.bitNoiseMass ε (x e) (y e) *
            (if e ∈ A then BernoulliParameter.bitValue (y e) / θ.p else 1) := by
              apply Finset.sum_congr rfl
              intro y _
              have hpart :
                  (∏ e ∈ A, BernoulliParameter.bitValue (y e) / θ.p) =
                    ∏ e : E, (if e ∈ A then
                      BernoulliParameter.bitValue (y e) / θ.p else 1) := by
                rw [Finset.prod_ite_mem]
                simp
              rw [hpart, ← Finset.prod_mul_distrib]
    _ = ∏ e ∈ A,
        ((1 - ε) * (BernoulliParameter.bitValue (x e) / θ.p) + ε) := by
      let g : E → Bool → ℝ := fun e b ↦
        θ.bitNoiseMass ε (x e) b *
          (if e ∈ A then BernoulliParameter.bitValue b / θ.p else 1)
      change (∑ y : BooleanConfiguration E, ∏ e, g e (y e)) = _
      rw [sum_prod_configuration_deleted]
      calc
        (∏ e : E, ∑ b : Bool, g e b) =
            ∏ e : E, (if e ∈ A then
              (1 - ε) * (BernoulliParameter.bitValue (x e) / θ.p) + ε else 1) := by
                apply Finset.prod_congr rfl
                intro e _
                by_cases he : e ∈ A
                · simpa [g, he] using sum_bitNoiseMass_mul_forcedBit θ ε (x e)
                · simpa [g, he] using θ.sum_bitNoiseMass ε (x e)
        _ = ∏ e ∈ A,
            ((1 - ε) * (BernoulliParameter.bitValue (x e) / θ.p) + ε) := by
          rw [Finset.prod_ite_mem]
          simp

/-- Fixed-set deletion before forcing is exactly edge noise after forcing. -/
theorem deletedForcedLikelihood_eq_edgeNoise
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : ℝ)
    (A : Finset E) :
    deletedForcedLikelihood θ ε A = edgeNoise θ ε (forcedLikelihood θ A) := by
  funext x
  rw [deletedForcedLikelihood_eq_prod, edgeNoise_forcedLikelihood_eq_prod]

/-- The fixed-set deletion mixture is nonnegative at a valid deletion rate. -/
theorem deletedForcedLikelihood_nonneg
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Finset E) (x : BooleanConfiguration E) :
    0 ≤ deletedForcedLikelihood θ ε A x := by
  classical
  unfold deletedForcedLikelihood
  exact Finset.sum_nonneg fun R _ ↦
    mul_nonneg (deletionWeight_nonneg hε0 hε1 A R)
      (forcedLikelihood_nonneg θ R x)

/-- The fixed-set deletion mixture is normalized under the null law. -/
theorem bernoulliExpectation_deletedForcedLikelihood
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : ℝ) (A : Finset E) :
    bernoulliExpectation θ (deletedForcedLikelihood θ ε A) = 1 := by
  rw [deletedForcedLikelihood_eq_edgeNoise,
    bernoulliExpectation_edgeNoise,
    bernoulliExpectation_forcedLikelihood]

/-- Average the independently deleted fixed-plant likelihood over a uniform
ambient permutation. -/
noncomputable def deletedPlantedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
    deletedForcedLikelihood θ (ε : ℝ) (permutedPlantEdges plant σ) x

/-- The permutation-averaged deletion likelihood is nonnegative. -/
theorem deletedPlantedLikelihood_nonneg {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    0 ≤ deletedPlantedLikelihood θ ε plant x := by
  classical
  unfold deletedPlantedLikelihood
  exact Finset.sum_nonneg fun σ _ ↦
    mul_nonneg (uniformPermutationWeight_pos n).le
      (deletedForcedLikelihood_nonneg θ ε.2.1.le ε.2.2.le
        (permutedPlantEdges plant σ) x)

/-- Deletion before superposition and edge noise after superposition have the
same permutation-averaged likelihood. -/
theorem deletedPlantedLikelihood_eq_noisedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    deletedPlantedLikelihood θ ε plant = noisedLikelihood θ ε plant := by
  classical
  funext x
  simp only [deletedPlantedLikelihood, noisedLikelihood, plantedLikelihood,
    deletedForcedLikelihood_eq_edgeNoise, edgeNoise]
  calc
    (∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
        ∑ y, bernoulliNoiseTransition θ (ε : ℝ) x y *
          forcedLikelihood θ (permutedPlantEdges plant σ) y) =
        ∑ σ : Equiv.Perm (Fin n), ∑ y,
          uniformPermutationWeight n *
            (bernoulliNoiseTransition θ (ε : ℝ) x y *
              forcedLikelihood θ (permutedPlantEdges plant σ) y) := by
                apply Finset.sum_congr rfl
                intro σ _
                rw [Finset.mul_sum]
    _ = ∑ y, ∑ σ : Equiv.Perm (Fin n),
          uniformPermutationWeight n *
            (bernoulliNoiseTransition θ (ε : ℝ) x y *
              forcedLikelihood θ (permutedPlantEdges plant σ) y) := by
                rw [Finset.sum_comm]
    _ = ∑ y, bernoulliNoiseTransition θ (ε : ℝ) x y *
          ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
            forcedLikelihood θ (permutedPlantEdges plant σ) y := by
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro σ _
              ring

/-- The permutation-averaged deletion likelihood has null expectation one. -/
theorem bernoulliExpectation_deletedPlantedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    bernoulliExpectation θ (deletedPlantedLikelihood θ ε plant) = 1 := by
  rw [deletedPlantedLikelihood_eq_noisedLikelihood,
    bernoulliExpectation_noisedLikelihood]

/-- The law obtained by first independently deleting planted edges and then
superposing the retained plant on the Erdős--Rényi graph. -/
noncomputable def deletedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) where
  mass x := bernoulliProductMass θ x * deletedPlantedLikelihood θ ε plant x
  mass_nonneg x := mul_nonneg (bernoulliProductMass_nonneg θ x)
    (deletedPlantedLikelihood_nonneg θ ε plant x)
  sum_mass := by
    simpa only [bernoulliExpectation] using
      bernoulliExpectation_deletedPlantedLikelihood θ ε plant

@[simp]
theorem deletedPlantedLaw_mass {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    (deletedPlantedLaw θ ε plant).mass x =
      (erdosRenyiLaw θ).mass x * deletedPlantedLikelihood θ ε plant x :=
  rfl

/-- The deletion-mixture density is the likelihood ratio of its finite law. -/
theorem deletedPlantedLikelihood_isLikelihoodRatio {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    FiniteLaw.IsLikelihoodRatio (deletedPlantedLaw θ ε plant)
      (erdosRenyiLaw θ) (deletedPlantedLikelihood θ ε plant) := by
  intro x
  rfl

/-- Deletion before superposition and edge noise after superposition define
the same finite planted law. -/
theorem deletedPlantedLaw_eq_noisedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    deletedPlantedLaw θ ε plant = noisedPlantedLaw θ ε plant := by
  apply FiniteLaw.ext_mass
  funext x
  simp only [deletedPlantedLaw_mass, noisedPlantedLaw_mass,
    deletedPlantedLikelihood_eq_noisedLikelihood]

end

end LowDegree
