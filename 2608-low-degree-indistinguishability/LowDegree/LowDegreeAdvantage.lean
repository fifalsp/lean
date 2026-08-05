import LowDegree.Fourier
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The low-degree variational identity

This file formalizes equation (1.1) of the paper on a finite Bernoulli cube.
The alternative law is represented by a normalized likelihood ratio `L` with
respect to the null product law.  The theorem identifies the squared norm of
the nonconstant part of the degree-`D` projection of `L` with the supremum of
the squared, variance-normalized distinguishing bias over all degree-`D`
statistics.

Because the cube is finite, the proof is elementary finite-dimensional
Fourier analysis.  Cauchy--Schwarz gives the upper bound, and the centered
low-degree likelihood projection is an explicit optimizer whenever the
common value is positive.
-/

namespace LowDegree

open scoped BigOperators

section Cube

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Variance under the Bernoulli product law. -/
noncomputable def bernoulliVariance (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) : ℝ :=
  bernoulliExpectation θ fun x ↦ (f x - bernoulliExpectation θ f) ^ 2

/-- A function has Fourier degree at most `D` when every coefficient above
degree `D` vanishes. -/
def FourierDegreeLE (θ : BernoulliParameter) (D : ℕ)
    (f : BooleanConfiguration E → ℝ) : Prop :=
  ∀ S : Finset E, D < S.card → fourierCoeff θ f S = 0

/-- The squared distinguishing bias of `f`, normalized by its null variance.
Here `bernoulliInner θ L f` is the expectation of `f` under the alternative
whose likelihood ratio relative to the null is `L`. -/
noncomputable def lowDegreeAdvantageRatio (θ : BernoulliParameter)
    (L f : BooleanConfiguration E → ℝ) : ℝ :=
  (bernoulliInner θ L f - bernoulliExpectation θ f) ^ 2 /
    bernoulliVariance θ f

/-- The set of ratios attained by nonconstant degree-at-most-`D` statistics. -/
noncomputable def lowDegreeAdvantageValues (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) : Set ℝ :=
  {a | ∃ f : BooleanConfiguration E → ℝ,
      FourierDegreeLE θ D f ∧
      0 < bernoulliVariance θ f ∧
      a = lowDegreeAdvantageRatio θ L f}

/-- The nonconstant part of the low-degree likelihood projection. -/
noncomputable def centeredLowDegreeLikelihood (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) : BooleanConfiguration E → ℝ :=
  fun x ↦ lowDegreeProjection θ D L x - 1

private theorem sum_eq_empty_add_sum_nonempty (a : Finset E → ℝ) :
    ∑ S : Finset E, a S =
      a ∅ + ∑ S : Finset E with S.Nonempty, a S := by
  classical
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (∅ : Finset E))]
  congr 1
  apply Finset.sum_congr
  · ext S
    simp [Finset.nonempty_iff_ne_empty]
  · intro S _
    rfl

private theorem sum_card_le_eq_empty_add_sum_card_le_nonempty (D : ℕ)
    (a : Finset E → ℝ) :
    ∑ S : Finset E with S.card ≤ D, a S =
      a ∅ + ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty, a S := by
  classical
  rw [Finset.sum_eq_add_sum_diff_singleton
    (show (∅ : Finset E) ∈
      (Finset.univ.filter fun S : Finset E ↦ S.card ≤ D) by simp)]
  congr 1
  apply Finset.sum_congr
  · ext S
    simp [Finset.nonempty_iff_ne_empty]
  · intro S _
    rfl

omit [DecidableEq E] in
private theorem sum_nonempty_eq_sum_card_le_nonempty_of_high_eq_zero
    (D : ℕ) (a : Finset E → ℝ)
    (ha : ∀ S : Finset E, D < S.card → a S = 0) :
    ∑ S : Finset E with S.Nonempty, a S =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty, a S := by
  classical
  symm
  apply Finset.sum_subset
  · intro S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · intro S hS hSnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hSnot
    apply ha S
    exact Nat.lt_of_not_ge fun hcard ↦ hSnot ⟨hcard, hS⟩

theorem fourierCoeff_sub (θ : BernoulliParameter)
    (f g : BooleanConfiguration E → ℝ) (S : Finset E) :
    fourierCoeff θ (fun x ↦ f x - g x) S =
      fourierCoeff θ f S - fourierCoeff θ g S := by
  unfold fourierCoeff bernoulliInner bernoulliExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp]
theorem fourierCoeff_const (θ : BernoulliParameter) (c : ℝ) (S : Finset E) :
    fourierCoeff θ (fun _ : BooleanConfiguration E ↦ c) S =
      if S = ∅ then c else 0 := by
  calc
    fourierCoeff θ (fun _ : BooleanConfiguration E ↦ c) S =
        c * bernoulliInner θ (fourierCharacter θ ∅) (fourierCharacter θ S) := by
          unfold fourierCoeff bernoulliInner bernoulliExpectation
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          simp [fourierCharacter_empty]
          ring
    _ = if S = ∅ then c else 0 := by
      rw [fourierCharacters_orthonormal]
      by_cases hS : S = ∅ <;> simp [hS, eq_comm]

@[simp]
theorem fourierCoeff_centered (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) (S : Finset E) :
    fourierCoeff θ (fun x ↦ f x - bernoulliExpectation θ f) S =
      if S = ∅ then 0 else fourierCoeff θ f S := by
  rw [fourierCoeff_sub, fourierCoeff_const]
  by_cases hS : S = ∅
  · subst S
    simp
  · simp [hS]

/-- Variance is the Fourier mass on the nonempty subsets. -/
theorem bernoulliVariance_eq_sum_nonempty_fourierCoeff_sq
    (θ : BernoulliParameter) (f : BooleanConfiguration E → ℝ) :
    bernoulliVariance θ f =
      ∑ S : Finset E with S.Nonempty, (fourierCoeff θ f S) ^ 2 := by
  let f₀ : BooleanConfiguration E → ℝ :=
    fun x ↦ f x - bernoulliExpectation θ f
  calc
    bernoulliVariance θ f = bernoulliInner θ f₀ f₀ := by
      simp only [bernoulliVariance, bernoulliInner, f₀, pow_two]
    _ = ∑ S : Finset E, (fourierCoeff θ f₀ S) ^ 2 :=
      fourierParseval_sq θ f₀
    _ = ∑ S : Finset E,
        if S.Nonempty then (fourierCoeff θ f S) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [fourierCoeff_centered]
      by_cases hS : S = ∅
      · subst S
        simp
      · simp [hS, Finset.nonempty_iff_ne_empty]
    _ = ∑ S : Finset E with S.Nonempty, (fourierCoeff θ f S) ^ 2 := by
      rw [Finset.sum_ite]
      simp

/-- Under the normalization `𝔼_Q[L] = 1`, the alternative-minus-null bias
is the Fourier pairing over the nonconstant characters. -/
theorem likelihoodBias_eq_sum_nonempty_fourierCoeff
    (θ : BernoulliParameter) (L f : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliInner θ L f - bernoulliExpectation θ f =
      ∑ S : Finset E with S.Nonempty,
        fourierCoeff θ L S * fourierCoeff θ f S := by
  rw [fourierParseval, sum_eq_empty_add_sum_nonempty]
  simp [hL]

/-- A low-degree statistic has no contribution from subsets of cardinality
greater than `D` in the Fourier expression for its variance. -/
theorem bernoulliVariance_eq_sum_lowDegree_fourierCoeff_sq
    (θ : BernoulliParameter) (D : ℕ)
    (f : BooleanConfiguration E → ℝ) (hf : FourierDegreeLE θ D f) :
    bernoulliVariance θ f =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        (fourierCoeff θ f S) ^ 2 := by
  rw [bernoulliVariance_eq_sum_nonempty_fourierCoeff_sq]
  apply sum_nonempty_eq_sum_card_le_nonempty_of_high_eq_zero D
  intro S hS
  rw [hf S hS]
  simp

/-- For a low-degree statistic, the alternative-minus-null bias is its
finite Fourier pairing with the low-degree nonconstant part of `L`. -/
theorem likelihoodBias_eq_sum_lowDegree_fourierCoeff
    (θ : BernoulliParameter) (D : ℕ)
    (L f : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) (hf : FourierDegreeLE θ D f) :
    bernoulliInner θ L f - bernoulliExpectation θ f =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        fourierCoeff θ L S * fourierCoeff θ f S := by
  rw [likelihoodBias_eq_sum_nonempty_fourierCoeff θ L f hL]
  apply sum_nonempty_eq_sum_card_le_nonempty_of_high_eq_zero D
  intro S hS
  rw [hf S hS]
  simp

/-- The squared norm of the low-degree likelihood projection, minus its
constant normalized coefficient, is precisely its nonconstant Fourier mass. -/
theorem lowDegreeProjection_excess_eq_sum_fourierCoeff_sq
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        (fourierCoeff θ L S) ^ 2 := by
  rw [lowDegreeProjection_norm_sq,
    sum_card_le_eq_empty_add_sum_card_le_nonempty]
  simp [hL]

/-- The projected likelihood excess is nonnegative. -/
theorem lowDegreeProjection_excess_nonneg
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    0 ≤ bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
  rw [lowDegreeProjection_excess_eq_sum_fourierCoeff_sq θ D L hL]
  exact Finset.sum_nonneg fun S _ ↦ sq_nonneg (fourierCoeff θ L S)

/-- Every admissible squared-bias ratio is nonnegative. -/
theorem lowDegreeAdvantageRatio_nonneg
    (θ : BernoulliParameter) (L f : BooleanConfiguration E → ℝ)
    (hf : 0 < bernoulliVariance θ f) :
    0 ≤ lowDegreeAdvantageRatio θ L f := by
  unfold lowDegreeAdvantageRatio
  exact div_nonneg (sq_nonneg _) hf.le

/-- Finite-dimensional Cauchy--Schwarz gives the variational upper bound. -/
theorem lowDegreeAdvantageRatio_le_projection_excess
    (θ : BernoulliParameter) (D : ℕ)
    (L f : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1)
    (hfdeg : FourierDegreeLE θ D f)
    (hfvar : 0 < bernoulliVariance θ f) :
    lowDegreeAdvantageRatio θ L f ≤
      bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
  classical
  let s : Finset (Finset E) :=
    Finset.univ.filter fun S : Finset E ↦ S.card ≤ D ∧ S.Nonempty
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fourierCoeff θ L) (fourierCoeff θ f)
  have hcs' :
      (∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
          fourierCoeff θ L S * fourierCoeff θ f S) ^ 2 ≤
        (∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
          (fourierCoeff θ L S) ^ 2) *
        ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
          (fourierCoeff θ f S) ^ 2 := by
    simpa [s] using hcs
  unfold lowDegreeAdvantageRatio
  apply (div_le_iff₀ hfvar).2
  rw [likelihoodBias_eq_sum_lowDegree_fourierCoeff θ D L f hL hfdeg,
    bernoulliVariance_eq_sum_lowDegree_fourierCoeff_sq θ D f hfdeg,
    lowDegreeProjection_excess_eq_sum_fourierCoeff_sq θ D L hL]
  exact hcs'

/-- On every nonconstant Fourier character, the centered low-degree
likelihood has the corresponding coefficient of `L` below the cutoff and
zero above it. -/
theorem fourierCoeff_centeredLowDegreeLikelihood_of_nonempty
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) (S : Finset E) (hS : S.Nonempty) :
    fourierCoeff θ (centeredLowDegreeLikelihood θ D L) S =
      if S.card ≤ D then fourierCoeff θ L S else 0 := by
  have hSne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hS
  unfold centeredLowDegreeLikelihood
  rw [fourierCoeff_sub, fourierCoeff_lowDegreeProjection, fourierCoeff_const]
  simp [hSne]

/-- The centered low-degree likelihood is itself degree at most `D`. -/
theorem centeredLowDegreeLikelihood_degreeLE
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) :
    FourierDegreeLE θ D (centeredLowDegreeLikelihood θ D L) := by
  intro S hS
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    subst S
    simp at hS
  rw [fourierCoeff_centeredLowDegreeLikelihood_of_nonempty θ D L S hSnonempty]
  simp [Nat.not_le_of_lt hS]

/-- Normalization makes the centered low-degree likelihood have null mean
zero. -/
theorem bernoulliExpectation_centeredLowDegreeLikelihood
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliExpectation θ (centeredLowDegreeLikelihood θ D L) = 0 := by
  rw [← fourierCoeff_empty]
  unfold centeredLowDegreeLikelihood
  rw [fourierCoeff_sub, fourierCoeff_lowDegreeProjection, fourierCoeff_const]
  simp [hL]

/-- The variance of the explicit optimizer is exactly the low-degree
nonconstant Fourier mass of the likelihood ratio. -/
theorem bernoulliVariance_centeredLowDegreeLikelihood
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) :
    bernoulliVariance θ (centeredLowDegreeLikelihood θ D L) =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        (fourierCoeff θ L S) ^ 2 := by
  rw [bernoulliVariance_eq_sum_lowDegree_fourierCoeff_sq θ D _
    (centeredLowDegreeLikelihood_degreeLE θ D L)]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [fourierCoeff_centeredLowDegreeLikelihood_of_nonempty θ D L S hS.2]
  simp [hS.1]

/-- The alternative-minus-null bias of the explicit optimizer is the same
low-degree nonconstant Fourier mass. -/
theorem likelihoodBias_centeredLowDegreeLikelihood
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliInner θ L (centeredLowDegreeLikelihood θ D L) -
        bernoulliExpectation θ (centeredLowDegreeLikelihood θ D L) =
      ∑ S : Finset E with S.card ≤ D ∧ S.Nonempty,
        (fourierCoeff θ L S) ^ 2 := by
  rw [likelihoodBias_eq_sum_lowDegree_fourierCoeff θ D L _ hL
    (centeredLowDegreeLikelihood_degreeLE θ D L)]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [fourierCoeff_centeredLowDegreeLikelihood_of_nonempty θ D L S hS.2]
  simp [hS.1, pow_two]

/-- The explicit optimizer's variance equals the projected likelihood
excess appearing on the left side of equation (1.1). -/
theorem bernoulliVariance_centeredLowDegreeLikelihood_eq_projection_excess
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliVariance θ (centeredLowDegreeLikelihood θ D L) =
      bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
  rw [bernoulliVariance_centeredLowDegreeLikelihood,
    lowDegreeProjection_excess_eq_sum_fourierCoeff_sq θ D L hL]

/-- The explicit optimizer's bias also equals the projected likelihood
excess. -/
theorem likelihoodBias_centeredLowDegreeLikelihood_eq_projection_excess
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliInner θ L (centeredLowDegreeLikelihood θ D L) -
        bernoulliExpectation θ (centeredLowDegreeLikelihood θ D L) =
      bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
  rw [likelihoodBias_centeredLowDegreeLikelihood θ D L hL,
    lowDegreeProjection_excess_eq_sum_fourierCoeff_sq θ D L hL]

/-- Whenever the projected likelihood has nonzero nonconstant low-degree
mass, its centered projection attains the Cauchy--Schwarz upper bound. -/
theorem lowDegreeAdvantageRatio_centeredLowDegreeLikelihood
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1)
    (hpos : 0 < bernoulliInner θ (lowDegreeProjection θ D L)
      (lowDegreeProjection θ D L) - 1) :
    lowDegreeAdvantageRatio θ L (centeredLowDegreeLikelihood θ D L) =
      bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
  unfold lowDegreeAdvantageRatio
  rw [likelihoodBias_centeredLowDegreeLikelihood_eq_projection_excess θ D L hL,
    bernoulliVariance_centeredLowDegreeLikelihood_eq_projection_excess θ D L hL]
  field_simp [ne_of_gt hpos]

/-- Every value in the degree-`D` variational family is nonnegative. -/
theorem lowDegreeAdvantageValues_nonneg
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ) {a : ℝ}
    (ha : a ∈ lowDegreeAdvantageValues θ D L) : 0 ≤ a := by
  rcases ha with ⟨f, _hfdeg, hfvar, rfl⟩
  exact lowDegreeAdvantageRatio_nonneg θ L f hfvar

/-- The projected likelihood excess is an upper bound for the full
degree-`D` variational family. -/
theorem lowDegreeAdvantageValues_bddAbove
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    BddAbove (lowDegreeAdvantageValues θ D L) := by
  refine ⟨bernoulliInner θ (lowDegreeProjection θ D L)
    (lowDegreeProjection θ D L) - 1, ?_⟩
  intro a ha
  rcases ha with ⟨f, hfdeg, hfvar, rfl⟩
  exact lowDegreeAdvantageRatio_le_projection_excess θ D L f hL hfdeg hfvar

/-- Equation (1.1): the squared norm of the degree-`D` likelihood
projection, minus its constant coefficient, is the supremum of the squared
alternative-minus-null bias divided by null variance over all nonconstant
degree-at-most-`D` statistics.

The assumption `bernoulliExpectation θ L = 1` is precisely the normalization
of `L` as a likelihood ratio relative to the Bernoulli product null law. -/
theorem lowDegree_advantage_identity
    (θ : BernoulliParameter) (D : ℕ)
    (L : BooleanConfiguration E → ℝ)
    (hL : bernoulliExpectation θ L = 1) :
    bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 =
      sSup (lowDegreeAdvantageValues θ D L) := by
  let A : ℝ := bernoulliInner θ (lowDegreeProjection θ D L)
    (lowDegreeProjection θ D L) - 1
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    exact lowDegreeProjection_excess_nonneg θ D L hL
  have hupper : ∀ a ∈ lowDegreeAdvantageValues θ D L, a ≤ A := by
    intro a ha
    rcases ha with ⟨f, hfdeg, hfvar, rfl⟩
    dsimp only [A]
    exact lowDegreeAdvantageRatio_le_projection_excess θ D L f hL hfdeg hfvar
  have hbdd : BddAbove (lowDegreeAdvantageValues θ D L) := ⟨A, hupper⟩
  change A = sSup (lowDegreeAdvantageValues θ D L)
  by_cases hApos : 0 < A
  · have hApos' : 0 < bernoulliInner θ (lowDegreeProjection θ D L)
        (lowDegreeProjection θ D L) - 1 := by
      simpa only [A] using hApos
    have hvar : 0 < bernoulliVariance θ
        (centeredLowDegreeLikelihood θ D L) := by
      rw [bernoulliVariance_centeredLowDegreeLikelihood_eq_projection_excess
        θ D L hL]
      exact hApos'
    have hratio :
        lowDegreeAdvantageRatio θ L (centeredLowDegreeLikelihood θ D L) = A := by
      simpa only [A] using
        lowDegreeAdvantageRatio_centeredLowDegreeLikelihood θ D L hL hApos'
    have hA_mem : A ∈ lowDegreeAdvantageValues θ D L := by
      refine ⟨centeredLowDegreeLikelihood θ D L,
        centeredLowDegreeLikelihood_degreeLE θ D L, hvar, ?_⟩
      exact hratio.symm
    apply le_antisymm
    · exact le_csSup hbdd hA_mem
    · exact csSup_le ⟨A, hA_mem⟩ hupper
  · have hAzero : A = 0 :=
      le_antisymm (le_of_not_gt hApos) hAnonneg
    by_cases hvalues : (lowDegreeAdvantageValues θ D L).Nonempty
    · apply le_antisymm
      · rw [hAzero]
        obtain ⟨a, ha⟩ := hvalues
        exact (lowDegreeAdvantageValues_nonneg θ D L ha).trans
          (le_csSup hbdd ha)
      · exact csSup_le hvalues hupper
    · have hempty : lowDegreeAdvantageValues θ D L = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hvalues
      rw [hempty, Real.sSup_empty, hAzero]

end Cube

end LowDegree
