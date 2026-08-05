import LowDegree.Probability.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Sqrt

/-!
# Bernoulli Fourier analysis on a finite Boolean cube

This file develops the finite-coordinate Fourier kernel used for the
`G(n,p)` calculations in the paper.  Everything is an explicit finite sum
or product.  In particular, no measure-theoretic convention is hidden in
the definitions of expectation, Fourier coefficient, or edge noise.
-/

namespace LowDegree

open scoped BigOperators

/-- A Boolean configuration on a finite coordinate type. -/
abbrev BooleanConfiguration (E : Type*) := E → Bool

/-- A Bernoulli parameter strictly inside the probability interval. -/
structure BernoulliParameter where
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1

namespace BernoulliParameter

/-- The variance `p(1-p)` of one Bernoulli coordinate. -/
def variance (θ : BernoulliParameter) : ℝ := θ.p * (1 - θ.p)

/-- The positive normalization `sqrt (p(1-p))`. -/
noncomputable def sigma (θ : BernoulliParameter) : ℝ := Real.sqrt θ.variance

theorem one_sub_p_pos (θ : BernoulliParameter) : 0 < 1 - θ.p := sub_pos.mpr θ.p_lt_one

theorem variance_pos (θ : BernoulliParameter) : 0 < θ.variance :=
  mul_pos θ.p_pos θ.one_sub_p_pos

theorem sigma_pos (θ : BernoulliParameter) : 0 < θ.sigma :=
  Real.sqrt_pos.2 θ.variance_pos

theorem sigma_ne_zero (θ : BernoulliParameter) : θ.sigma ≠ 0 := ne_of_gt θ.sigma_pos

theorem sigma_sq (θ : BernoulliParameter) : θ.sigma ^ 2 = θ.variance :=
  Real.sq_sqrt θ.variance_pos.le

/-- A Boolean value viewed as a real number. -/
def bitValue : Bool → ℝ
  | false => 0
  | true => 1

/-- The Bernoulli mass of one Boolean coordinate. -/
def bitMass (θ : BernoulliParameter) : Bool → ℝ
  | false => 1 - θ.p
  | true => θ.p

theorem bitMass_nonneg (θ : BernoulliParameter) (b : Bool) : 0 ≤ θ.bitMass b := by
  cases b <;> simp [bitMass, θ.p_pos.le, θ.p_lt_one.le]

@[simp]
theorem sum_bitMass (θ : BernoulliParameter) : ∑ b : Bool, θ.bitMass b = 1 := by
  rw [Fintype.sum_bool]
  simp [bitMass]

/-- The centered, variance-one character of one Bernoulli coordinate. -/
noncomputable def oneCharacter (θ : BernoulliParameter) (b : Bool) : ℝ :=
  (bitValue b - θ.p) / θ.sigma

@[simp]
theorem sum_bitMass_mul_oneCharacter (θ : BernoulliParameter) :
    ∑ b : Bool, θ.bitMass b * θ.oneCharacter b = 0 := by
  rw [Fintype.sum_bool]
  simp only [bitMass, oneCharacter, bitValue]
  field_simp [θ.sigma_ne_zero]
  ring

@[simp]
theorem sum_bitMass_mul_oneCharacter_sq (θ : BernoulliParameter) :
    ∑ b : Bool, θ.bitMass b * (θ.oneCharacter b) ^ 2 = 1 := by
  rw [Fintype.sum_bool]
  simp only [bitMass, oneCharacter, bitValue]
  field_simp [θ.sigma_ne_zero]
  rw [θ.sigma_sq]
  simp only [variance]
  ring

/-- The coefficient contributed by one edge that is forced to be present. -/
noncomputable def forcedWeight (θ : BernoulliParameter) : ℝ :=
  (1 - θ.p) / θ.sigma

theorem forcedWeight_pos (θ : BernoulliParameter) : 0 < θ.forcedWeight :=
  div_pos θ.one_sub_p_pos θ.sigma_pos

theorem forcedWeight_sq (θ : BernoulliParameter) :
    θ.forcedWeight ^ 2 = (1 - θ.p) / θ.p := by
  unfold forcedWeight
  field_simp [θ.p_pos.ne', θ.sigma_ne_zero]
  rw [θ.sigma_sq]
  simp only [variance]
  ring

/-- The preceding algebraic weight is exactly the paper's square-root odds. -/
theorem forcedWeight_eq_sqrt_odds (θ : BernoulliParameter) :
    θ.forcedWeight = Real.sqrt ((1 - θ.p) / θ.p) := by
  symm
  apply (Real.sqrt_eq_iff_eq_sq (div_nonneg θ.one_sub_p_pos.le θ.p_pos.le)
    θ.forcedWeight_pos.le).2
  exact θ.forcedWeight_sq.symm

/-- One-coordinate likelihood identity for forcing a Bernoulli bit to be `true`. -/
theorem bitValue_div_p_eq_one_add (θ : BernoulliParameter) (b : Bool) :
    bitValue b / θ.p = 1 + θ.forcedWeight * θ.oneCharacter b := by
  cases b <;> simp only [bitValue, forcedWeight, oneCharacter]
  · field_simp [θ.p_pos.ne', θ.sigma_ne_zero]
    rw [θ.sigma_sq]
    simp only [variance]
    ring
  · field_simp [θ.p_pos.ne', θ.sigma_ne_zero]
    rw [θ.sigma_sq]
    simp only [variance]
    ring

/-- One-coordinate resampling kernel: retain the old bit with probability `1-ε`,
and otherwise draw a fresh Bernoulli bit. -/
def bitNoiseMass (θ : BernoulliParameter) (ε : ℝ) (x y : Bool) : ℝ :=
  (1 - ε) * (if x = y then 1 else 0) + ε * θ.bitMass y

theorem bitNoiseMass_nonneg (θ : BernoulliParameter) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : Bool) : 0 ≤ θ.bitNoiseMass ε x y := by
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hε1) (by split <;> norm_num))
    (mul_nonneg hε0 (θ.bitMass_nonneg y))

@[simp]
theorem sum_bitNoiseMass (θ : BernoulliParameter) (ε : ℝ) (x : Bool) :
    ∑ y : Bool, θ.bitNoiseMass ε x y = 1 := by
  cases x <;> rw [Fintype.sum_bool] <;> simp [bitNoiseMass, bitMass] <;> ring

/-- Detailed balance of the one-coordinate resampling kernel. -/
theorem bitNoise_detailedBalance (θ : BernoulliParameter) (ε : ℝ) (x y : Bool) :
    θ.bitMass x * θ.bitNoiseMass ε x y =
      θ.bitMass y * θ.bitNoiseMass ε y x := by
  cases x <;> cases y <;> simp [bitNoiseMass, bitMass] <;> ring

/-- The centered one-coordinate character is an eigenfunction of resampling. -/
theorem sum_bitNoiseMass_mul_oneCharacter (θ : BernoulliParameter) (ε : ℝ) (x : Bool) :
    ∑ y : Bool, θ.bitNoiseMass ε x y * θ.oneCharacter y =
      (1 - ε) * θ.oneCharacter x := by
  cases x <;> rw [Fintype.sum_bool] <;>
    simp [bitNoiseMass, bitMass, oneCharacter, bitValue] <;>
    field_simp [θ.sigma_ne_zero] <;> ring

/-- One-coordinate reproducing-kernel identity for the basis `{1,r}`. -/
theorem bitMass_mul_characterKernel (θ : BernoulliParameter) (x y : Bool) :
    θ.bitMass y * (1 + θ.oneCharacter y * θ.oneCharacter x) =
      if y = x then 1 else 0 := by
  cases x <;> cases y <;>
    simp only [bitMass, oneCharacter, bitValue, reduceCtorEq, ↓reduceIte] <;>
    field_simp [θ.sigma_ne_zero] <;>
    rw [θ.sigma_sq] <;>
    simp only [variance] <;>
    ring

end BernoulliParameter

section Cube

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A sum of coordinatewise products factors into one-coordinate sums. -/
private theorem sum_prod_configuration (g : E → Bool → ℝ) :
    ∑ x : BooleanConfiguration E, ∏ e, g e (x e) = ∏ e, ∑ b : Bool, g e b := by
  simpa using (Fintype.prod_sum g).symm

/-- Product Bernoulli mass on the finite Boolean cube. -/
def bernoulliProductMass (θ : BernoulliParameter) (x : BooleanConfiguration E) : ℝ :=
  ∏ e, θ.bitMass (x e)

theorem bernoulliProductMass_nonneg (θ : BernoulliParameter)
    (x : BooleanConfiguration E) : 0 ≤ bernoulliProductMass θ x := by
  exact Finset.prod_nonneg fun e _ ↦ θ.bitMass_nonneg (x e)

/-- The Bernoulli product mass is normalized. -/
@[simp]
theorem sum_bernoulliProductMass (θ : BernoulliParameter) :
    ∑ x : BooleanConfiguration E, bernoulliProductMass θ x = 1 := by
  calc
    ∑ x : BooleanConfiguration E, bernoulliProductMass θ x =
        ∏ e : E, ∑ b : Bool, θ.bitMass b := sum_prod_configuration _
    _ = 1 := by simp [BernoulliParameter.bitMass]

/-- The product Bernoulli law, connected to the finite-law API. -/
def bernoulliProductLaw (θ : BernoulliParameter) : FiniteLaw (BooleanConfiguration E) where
  mass := bernoulliProductMass θ
  mass_nonneg := bernoulliProductMass_nonneg θ
  sum_mass := sum_bernoulliProductMass θ

/-- Expectation under the product Bernoulli law. -/
def bernoulliExpectation (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) : ℝ :=
  ∑ x, bernoulliProductMass θ x * f x

@[simp]
theorem bernoulliExpectation_one (θ : BernoulliParameter) :
    bernoulliExpectation θ (fun _ : BooleanConfiguration E ↦ (1 : ℝ)) = 1 := by
  simp [bernoulliExpectation]

/-- The real inner product under the product Bernoulli law. -/
def bernoulliInner (θ : BernoulliParameter)
    (f g : BooleanConfiguration E → ℝ) : ℝ :=
  bernoulliExpectation θ fun x ↦ f x * g x

theorem bernoulliInner_comm (θ : BernoulliParameter)
    (f g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ f g = bernoulliInner θ g f := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [bernoulliInner, bernoulliExpectation]
  ring

/-- The normalized character on one named coordinate. -/
noncomputable def edgeCharacter (θ : BernoulliParameter) (e : E)
    (x : BooleanConfiguration E) : ℝ :=
  θ.oneCharacter (x e)

/-- The product character indexed by a finite coordinate subset. -/
noncomputable def fourierCharacter (θ : BernoulliParameter) (S : Finset E)
    (x : BooleanConfiguration E) : ℝ :=
  ∏ e : E, if e ∈ S then edgeCharacter θ e x else 1

theorem fourierCharacter_eq_prod (θ : BernoulliParameter) (S : Finset E)
    (x : BooleanConfiguration E) :
    fourierCharacter θ S x = ∏ e ∈ S, edgeCharacter θ e x := by
  classical
  rw [fourierCharacter]
  calc
    (∏ e : E, if e ∈ S then edgeCharacter θ e x else 1) =
        ∏ e ∈ S, (if e ∈ S then edgeCharacter θ e x else 1) := by
          symm
          apply Finset.prod_subset (Finset.subset_univ S)
          intro e _ he
          simp [he]
    _ = ∏ e ∈ S, edgeCharacter θ e x := by simp

@[simp]
theorem fourierCharacter_empty (θ : BernoulliParameter) (x : BooleanConfiguration E) :
    fourierCharacter θ ∅ x = 1 := by
  simp [fourierCharacter_eq_prod]

/-- Fourier coefficient with the paper's Bernoulli normalization. -/
noncomputable def fourierCoeff (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) (S : Finset E) : ℝ :=
  bernoulliInner θ f (fourierCharacter θ S)

/-- Bernoulli subset characters are orthonormal. -/
theorem fourierCharacters_orthonormal (θ : BernoulliParameter) (S T : Finset E) :
    bernoulliInner θ (fourierCharacter θ S) (fourierCharacter θ T) =
      if S = T then 1 else 0 := by
  classical
  unfold bernoulliInner bernoulliExpectation bernoulliProductMass fourierCharacter edgeCharacter
  simp_rw [← Finset.prod_mul_distrib]
  let g : E → Bool → ℝ := fun e b ↦
    θ.bitMass b *
      ((if e ∈ S then θ.oneCharacter b else 1) *
        (if e ∈ T then θ.oneCharacter b else 1))
  change (∑ x : BooleanConfiguration E, ∏ e, g e (x e)) = if S = T then 1 else 0
  rw [sum_prod_configuration]
  by_cases hST : S = T
  · subst T
    simp only [if_pos rfl]
    apply Finset.prod_eq_one
    intro e _
    by_cases he : e ∈ S
    · simpa [g, he, pow_two] using θ.sum_bitMass_mul_oneCharacter_sq
    · simpa [g, he, Fintype.sum_bool, add_comm] using θ.sum_bitMass
  · rw [if_neg hST]
    have hmem : ¬∀ e : E, (e ∈ S ↔ e ∈ T) := by
      intro h
      exact hST (Finset.ext h)
    push_neg at hmem
    obtain ⟨e, he⟩ := hmem
    have he' : (e ∈ S ∧ e ∉ T) ∨ (e ∉ S ∧ e ∈ T) := by tauto
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    rcases he' with ⟨heS, heT⟩ | ⟨heS, heT⟩
    · simpa [g, heS, heT] using θ.sum_bitMass_mul_oneCharacter
    · simpa [g, heS, heT] using θ.sum_bitMass_mul_oneCharacter

/-- Summing over all subsets factors into the product of one-coordinate kernels. -/
theorem sum_fourierCharacter_mul (θ : BernoulliParameter)
    (x y : BooleanConfiguration E) :
    ∑ S : Finset E, fourierCharacter θ S x * fourierCharacter θ S y =
      ∏ e : E, (1 + edgeCharacter θ e x * edgeCharacter θ e y) := by
  classical
  simpa [fourierCharacter_eq_prod, Finset.prod_mul_distrib, add_comm] using
    (Fintype.prod_add
      (fun e : E ↦ edgeCharacter θ e x * edgeCharacter θ e y)
      (fun _ : E ↦ (1 : ℝ))).symm

/-- Weighted completeness kernel of the Bernoulli characters. -/
theorem bernoulliProductMass_mul_characterKernel (θ : BernoulliParameter)
    (x y : BooleanConfiguration E) :
    bernoulliProductMass θ y *
        (∑ S : Finset E, fourierCharacter θ S y * fourierCharacter θ S x) =
      if y = x then 1 else 0 := by
  rw [sum_fourierCharacter_mul]
  unfold bernoulliProductMass edgeCharacter
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ e : E, θ.bitMass (y e) *
        (1 + θ.oneCharacter (y e) * θ.oneCharacter (x e))) =
        ∏ e : E, (if y e = x e then 1 else 0) := by
          apply Finset.prod_congr rfl
          intro e _
          exact θ.bitMass_mul_characterKernel (x e) (y e)
    _ = if y = x then 1 else 0 := by
      by_cases hxy : y = x
      · subst y
        simp
      · rw [if_neg hxy]
        have hex : ∃ e : E, y e ≠ x e := by
          by_contra h
          push_neg at h
          exact hxy (funext h)
        obtain ⟨e, he⟩ := hex
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp [he]

/-- Linearity of the Bernoulli inner product in a finite sum. -/
theorem bernoulliInner_finset_sum_left {ι : Type*} (θ : BernoulliParameter)
    (s : Finset ι) (a : ι → ℝ) (f : ι → BooleanConfiguration E → ℝ)
    (g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ (fun x ↦ ∑ i ∈ s, a i * f i x) g =
      ∑ i ∈ s, a i * bernoulliInner θ (f i) g := by
  unfold bernoulliInner bernoulliExpectation
  calc
    (∑ x, bernoulliProductMass θ x * ((∑ i ∈ s, a i * f i x) * g x)) =
        ∑ x, ∑ i ∈ s, a i * (bernoulliProductMass θ x * (f i x * g x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i ∈ s, ∑ x, a i * (bernoulliProductMass θ x * (f i x * g x)) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, a i * ∑ x, bernoulliProductMass θ x * (f i x * g x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- Reconstruct a function from a prescribed finite family of Fourier coefficients. -/
noncomputable def fourierSum (θ : BernoulliParameter) (a : Finset E → ℝ)
    (x : BooleanConfiguration E) : ℝ :=
  ∑ S : Finset E, a S * fourierCharacter θ S x

theorem bernoulliInner_fourierSum_left (θ : BernoulliParameter) (a : Finset E → ℝ)
    (g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ (fourierSum θ a) g =
      ∑ S : Finset E, a S * bernoulliInner θ (fourierCharacter θ S) g := by
  simpa [fourierSum] using
    (bernoulliInner_finset_sum_left θ (Finset.univ : Finset (Finset E)) a
      (fourierCharacter θ) g)

/-- Orthonormality recovers every prescribed coefficient of a Fourier sum. -/
@[simp]
theorem fourierCoeff_fourierSum (θ : BernoulliParameter) (a : Finset E → ℝ) (T : Finset E) :
    fourierCoeff θ (fourierSum θ a) T = a T := by
  unfold fourierCoeff
  rw [bernoulliInner_fourierSum_left]
  simp [fourierCharacters_orthonormal]

/-- Every function on the finite Boolean cube has its exact Bernoulli Fourier expansion. -/
theorem fourierExpansion (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) (x : BooleanConfiguration E) :
    f x = fourierSum θ (fourierCoeff θ f) x := by
  unfold fourierSum fourierCoeff bernoulliInner bernoulliExpectation
  symm
  calc
    (∑ S : Finset E,
        (∑ y, bernoulliProductMass θ y * (f y * fourierCharacter θ S y)) *
          fourierCharacter θ S x) =
        ∑ S : Finset E, ∑ y, bernoulliProductMass θ y * f y *
          fourierCharacter θ S y * fourierCharacter θ S x := by
            apply Finset.sum_congr rfl
            intro S _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ = ∑ y, ∑ S : Finset E, bernoulliProductMass θ y * f y *
          fourierCharacter θ S y * fourierCharacter θ S x := by
            rw [Finset.sum_comm]
    _ = ∑ y, f y * (bernoulliProductMass θ y *
          ∑ S : Finset E, fourierCharacter θ S y * fourierCharacter θ S x) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro S _
            ring
    _ = ∑ y, if y = x then f y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [bernoulliProductMass_mul_characterKernel]
      split <;> simp_all
    _ = f x := by simp

/-- Function-valued form of the exact Fourier expansion. -/
theorem fourierExpansion_fun (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) :
    fourierSum θ (fourierCoeff θ f) = f := by
  funext x
  exact (fourierExpansion θ f x).symm

/-- Parseval's bilinear identity on the Bernoulli cube. -/
theorem fourierParseval (θ : BernoulliParameter)
    (f g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ f g =
      ∑ S : Finset E, fourierCoeff θ f S * fourierCoeff θ g S := by
  calc
    bernoulliInner θ f g =
        bernoulliInner θ (fourierSum θ (fourierCoeff θ f)) g := by
          rw [fourierExpansion_fun]
    _ = ∑ S : Finset E,
          fourierCoeff θ f S * bernoulliInner θ (fourierCharacter θ S) g := by
          rw [bernoulliInner_fourierSum_left]
    _ = ∑ S : Finset E, fourierCoeff θ f S * fourierCoeff θ g S := by
          apply Finset.sum_congr rfl
          intro S _
          congr 1
          exact bernoulliInner_comm θ (fourierCharacter θ S) g

/-- Squared-norm form of Parseval. -/
theorem fourierParseval_sq (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) :
    bernoulliInner θ f f = ∑ S : Finset E, (fourierCoeff θ f S) ^ 2 := by
  simpa [pow_two] using fourierParseval θ f f

/-- The likelihood ratio for requiring every coordinate in `A` to be present. -/
noncomputable def forcedLikelihood (θ : BernoulliParameter) (A : Finset E)
    (x : BooleanConfiguration E) : ℝ :=
  ∏ e ∈ A, BernoulliParameter.bitValue (x e) / θ.p

/-- Pointwise Fourier expansion of a fixed forced coordinate set. -/
theorem forcedLikelihood_fourierExpansion (θ : BernoulliParameter) (A : Finset E)
    (x : BooleanConfiguration E) :
    forcedLikelihood θ A x =
      ∑ S ∈ A.powerset, θ.forcedWeight ^ S.card * fourierCharacter θ S x := by
  classical
  unfold forcedLikelihood
  simp_rw [θ.bitValue_div_p_eq_one_add]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  simp [fourierCharacter_eq_prod, edgeCharacter]

/-- The fixed-forcing likelihood as a full coefficient function on all subsets. -/
theorem forcedLikelihood_eq_fourierSum (θ : BernoulliParameter) (A : Finset E) :
    forcedLikelihood θ A =
      fourierSum θ (fun S ↦ if S ⊆ A then θ.forcedWeight ^ S.card else 0) := by
  classical
  funext x
  rw [forcedLikelihood_fourierExpansion]
  unfold fourierSum
  calc
    (∑ S ∈ A.powerset, θ.forcedWeight ^ S.card * fourierCharacter θ S x) =
        ∑ S ∈ (Finset.univ.filter fun S : Finset E ↦ S ⊆ A),
          θ.forcedWeight ^ S.card * fourierCharacter θ S x := by
            congr 1
            ext S
            simp
    _ = ∑ S : Finset E,
          if S ⊆ A then θ.forcedWeight ^ S.card * fourierCharacter θ S x else 0 := by
            rw [Finset.sum_ite]
            simp
    _ = ∑ S : Finset E,
          (if S ⊆ A then θ.forcedWeight ^ S.card else 0) *
            fourierCharacter θ S x := by
            apply Finset.sum_congr rfl
            intro S _
            split <;> simp_all

/-- Exact coefficient of a likelihood that forces all coordinates in `A`. -/
theorem fourierCoeff_forcedLikelihood (θ : BernoulliParameter) (A T : Finset E) :
    fourierCoeff θ (forcedLikelihood θ A) T =
      if T ⊆ A then θ.forcedWeight ^ T.card else 0 := by
  rw [forcedLikelihood_eq_fourierSum, fourierCoeff_fourierSum]

/-- Fourier truncation to subsets of cardinality at most `D`. -/
noncomputable def lowDegreeProjection (θ : BernoulliParameter) (D : ℕ)
    (f : BooleanConfiguration E → ℝ) : BooleanConfiguration E → ℝ :=
  fourierSum θ fun S ↦ if S.card ≤ D then fourierCoeff θ f S else 0

/-- The truncation retains exactly the coefficients of degree at most `D`. -/
@[simp]
theorem fourierCoeff_lowDegreeProjection (θ : BernoulliParameter) (D : ℕ)
    (f : BooleanConfiguration E → ℝ) (T : Finset E) :
    fourierCoeff θ (lowDegreeProjection θ D f) T =
      if T.card ≤ D then fourierCoeff θ f T else 0 := by
  rw [lowDegreeProjection, fourierCoeff_fourierSum]

/-- Parseval on the finite-dimensional low-degree projection. -/
theorem lowDegreeProjection_norm_sq (θ : BernoulliParameter) (D : ℕ)
    (f : BooleanConfiguration E → ℝ) :
    bernoulliInner θ (lowDegreeProjection θ D f) (lowDegreeProjection θ D f) =
      ∑ S : Finset E with S.card ≤ D, (fourierCoeff θ f S) ^ 2 := by
  rw [fourierParseval_sq]
  simp [fourierCoeff_lowDegreeProjection]
  rw [Finset.sum_ite]
  simp

/-- Independent coordinatewise edge-resampling transition kernel. -/
def bernoulliNoiseTransition (θ : BernoulliParameter) (ε : ℝ)
    (x y : BooleanConfiguration E) : ℝ :=
  ∏ e, θ.bitNoiseMass ε (x e) (y e)

theorem bernoulliNoiseTransition_nonneg (θ : BernoulliParameter) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : BooleanConfiguration E) :
    0 ≤ bernoulliNoiseTransition θ ε x y := by
  exact Finset.prod_nonneg fun e _ ↦ θ.bitNoiseMass_nonneg hε0 hε1 (x e) (y e)

/-- Every row of the finite noise kernel has mass one. -/
@[simp]
theorem sum_bernoulliNoiseTransition (θ : BernoulliParameter) (ε : ℝ)
    (x : BooleanConfiguration E) :
    ∑ y, bernoulliNoiseTransition θ ε x y = 1 := by
  unfold bernoulliNoiseTransition
  rw [sum_prod_configuration]
  apply Finset.prod_eq_one
  intro e _
  exact θ.sum_bitNoiseMass ε (x e)

/-- The Bernoulli product law satisfies detailed balance for edge resampling. -/
theorem bernoulliNoise_detailedBalance (θ : BernoulliParameter) (ε : ℝ)
    (x y : BooleanConfiguration E) :
    bernoulliProductMass θ x * bernoulliNoiseTransition θ ε x y =
      bernoulliProductMass θ y * bernoulliNoiseTransition θ ε y x := by
  unfold bernoulliProductMass bernoulliNoiseTransition
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  exact θ.bitNoise_detailedBalance ε (x e) (y e)

/-- Apply independent edge resampling to a function on configurations. -/
def edgeNoise (θ : BernoulliParameter) (ε : ℝ)
    (f : BooleanConfiguration E → ℝ) (x : BooleanConfiguration E) : ℝ :=
  ∑ y, bernoulliNoiseTransition θ ε x y * f y

@[simp]
theorem edgeNoise_one (θ : BernoulliParameter) (ε : ℝ) (x : BooleanConfiguration E) :
    edgeNoise θ ε (fun _ ↦ 1) x = 1 := by
  simp [edgeNoise]

/-- A degree-`|S|` character is multiplied by `(1-ε)^|S|` under edge resampling. -/
theorem edgeNoise_fourierCharacter (θ : BernoulliParameter) (ε : ℝ)
    (S : Finset E) (x : BooleanConfiguration E) :
    edgeNoise θ ε (fourierCharacter θ S) x =
      (1 - ε) ^ S.card * fourierCharacter θ S x := by
  classical
  unfold edgeNoise bernoulliNoiseTransition fourierCharacter edgeCharacter
  simp_rw [← Finset.prod_mul_distrib]
  let g : E → Bool → ℝ := fun e b ↦
    θ.bitNoiseMass ε (x e) b * (if e ∈ S then θ.oneCharacter b else 1)
  change (∑ y : BooleanConfiguration E, ∏ e, g e (y e)) =
    (1 - ε) ^ S.card * ∏ e : E, (if e ∈ S then θ.oneCharacter (x e) else 1)
  rw [sum_prod_configuration]
  calc
    (∏ e : E, ∑ b : Bool, g e b) =
        ∏ e : E, (if e ∈ S then (1 - ε) * θ.oneCharacter (x e) else 1) := by
          apply Finset.prod_congr rfl
          intro e _
          by_cases he : e ∈ S
          · simpa [g, he] using θ.sum_bitNoiseMass_mul_oneCharacter ε (x e)
          · simpa [g, he] using θ.sum_bitNoiseMass ε (x e)
    _ = ∏ e ∈ S, ((1 - ε) * θ.oneCharacter (x e)) := by
      rw [Finset.prod_ite_mem]
      simp
    _ = (1 - ε) ^ S.card * ∏ e ∈ S, θ.oneCharacter (x e) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = (1 - ε) ^ S.card *
        ∏ e : E, (if e ∈ S then θ.oneCharacter (x e) else 1) := by
      congr 1
      rw [Finset.prod_ite_mem]
      simp

/-- Pulling a scalar out of the right input of the inner product. -/
theorem bernoulliInner_const_mul_right (θ : BernoulliParameter) (a : ℝ)
    (f g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ f (fun x ↦ a * g x) = a * bernoulliInner θ f g := by
  unfold bernoulliInner bernoulliExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Reversibility makes the finite edge-noise operator self-adjoint. -/
theorem bernoulliInner_edgeNoise_self_adjoint (θ : BernoulliParameter) (ε : ℝ)
    (f g : BooleanConfiguration E → ℝ) :
    bernoulliInner θ (edgeNoise θ ε f) g =
      bernoulliInner θ f (edgeNoise θ ε g) := by
  unfold bernoulliInner bernoulliExpectation edgeNoise
  calc
    (∑ x, bernoulliProductMass θ x *
        ((∑ y, bernoulliNoiseTransition θ ε x y * f y) * g x)) =
        ∑ x, ∑ y, bernoulliProductMass θ x *
          bernoulliNoiseTransition θ ε x y * f y * g x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ = ∑ x, ∑ y, bernoulliProductMass θ y *
          bernoulliNoiseTransition θ ε y x * f y * g x := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [bernoulliNoise_detailedBalance θ ε x y]
    _ = ∑ y, ∑ x, bernoulliProductMass θ y *
          bernoulliNoiseTransition θ ε y x * f y * g x := by
            rw [Finset.sum_comm]
    _ = ∑ y, bernoulliProductMass θ y *
          (f y * ∑ x, bernoulliNoiseTransition θ ε y x * g x) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring

/-- Edge resampling multiplies a Fourier coefficient of degree `|S|` by `(1-ε)^|S|`. -/
theorem fourierCoeff_edgeNoise (θ : BernoulliParameter) (ε : ℝ)
    (f : BooleanConfiguration E → ℝ) (S : Finset E) :
    fourierCoeff θ (edgeNoise θ ε f) S =
      (1 - ε) ^ S.card * fourierCoeff θ f S := by
  unfold fourierCoeff
  rw [bernoulliInner_edgeNoise_self_adjoint]
  have hchar : edgeNoise θ ε (fourierCharacter θ S) =
      fun x ↦ (1 - ε) ^ S.card * fourierCharacter θ S x := by
    funext x
    exact edgeNoise_fourierCharacter θ ε S x
  rw [hchar, bernoulliInner_const_mul_right]

@[simp]
theorem fourierCoeff_empty (θ : BernoulliParameter)
    (f : BooleanConfiguration E → ℝ) :
    fourierCoeff θ f ∅ = bernoulliExpectation θ f := by
  simp [fourierCoeff, bernoulliInner, fourierCharacter_empty]

/-- Edge resampling preserves expectation under the null Bernoulli product law. -/
theorem bernoulliExpectation_edgeNoise (θ : BernoulliParameter) (ε : ℝ)
    (f : BooleanConfiguration E → ℝ) :
    bernoulliExpectation θ (edgeNoise θ ε f) = bernoulliExpectation θ f := by
  have h := fourierCoeff_edgeNoise θ ε f (∅ : Finset E)
  simpa using h

end Cube

end LowDegree
