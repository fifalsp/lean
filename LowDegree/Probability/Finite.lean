import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite probability laws and the TV/chi-square estimate

The observed graph at each fixed `n` lives in a finite sample space.  This
module proves the exact inequality used at the end of Theorem 1.1 without
appealing to measure-theoretic conventions about versions of a likelihood
ratio.
-/

namespace LowDegree

open scoped BigOperators

/-- A probability mass function represented directly in `ℝ`. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation under a finite law. -/
def expect (q : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, q.mass ω * f ω

/-- Probability of an event represented as a finset. -/
def prob (q : FiniteLaw Ω) (event : Finset Ω) : ℝ := ∑ ω ∈ event, q.mass ω

/-- Total variation distance in the finite setting. -/
noncomputable def tv (p q : FiniteLaw Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ ω, |p.mass ω - q.mass ω|

theorem tv_nonneg (p q : FiniteLaw Ω) : 0 ≤ p.tv q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

theorem tv_comm (p q : FiniteLaw Ω) : p.tv q = q.tv p := by
  simp only [tv, abs_sub_comm]

theorem tv_triangle (p q r : FiniteLaw Ω) : p.tv r ≤ p.tv q + q.tv r := by
  simp only [tv, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  simpa only [sub_add_sub_cancel] using
    (abs_add_le (p.mass ω - q.mass ω) (q.mass ω - r.mass ω))

theorem tv_le_one (p q : FiniteLaw Ω) : p.tv q ≤ 1 := by
  have hpoint : ∀ ω, |p.mass ω - q.mass ω| ≤ p.mass ω + q.mass ω := by
    intro ω
    calc
      |p.mass ω - q.mass ω| ≤ |p.mass ω| + |q.mass ω| := abs_sub _ _
      _ = p.mass ω + q.mass ω := by
        rw [abs_of_nonneg (p.mass_nonneg ω), abs_of_nonneg (q.mass_nonneg ω)]
  simp only [tv]
  calc
    (1 / 2 : ℝ) * ∑ ω, |p.mass ω - q.mass ω| ≤
        (1 / 2 : ℝ) * ∑ ω, (p.mass ω + q.mass ω) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ ↦ hpoint ω) (by norm_num)
    _ = 1 := by rw [Finset.sum_add_distrib, p.sum_mass, q.sum_mass]; norm_num

/-- Event-probability differences are bounded by total variation, with the
paper's `1/2 · ℓ¹` normalization. -/
theorem abs_prob_sub_prob_le_tv (p q : FiniteLaw Ω) (event : Finset Ω) :
    |p.prob event - q.prob event| ≤ p.tv q := by
  classical
  let d : Ω → ℝ := fun ω ↦ p.mass ω - q.mass ω
  have hsumzero : ∑ ω, d ω = 0 := by
    simp only [d, Finset.sum_sub_distrib, p.sum_mass, q.sum_mass, sub_self]
  have hsplit := event.sum_add_sum_compl d
  have hcomp : ∑ ω ∈ eventᶜ, d ω = -(∑ ω ∈ event, d ω) := by
    rw [hsumzero] at hsplit
    linarith
  have hevent : |∑ ω ∈ event, d ω| ≤ ∑ ω ∈ event, |d ω| :=
    Finset.abs_sum_le_sum_abs _ _
  have hcompl : |∑ ω ∈ event, d ω| ≤ ∑ ω ∈ eventᶜ, |d ω| := by
    rw [← abs_neg, ← hcomp]
    exact Finset.abs_sum_le_sum_abs _ _
  have htwo : 2 * |∑ ω ∈ event, d ω| ≤ ∑ ω, |d ω| := by
    calc
      2 * |∑ ω ∈ event, d ω| =
          |∑ ω ∈ event, d ω| + |∑ ω ∈ event, d ω| := by ring
      _ ≤ (∑ ω ∈ event, |d ω|) + ∑ ω ∈ eventᶜ, |d ω| :=
        add_le_add hevent hcompl
      _ = ∑ ω, |d ω| := event.sum_add_sum_compl _
  have hprob : p.prob event - q.prob event = ∑ ω ∈ event, d ω := by
    simp [prob, d, Finset.sum_sub_distrib]
  rw [hprob, tv]
  linarith

/-- `L` is a pointwise likelihood ratio of `p` with respect to `q`. -/
def IsLikelihoodRatio (p q : FiniteLaw Ω) (L : Ω → ℝ) : Prop :=
  ∀ ω, p.mass ω = q.mass ω * L ω

theorem expect_one (q : FiniteLaw Ω) : q.expect (fun _ ↦ 1) = 1 := by
  simp [expect, q.sum_mass]

theorem expect_likelihood_eq_one {p q : FiniteLaw Ω} {L : Ω → ℝ}
    (hL : IsLikelihoodRatio p q L) : q.expect L = 1 := by
  rw [expect]
  calc
    ∑ ω, q.mass ω * L ω = ∑ ω, p.mass ω := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (hL ω).symm
    _ = 1 := p.sum_mass

theorem tv_eq_half_expect_abs_sub_one {p q : FiniteLaw Ω} {L : Ω → ℝ}
    (hL : IsLikelihoodRatio p q L) :
    p.tv q = (1 / 2 : ℝ) * q.expect (fun ω ↦ |L ω - 1|) := by
  simp only [tv, expect]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [hL ω]
  have hfactor : q.mass ω * L ω - q.mass ω = q.mass ω * (L ω - 1) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (q.mass_nonneg ω)]

private theorem weighted_cauchy (q : FiniteLaw Ω) (f : Ω → ℝ) :
    (q.expect fun ω ↦ |f ω|) ^ 2 ≤ q.expect (fun ω ↦ (f ω) ^ 2) := by
  let s : Finset Ω := Finset.univ
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (R := ℝ) s
    (r := fun ω ↦ q.mass ω * |f ω|)
    (f := fun ω ↦ q.mass ω * (f ω) ^ 2)
    (g := fun ω ↦ q.mass ω)
    (fun ω _ ↦ mul_nonneg (q.mass_nonneg ω) (sq_nonneg _))
    (fun ω _ ↦ q.mass_nonneg ω)
    (fun ω _ ↦ by rw [mul_pow, sq_abs]; ring)
  simpa [FiniteLaw.expect, s, q.sum_mass] using h

/-- Finite Cauchy--Schwarz in the exact form used by the paper. -/
theorem expect_abs_sq_le_expect_sq (q : FiniteLaw Ω) (f : Ω → ℝ) :
    (q.expect fun ω ↦ |f ω|) ^ 2 ≤ q.expect (fun ω ↦ (f ω) ^ 2) :=
  weighted_cauchy q f

theorem expect_sq_sub_one {p q : FiniteLaw Ω} {L : Ω → ℝ}
    (hL : IsLikelihoodRatio p q L) :
    q.expect (fun ω ↦ (L ω - 1) ^ 2) = q.expect (fun ω ↦ (L ω) ^ 2) - 1 := by
  have hmean : q.expect L = 1 := expect_likelihood_eq_one hL
  rw [expect] at hmean ⊢
  calc
    ∑ ω, q.mass ω * (L ω - 1) ^ 2
        = ∑ ω, (q.mass ω * (L ω) ^ 2 - 2 * (q.mass ω * L ω) + q.mass ω) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = (∑ ω, q.mass ω * (L ω) ^ 2) - 2 * (∑ ω, q.mass ω * L ω) +
            ∑ ω, q.mass ω := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ ω, q.mass ω * (L ω) ^ 2) - 1 := by rw [hmean, q.sum_mass]; ring

/-- The paper's TV/chi-square inequality
`TV(p,q) ≤ 1/2 * sqrt(E_q[L²] - 1)`. -/
theorem tv_le_half_sqrt_chiSq {p q : FiniteLaw Ω} {L : Ω → ℝ}
    (hL : IsLikelihoodRatio p q L) :
    p.tv q ≤ (1 / 2 : ℝ) * Real.sqrt (q.expect (fun ω ↦ (L ω) ^ 2) - 1) := by
  rw [tv_eq_half_expect_abs_sub_one hL]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsq := expect_abs_sq_le_expect_sq q (fun ω ↦ L ω - 1)
  rw [expect_sq_sub_one hL] at hsq
  have hnonneg : 0 ≤ q.expect (fun ω ↦ |L ω - 1|) := by
    exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (q.mass_nonneg ω) (abs_nonneg _)
  have hchi : 0 ≤ q.expect (fun ω ↦ (L ω) ^ 2) - 1 :=
    (sq_nonneg (q.expect fun ω ↦ |L ω - 1|)).trans hsq
  exact (Real.le_sqrt hnonneg hchi).2 hsq

end FiniteLaw

end LowDegree
