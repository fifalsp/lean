import LowDegree.Asymptotics.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exact and leading Fourier weights

This file fixes the normalization of the paper's `αₙ(F)` and `βₙ(F)`.
In particular, `n^(e-v)` is represented as `n^e / n^v`, so trees (where
`e-v=-1`) are handled correctly rather than by truncated natural subtraction.
-/

namespace LowDegree

open scoped BigOperators

/-- The real-valued falling factorial `(n)ᵥ`. -/
def fallingFactorial (n v : ℕ) : ℝ := (n.descFactorial v : ℝ)

/-- The exact isomorphism-class summand `αₙ(F)` from Equation (3.5). -/
noncomputable def alphaWeight
    (c : ℝ) (n e v copyCount autCount : ℕ) : ℝ :=
  (((1 - c / n) / (c / n)) ^ e) *
    ((copyCount : ℝ) ^ 2 * autCount) / fallingFactorial n v

/-- The leading summand `βₙ(F)` used from Lemma 3.1 onward. -/
noncomputable def betaWeight
    (c : ℝ) (n e v copyCount autCount : ℕ) : ℝ :=
  ((((n : ℝ) ^ e / (n : ℝ) ^ v) / c ^ e) *
    ((copyCount : ℝ) ^ 2 * autCount))

/-- The factor left after cancelling the copy and automorphism terms in
`αₙ(F)/βₙ(F)`. -/
noncomputable def leadingRatio (c : ℝ) (n e v : ℕ) : ℝ :=
  (1 - c / n) ^ e * (n : ℝ) ^ v / fallingFactorial n v

theorem fallingFactorial_ne_zero {n v : ℕ} (hv : v ≤ n) :
    fallingFactorial n v ≠ 0 := by
  simp only [fallingFactorial, Nat.cast_ne_zero]
  exact (Nat.descFactorial_eq_zero_iff_lt.not.mpr (Nat.not_lt.mpr hv))

/-- Exact cancellation identity in the proof of Lemma 3.1. -/
theorem alpha_div_beta_exact
    {c : ℝ} {n e v copyCount autCount : ℕ}
    (hc : c ≠ 0) (hn : n ≠ 0) (hv : v ≤ n)
    (hcopy : copyCount ≠ 0) (haut : autCount ≠ 0) :
    alphaWeight c n e v copyCount autCount /
        betaWeight c n e v copyCount autCount =
      leadingRatio c n e v := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hcopyr : (copyCount : ℝ) ≠ 0 := by exact_mod_cast hcopy
  have hautr : (autCount : ℝ) ≠ 0 := by exact_mod_cast haut
  have hfall := fallingFactorial_ne_zero hv
  simp only [alphaWeight, betaWeight, leadingRatio]
  field_simp
  rw [← mul_pow, ← mul_pow]
  congr 1
  field_simp

/-- Casted product form of the falling factorial, with the domain guard made
explicit. -/
theorem fallingFactorial_eq_prod (n v : ℕ) (hv : v ≤ n) :
    fallingFactorial n v =
      ∏ j ∈ Finset.range v, ((n : ℝ) - (j : ℝ)) := by
  rw [fallingFactorial, Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.cast_sub]
  exact (Nat.le_trans (Finset.mem_range.mp hj).le hv)

/-- Product identity displayed in the proof of Lemma 3.1. -/
theorem leadingRatio_eq_product
    {c : ℝ} {n e v : ℕ} (hn : n ≠ 0) (hv : v ≤ n) :
    leadingRatio c n e v =
      (1 - c / n) ^ e *
        ∏ j ∈ Finset.range v, (1 - (j : ℝ) / n)⁻¹ := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [leadingRatio, fallingFactorial_eq_prod n v hv]
  have hfactor :
      (∏ j ∈ Finset.range v, ((n : ℝ) - (j : ℝ))) =
        (n : ℝ) ^ v * ∏ j ∈ Finset.range v, (1 - (j : ℝ) / n) := by
    calc
      (∏ j ∈ Finset.range v, ((n : ℝ) - (j : ℝ))) =
          ∏ j ∈ Finset.range v, ((n : ℝ) * (1 - (j : ℝ) / n)) := by
            apply Finset.prod_congr rfl
            intro j _
            field_simp
      _ = (∏ _j ∈ Finset.range v, (n : ℝ)) *
          ∏ j ∈ Finset.range v, (1 - (j : ℝ) / n) := by
            rw [← Finset.prod_mul_distrib]
      _ = (n : ℝ) ^ v *
          ∏ j ∈ Finset.range v, (1 - (j : ℝ) / n) := by simp
  rw [hfactor]
  have hnpow : (n : ℝ) ^ v ≠ 0 := pow_ne_zero _ hnr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hprod : (∏ j ∈ Finset.range v, (1 - (j : ℝ) / n)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjn : j < n := (Finset.mem_range.mp hj).trans_le hv
    have hjdiv : (j : ℝ) / n < 1 := (div_lt_one hnpos).2 (by exact_mod_cast hjn)
    exact (sub_pos.mpr hjdiv).ne'
  rw [Finset.prod_inv_distrib]
  field_simp

/-- The elementary logarithm estimate used in the proof of Lemma 3.1:
`|log (1-x)| ≤ 2x` on `[0,1/2]`. -/
theorem abs_log_one_sub_le_two_mul
    {x : ℝ} (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hone_sub_pos : 0 < 1 - x := by linarith
  have hone_sub_le_one : 1 - x ≤ 1 := by linarith
  have hlog_nonpos : Real.log (1 - x) ≤ 0 :=
    Real.log_nonpos hone_sub_pos.le hone_sub_le_one
  rw [abs_of_nonpos hlog_nonpos]
  have hlower := Real.one_sub_inv_le_log_of_pos hone_sub_pos
  have hinv_bound : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    have hrewrite : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp
      ring
    rw [hrewrite, div_le_iff₀ hone_sub_pos]
    nlinarith
  linarith

/-- Positivity of the leading ratio under the eventual Bernoulli-domain
guard.  The assumptions are kept explicit because `G(n,c/n)` is only used
for sufficiently large `n` in the paper. -/
theorem leadingRatio_pos
    {c : ℝ} {n e v : ℕ}
    (hn : 0 < n) (hc_nonneg : 0 ≤ c)
    (hc_domain : c / (n : ℝ) < 1) (hv : v ≤ n) :
    0 < leadingRatio c n e v := by
  rw [leadingRatio_eq_product hn.ne' hv]
  apply mul_pos
  · exact pow_pos (sub_pos.mpr hc_domain) _
  · apply Finset.prod_pos
    intro j hj
    apply inv_pos.mpr
    apply sub_pos.mpr
    have hjn : j < n := (Finset.mem_range.mp hj).trans_le hv
    exact (div_lt_one (by exact_mod_cast hn)).2 (by exact_mod_cast hjn)

/-- Twice the sum of the integers below `v` is at most `v²`, in the
real-valued form used by the logarithmic estimate. -/
private theorem sum_two_mul_range_le_sq (v : ℕ) :
    (∑ j ∈ Finset.range v, (2 : ℝ) * (j : ℝ)) ≤ (v : ℝ) ^ 2 := by
  induction v with
  | zero => simp
  | succ v induction_hypothesis =>
      rw [Finset.sum_range_succ]
      push_cast
      calc
        (∑ x ∈ Finset.range v, 2 * (x : ℝ)) + 2 * (v : ℝ) ≤
            (v : ℝ) ^ 2 + 2 * (v : ℝ) :=
          add_le_add_right induction_hypothesis _
        _ ≤ ((v : ℝ) + 1) ^ 2 := by nlinarith only

/-- Quantitative logarithmic bound from the proof of paper Lemma 3.1.

The two half-domain hypotheses are precisely the eventual guards under
which the paper invokes `|log(1-x)| ≤ 2x`. -/
theorem abs_log_leadingRatio_le
    {c : ℝ} {n e v : ℕ}
    (hn : 0 < n) (hc_nonneg : 0 ≤ c)
    (hc_half : c / (n : ℝ) ≤ 1 / 2)
    (hv : v ≤ n) (hv_half : (v : ℝ) / n ≤ 1 / 2) :
    |Real.log (leadingRatio c n e v)| ≤
      2 * c * (e : ℝ) / n + (v : ℝ) ^ 2 / n := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hc_div_nonneg : 0 ≤ c / (n : ℝ) := div_nonneg hc_nonneg hn_real.le
  have hc_base_pos : 0 < 1 - c / (n : ℝ) := by linarith
  have hj_base_pos : ∀ j ∈ Finset.range v,
      0 < 1 - (j : ℝ) / (n : ℝ) := by
    intro j hj
    have hjn : j < n := (Finset.mem_range.mp hj).trans_le hv
    exact sub_pos.mpr ((div_lt_one hn_real).2 (by exact_mod_cast hjn))
  have hprod_ne :
      (∏ j ∈ Finset.range v, (1 - (j : ℝ) / (n : ℝ))⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact (inv_pos.mpr (hj_base_pos j hj)).ne'
  rw [leadingRatio_eq_product hn.ne' hv,
    Real.log_mul (pow_ne_zero _ hc_base_pos.ne') hprod_ne,
    Real.log_pow,
    Real.log_prod]
  · simp_rw [Real.log_inv]
    have hc_log : |Real.log (1 - c / (n : ℝ))| ≤
        2 * (c / (n : ℝ)) :=
      abs_log_one_sub_le_two_mul hc_div_nonneg hc_half
    have hj_log : ∀ j ∈ Finset.range v,
        |-Real.log (1 - (j : ℝ) / (n : ℝ))| ≤
          2 * ((j : ℝ) / (n : ℝ)) := by
      intro j hj
      rw [abs_neg]
      apply abs_log_one_sub_le_two_mul
      · positivity
      · calc
          (j : ℝ) / (n : ℝ) ≤ (v : ℝ) / (n : ℝ) := by
            apply (div_le_div_iff_of_pos_right hn_real).2
            exact_mod_cast (Finset.mem_range.mp hj).le
          _ ≤ 1 / 2 := hv_half
    have hsum_nat := sum_two_mul_range_le_sq v
    have hsum_div :
        (∑ j ∈ Finset.range v, 2 * ((j : ℝ) / (n : ℝ))) ≤
          (v : ℝ) ^ 2 / (n : ℝ) := by
      calc
        (∑ j ∈ Finset.range v, 2 * ((j : ℝ) / (n : ℝ))) =
            (∑ j ∈ Finset.range v, (2 : ℝ) * (j : ℝ)) / (n : ℝ) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ ≤ (v : ℝ) ^ 2 / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hn_real).2 hsum_nat
    calc
      |(e : ℝ) * Real.log (1 - c / (n : ℝ)) +
          ∑ j ∈ Finset.range v, -Real.log (1 - (j : ℝ) / (n : ℝ))| ≤
          |(e : ℝ) * Real.log (1 - c / (n : ℝ))| +
            |∑ j ∈ Finset.range v,
              -Real.log (1 - (j : ℝ) / (n : ℝ))| := abs_add_le _ _
      _ ≤ (e : ℝ) * |Real.log (1 - c / (n : ℝ))| +
          ∑ j ∈ Finset.range v,
            |-Real.log (1 - (j : ℝ) / (n : ℝ))| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ e)]
            exact add_le_add_left
              (Finset.abs_sum_le_sum_abs
                (fun j : ℕ ↦ -Real.log (1 - (j : ℝ) / (n : ℝ)))
                (Finset.range v)) _
      _ ≤ (e : ℝ) * (2 * (c / (n : ℝ))) +
          ∑ j ∈ Finset.range v, 2 * ((j : ℝ) / (n : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hc_log (by positivity))
              (Finset.sum_le_sum hj_log)
      _ ≤ 2 * c * (e : ℝ) / (n : ℝ) +
          (v : ℝ) ^ 2 / (n : ℝ) := by
            apply add_le_add
            · ring_nf
              rfl
            · exact hsum_div
  · intro j hj
    exact (inv_pos.mpr (hj_base_pos j hj)).ne'

end LowDegree
