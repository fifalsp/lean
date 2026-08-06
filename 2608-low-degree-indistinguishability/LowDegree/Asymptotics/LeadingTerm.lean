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
open Filter Topology Asymptotics

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

/-! ## Uniform form of paper Lemma 3.1 -/

/-- Numerical data carried by a nonempty graph without isolated vertices
that occurs as a subgraph of an ambient graph on `n` vertices.  Keeping this
small arithmetic interface separate from a particular graph representation
lets the uniform estimate be reused by both deterministic and randomized
plant models. -/
structure LeadingTermDatum (n : ℕ) where
  edgeCount : ℕ
  vertexCount : ℕ
  copyCount : ℕ
  autCount : ℕ
  edgeCount_pos : 0 < edgeCount
  vertexCount_le_twice_edges : vertexCount ≤ 2 * edgeCount
  vertexCount_le_ambient : vertexCount ≤ n
  copyCount_pos : 0 < copyCount
  autCount_pos : 0 < autCount

/-- Uniform convergence to one on a changing family of finite objects.  This
is the quantifier order intended by the word "uniformly" in paper Lemma 3.1. -/
def UniformlyTendsToOneOn
    {ι : ℕ → Type*}
    (f : (n : ℕ) → ι n → ℝ) (admissible : (n : ℕ) → ι n → Prop) : Prop :=
  ∀ δ > 0, ∀ᶠ n in atTop, ∀ x, admissible n x → |f n x - 1| < δ

/-- The two error terms in the logarithmic estimate vanish when
`dₙ = o(√n)`. -/
private theorem leadingError_tendsto_zero
    {d : ℕ → ℕ}
    (hd : (fun n : ℕ ↦ (d n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)))
    (c : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        2 * c * (d n : ℝ) / (n : ℝ) +
          (2 * (d n : ℝ)) ^ 2 / (n : ℝ))
      atTop (𝓝 0) := by
  have hquot : Tendsto
      (fun n : ℕ ↦ (d n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
    hd.tendsto_div_nhds_zero
  have hlinear : Tendsto
      (fun n : ℕ ↦ (d n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
      have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_real
      have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
        rw [Real.sqrt_le_iff]
        constructor
        · exact hn_real.le
        · have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
      exact div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt_le
    · exact hquot
  have hquadratic : Tendsto
      (fun n : ℕ ↦ (d n : ℝ) ^ 2 / (n : ℝ))
      atTop (𝓝 0) := by
    have hsquare : Tendsto
        (fun n : ℕ ↦ ((d n : ℝ) / Real.sqrt (n : ℝ)) ^ 2)
        atTop (𝓝 0) := by
      simpa using hquot.pow 2
    simpa only using hsquare.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      rw [div_pow, Real.sq_sqrt hn_nonneg])
  have hfirst : Tendsto
      (fun n : ℕ ↦ 2 * c * ((d n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hlinear.const_mul (2 * c)
  have hsecond : Tendsto
      (fun n : ℕ ↦ 4 * ((d n : ℝ) ^ 2 / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hquadratic
  convert hfirst.add hsecond using 1 <;> ring

/-- **Uniform scalar heart of paper Lemma 3.1.**

For every changing family of graph data with at most `dₙ` edges, where
`dₙ = o(√n)`, the exact-to-leading ratio `αₙ/βₙ` tends uniformly to one.
The graph-facing specialization only has to package the ordinary facts that
a nonempty graph without isolated vertices has `v ≤ 2e`, that an occurring
copy has positive copy count, and that an automorphism group is nonempty. -/
theorem alpha_div_beta_tendsto_uniformly
    {d : ℕ → ℕ}
    (c : ℝ) (hc : 0 < c)
    (hd : (fun n : ℕ ↦ (d n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ))) :
    UniformlyTendsToOneOn
      (fun n (F : LeadingTermDatum n) ↦
        alphaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount /
          betaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount)
      (fun n F ↦ F.edgeCount ≤ d n) := by
  let error : ℕ → ℝ := fun n ↦
    2 * c * (d n : ℝ) / (n : ℝ) +
      (2 * (d n : ℝ)) ^ 2 / (n : ℝ)
  have herror : Tendsto error atTop (𝓝 0) :=
    leadingError_tendsto_zero hd c
  have hdegree : Tendsto
      (fun n : ℕ ↦ 2 * (d n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hlinear : Tendsto
        (fun n : ℕ ↦ (d n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      have hquot : Tendsto
          (fun n : ℕ ↦ (d n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
        hd.tendsto_div_nhds_zero
      apply squeeze_zero'
      · exact Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity)
      · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
        have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_real
        have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
          rw [Real.sqrt_le_iff]
          constructor
          · exact hn_real.le
          · have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith
        exact div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt_le
      · exact hquot
    simpa only [mul_div_assoc, mul_zero] using hlinear.const_mul (2 : ℝ)
  have hcquot : Tendsto (fun n : ℕ ↦ c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  intro δ hδ
  have hsmall : ∀ᶠ n : ℕ in atTop, |error n| < min 1 (δ / 2) := by
    have hdist :=
      (Metric.tendsto_nhds.1 herror) _ (lt_min zero_lt_one (half_pos hδ))
    filter_upwards [hdist] with n hn
    simpa [Real.dist_eq] using hn
  have hdegree_half : ∀ᶠ n in atTop,
      2 * (d n : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    have h : ∀ᶠ n : ℕ in atTop,
        dist (2 * (d n : ℝ) / (n : ℝ)) 0 < (1 / 2 : ℝ) :=
      (Metric.tendsto_nhds.1 hdegree) _ (by norm_num)
    filter_upwards [h] with n hn
    have hnonneg : 0 ≤ 2 * (d n : ℝ) / (n : ℝ) := by positivity
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hn.le
  have hc_half : ∀ᶠ n : ℕ in atTop, c / (n : ℝ) ≤ 1 / 2 := by
    have h : ∀ᶠ n : ℕ in atTop, dist (c / (n : ℝ)) 0 < (1 / 2 : ℝ) :=
      (Metric.tendsto_nhds.1 hcquot) _ (by norm_num)
    filter_upwards [h] with n hn
    have habs : |c / (n : ℝ)| ≤ (1 / 2 : ℝ) := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      simpa [Real.dist_eq] using hn.le
    exact le_trans (le_abs_self _) habs
  filter_upwards [hsmall, hdegree_half, hc_half,
    eventually_ge_atTop (1 : ℕ)] with n hnsmall hd_half hc_half hn F hFed
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hdn_nonneg : 0 ≤ (d n : ℝ) := by positivity
  have herror_nonneg : 0 ≤ error n := by
    dsimp [error]
    positivity
  have herror_lt_one : error n < 1 := by
    have habs_lt : |error n| < 1 := lt_of_lt_of_le hnsmall (min_le_left _ _)
    simpa [abs_of_nonneg herror_nonneg] using habs_lt
  have herror_lt_half_delta : error n < δ / 2 := by
    have habs_lt : |error n| < δ / 2 := lt_of_lt_of_le hnsmall (min_le_right _ _)
    simpa [abs_of_nonneg herror_nonneg] using habs_lt
  have hFv_half : (F.vertexCount : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    have hv_le : F.vertexCount ≤ 2 * d n :=
      le_trans F.vertexCount_le_twice_edges (Nat.mul_le_mul_left 2 hFed)
    exact le_trans
      ((div_le_div_iff_of_pos_right hn_real).2 (by exact_mod_cast hv_le))
      hd_half
  have hratio_pos : 0 < leadingRatio c n F.edgeCount F.vertexCount :=
    leadingRatio_pos hn hc.le (lt_of_le_of_lt hc_half (by norm_num))
      F.vertexCount_le_ambient
  have hlog_bound :
      |Real.log (leadingRatio c n F.edgeCount F.vertexCount)| ≤ error n := by
    refine le_trans (abs_log_leadingRatio_le hn hc.le hc_half
      F.vertexCount_le_ambient hFv_half) ?_
    dsimp [error]
    have he_le : (F.edgeCount : ℝ) ≤ d n := by exact_mod_cast hFed
    have hv_le : (F.vertexCount : ℝ) ≤ 2 * (d n : ℝ) := by
      exact_mod_cast le_trans F.vertexCount_le_twice_edges
        (Nat.mul_le_mul_left 2 hFed)
    have hfirst : 2 * c * (F.edgeCount : ℝ) / (n : ℝ) ≤
        2 * c * (d n : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hn_real).2
        (mul_le_mul_of_nonneg_left he_le (by positivity))
    have hsecond : (F.vertexCount : ℝ) ^ 2 / (n : ℝ) ≤
        (2 * (d n : ℝ)) ^ 2 / (n : ℝ) := by
      apply (div_le_div_iff_of_pos_right hn_real).2
      nlinarith [sq_nonneg (F.vertexCount : ℝ), sq_nonneg (2 * (d n : ℝ))]
    exact add_le_add hfirst hsecond
  have hlog_one : |Real.log (leadingRatio c n F.edgeCount F.vertexCount)| ≤ 1 :=
    le_trans hlog_bound herror_lt_one.le
  have hratio_eq :
      alphaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount /
          betaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount =
        leadingRatio c n F.edgeCount F.vertexCount :=
    alpha_div_beta_exact hc.ne' (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
      F.vertexCount_le_ambient
      F.copyCount_pos.ne' F.autCount_pos.ne'
  rw [hratio_eq, ← Real.exp_log hratio_pos]
  calc
    |Real.exp (Real.log (leadingRatio c n F.edgeCount F.vertexCount)) - 1| ≤
        2 * |Real.log (leadingRatio c n F.edgeCount F.vertexCount)| :=
      Real.abs_exp_sub_one_le hlog_one
    _ ≤ 2 * error n := mul_le_mul_of_nonneg_left hlog_bound (by norm_num)
    _ < δ := by linarith

/-- Eventual multiplicative comparison, the second conclusion of paper
Lemma 3.1. -/
theorem alpha_beta_eventually_between_half_and_two
    {d : ℕ → ℕ}
    (c : ℝ) (hc : 0 < c)
    (hd : (fun n : ℕ ↦ (d n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ))) :
    ∀ᶠ n in atTop, ∀ F : LeadingTermDatum n, F.edgeCount ≤ d n →
      (1 / 2 : ℝ) * betaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount ≤
          alphaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount ∧
        alphaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount ≤
          2 * betaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount := by
  have huniform := alpha_div_beta_tendsto_uniformly c hc hd
  have hhalf := huniform (1 / 2) (by norm_num)
  filter_upwards [hhalf, eventually_ge_atTop (1 : ℕ)] with n hhalf_n hn
  intro F hFed
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hcopy_real : (0 : ℝ) < F.copyCount := by exact_mod_cast F.copyCount_pos
  have haut_real : (0 : ℝ) < F.autCount := by exact_mod_cast F.autCount_pos
  have hbeta_pos : 0 < betaWeight c n F.edgeCount F.vertexCount
      F.copyCount F.autCount := by
    dsimp [betaWeight]
    positivity
  specialize hhalf_n F hFed
  have hratio_eq := alpha_div_beta_exact (e := F.edgeCount) hc.ne'
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    F.vertexCount_le_ambient F.copyCount_pos.ne' F.autCount_pos.ne'
  rw [hratio_eq] at hhalf_n
  have hlower : (1 / 2 : ℝ) < leadingRatio c n F.edgeCount F.vertexCount := by
    rw [abs_lt] at hhalf_n
    linarith
  have hupper : leadingRatio c n F.edgeCount F.vertexCount < (3 / 2 : ℝ) := by
    rw [abs_lt] at hhalf_n
    linarith
  have halpha_eq : alphaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount =
      leadingRatio c n F.edgeCount F.vertexCount *
        betaWeight c n F.edgeCount F.vertexCount F.copyCount F.autCount := by
    apply (div_eq_iff hbeta_pos.ne').mp
    exact hratio_eq
  rw [halpha_eq]
  constructor
  · exact mul_le_mul_of_nonneg_right hlower.le hbeta_pos.le
  · exact mul_le_mul_of_nonneg_right (le_trans hupper.le (by norm_num)) hbeta_pos.le

/-! ## Degree-one consequence (paper Lemma 3.2) -/

/-- The leading weight of `K₂` is a positive constant times the square of
the edge count normalized by `√n`. -/
theorem betaWeight_edge_eq_normalized_sq
    {c : ℝ} (hc : 0 < c) {n edgeCount : ℕ} (hn : 0 < n) :
    betaWeight c n 1 2 edgeCount 2 =
      (2 / c) * ((edgeCount : ℝ) / Real.sqrt (n : ℝ)) ^ 2 := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hn_real.le
  dsimp [betaWeight]
  rw [div_pow, hsqrt_sq]
  field_simp

/-- If the leading `K₂` mass vanishes, the number of plant edges is
`o(√n)`. -/
theorem edgeCount_isLittleO_sqrt_of_betaEdge_vanishes
    {c : ℝ} (hc : 0 < c) {edgeCount : ℕ → ℕ}
    (hbeta : Vanishes
      (fun n ↦ betaWeight c n 1 2 (edgeCount n) 2)) :
    (fun n : ℕ ↦ (edgeCount n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  let q : ℕ → ℝ := fun n ↦
    (edgeCount n : ℝ) / Real.sqrt (n : ℝ)
  have hsquare : Tendsto (fun n ↦ (q n) ^ 2) atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n ↦ (c / 2) * betaWeight c n 1 2 (edgeCount n) 2)
        atTop (𝓝 0) := by
      simpa using hbeta.const_mul (c / 2)
    apply hscaled.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [betaWeight_edge_eq_normalized_sq hc
      (lt_of_lt_of_le Nat.zero_lt_one hn)]
    dsimp [q]
    field_simp
  have hq : Tendsto q atTop (𝓝 0) := by
    have hq_nonneg : ∀ n, 0 ≤ q n := by
      intro n
      dsimp [q]
      positivity
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    have habs : Tendsto (fun n ↦ |q n|) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
    exact habs.congr' (Eventually.of_forall fun n ↦ abs_of_nonneg (hq_nonneg n))
  apply (isLittleO_iff_tendsto' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hzero
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact (hsqrt_pos.ne' hzero).elim)).2
  exact hq

/-- **Scalar Fourier form of paper Lemma 3.2.**

The model-facing Fourier identity supplies `hK2`: degree one is included and
the nonnegative `K₂` leading mass is bounded by twice the excess projected
second moment.  The remaining implication to `e(Γₙ)=o(√n)` is fully analytic. -/
theorem edgeCount_isLittleO_sqrt
    {c : ℝ} (hc : 0 < c) {edgeCount : ℕ → ℕ}
    {lowDegreeNormSq : ℕ → ℝ}
    (hlow : TendsToOne lowDegreeNormSq)
    (hK2 : ∀ᶠ n in atTop,
      betaWeight c n 1 2 (edgeCount n) 2 ≤
        2 * (lowDegreeNormSq n - 1)) :
    (fun n : ℕ ↦ (edgeCount n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  have hright : Tendsto
      (fun n ↦ 2 * (lowDegreeNormSq n - 1)) atTop (𝓝 0) := by
    simpa using (hlow.sub_one.const_mul 2)
  have hnonneg : ∀ n,
      0 ≤ betaWeight c n 1 2 (edgeCount n) 2 := by
    intro n
    dsimp [betaWeight]
    positivity
  have hbeta : Vanishes
      (fun n ↦ betaWeight c n 1 2 (edgeCount n) 2) :=
    squeeze_zero' (Eventually.of_forall hnonneg) hK2 hright
  exact edgeCount_isLittleO_sqrt_of_betaEdge_vanishes hc hbeta

end LowDegree
