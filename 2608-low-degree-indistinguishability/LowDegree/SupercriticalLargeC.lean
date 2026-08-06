import LowDegree.SupercriticalEnumerationBounds

/-!
# A uniform large-null-density threshold for Appendix A

This module isolates the last parameter choice in the proof of Theorem A.1.
For positive counting constants `K` and `C_A`, one explicit threshold makes
`b = λ² / c` and both geometric ratios from (A.11)--(A.12) strictly smaller
than one, uniformly for every `c` above that threshold.
-/

namespace LowDegree

noncomputable section

/-- An explicit admissible value of the paper's constant `c₀`. -/
noncomputable def appendixLargeCThreshold (lam K C_A : ℝ) : ℝ :=
  max 2 <| max (lam ^ 2 + 1) <|
    max ((2 * K * |lam| + 1) ^ 2)
      (2 * K * C_A * lam ^ 2 + 1)

theorem one_lt_appendixLargeCThreshold (lam K C_A : ℝ) :
    1 < appendixLargeCThreshold lam K C_A := by
  unfold appendixLargeCThreshold
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- Above `appendixLargeCThreshold`, all three strict inequalities used in
the forest/cyclic split hold simultaneously. -/
theorem appendix_largeC_geometric_ratios
    (lam K C_A : ℝ) (hK : 0 < K) (hC_A : 0 < C_A)
    {c : ℝ} (hc : appendixLargeCThreshold lam K C_A ≤ c) :
    0 ≤ lam ^ 2 / c ∧ lam ^ 2 / c < 1 ∧
      0 ≤ 2 * K * Real.sqrt (lam ^ 2 / c) ∧
      2 * K * Real.sqrt (lam ^ 2 / c) < 1 ∧
      0 ≤ 2 * K * C_A * (lam ^ 2 / c) ∧
      2 * K * C_A * (lam ^ 2 / c) < 1 := by
  have htwo : (2 : ℝ) ≤ c :=
    (le_max_left (2 : ℝ)
      (max (lam ^ 2 + 1)
        (max ((2 * K * |lam| + 1) ^ 2)
          (2 * K * C_A * lam ^ 2 + 1)))).trans hc
  have hcpos : 0 < c := by linarith
  have hlamBound : lam ^ 2 + 1 ≤ c := by
    exact (le_max_left (lam ^ 2 + 1)
      (max ((2 * K * |lam| + 1) ^ 2)
        (2 * K * C_A * lam ^ 2 + 1))).trans
      (le_max_right (2 : ℝ) _ |>.trans hc)
  have hforestBound : (2 * K * |lam| + 1) ^ 2 ≤ c := by
    exact (le_max_left ((2 * K * |lam| + 1) ^ 2)
      (2 * K * C_A * lam ^ 2 + 1)).trans
      (le_max_right (lam ^ 2 + 1) _ |>.trans
        (le_max_right (2 : ℝ) _ |>.trans hc))
  have hcyclicBound : 2 * K * C_A * lam ^ 2 + 1 ≤ c := by
    exact (le_max_right ((2 * K * |lam| + 1) ^ 2)
      (2 * K * C_A * lam ^ 2 + 1)).trans
      (le_max_right (lam ^ 2 + 1) _ |>.trans
        (le_max_right (2 : ℝ) _ |>.trans hc))
  have hb0 : 0 ≤ lam ^ 2 / c := div_nonneg (sq_nonneg lam) hcpos.le
  have hb1 : lam ^ 2 / c < 1 := by
    rw [div_lt_one hcpos]
    linarith
  have hqForest0 : 0 ≤ 2 * K * Real.sqrt (lam ^ 2 / c) := by
    positivity
  have hnumForest : (2 * K * |lam|) ^ 2 < c := by
    have ht0 : 0 ≤ 2 * K * |lam| := by positivity
    nlinarith [hforestBound]
  have hqForestSq :
      (2 * K * Real.sqrt (lam ^ 2 / c)) ^ 2 < 1 := by
    have hsqrt : (Real.sqrt (lam ^ 2 / c)) ^ 2 = lam ^ 2 / c :=
      Real.sq_sqrt hb0
    have habs : |lam| ^ 2 = lam ^ 2 := sq_abs lam
    calc
      (2 * K * Real.sqrt (lam ^ 2 / c)) ^ 2 =
          (2 * K * |lam|) ^ 2 / c := by
        rw [mul_pow, hsqrt]
        simp only [mul_pow, div_eq_mul_inv, habs]
        ring
      _ < 1 := (div_lt_one hcpos).2 hnumForest
  have hqForest1 : 2 * K * Real.sqrt (lam ^ 2 / c) < 1 := by
    nlinarith
  have hqCyclic0 : 0 ≤ 2 * K * C_A * (lam ^ 2 / c) := by
    positivity
  have hnumCyclic : 2 * K * C_A * lam ^ 2 < c := by
    linarith
  have hqCyclic1 : 2 * K * C_A * (lam ^ 2 / c) < 1 := by
    calc
      2 * K * C_A * (lam ^ 2 / c) =
          (2 * K * C_A * lam ^ 2) / c := by ring
      _ < 1 := (div_lt_one hcpos).2 hnumCyclic
  exact ⟨hb0, hb1, hqForest0, hqForest1,
    hqCyclic0, hqCyclic1⟩

end

end LowDegree
