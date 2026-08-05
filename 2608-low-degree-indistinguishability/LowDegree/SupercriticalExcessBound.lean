import LowDegree.SupercriticalCountingBound

/-!
# The local-sparsity excess bound in Appendix A

This is the elementary estimate behind the constant `C_A` in (A.12).  It
is intentionally stated for arbitrary finite parameters so the final proof
can instantiate it directly after extracting (A.7).
-/

namespace LowDegree

noncomputable section

/-- If `e ≤ (1 + A / log n)v`, then the potentially dangerous factor
`(v/a)^(e-v)`, with `a=m²/n`, is uniformly exponential in `v`.

The deliberately coarse bound `v/a ≤ n²` only uses `m≥1` and `v≤n`; it is
more than sufficient for choosing a constant geometric base. -/
theorem appendix_excess_power_le
    (A : ℝ) {n m v e : ℕ}
    (hn : 1 < n) (hm : 1 ≤ m)
    (hv : v ≤ n) (hve : v ≤ e)
    (hexcess : (e : ℝ) ≤
      (1 + A / Real.log (n : ℝ)) * (v : ℝ)) :
    ((v : ℝ) / ((m : ℝ) ^ 2 / (n : ℝ))) ^ (e - v) ≤
      (Real.exp (2 * A)) ^ v := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have haPos : 0 < (m : ℝ) ^ 2 / (n : ℝ) := by positivity
  have hvreal : (v : ℝ) ≤ n := by exact_mod_cast hv
  have hbase :
      (v : ℝ) / ((m : ℝ) ^ 2 / (n : ℝ)) ≤ (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ haPos]
    calc
      (v : ℝ) ≤ n := hvreal
      _ ≤ (n : ℝ) * (m : ℝ) ^ 2 :=
        (le_mul_iff_one_le_right hnpos).2 hmsq
      _ = (n : ℝ) ^ 2 * ((m : ℝ) ^ 2 / (n : ℝ)) := by
        field_simp
  have hbase0 : 0 ≤
      (v : ℝ) / ((m : ℝ) ^ 2 / (n : ℝ)) := by positivity
  have hpowBase :
      ((v : ℝ) / ((m : ℝ) ^ 2 / (n : ℝ))) ^ (e - v) ≤
        ((n : ℝ) ^ 2) ^ (e - v) :=
    pow_le_pow_left₀ hbase0 hbase (e - v)
  have hk : ((e - v : ℕ) : ℝ) ≤
      A / Real.log (n : ℝ) * (v : ℝ) := by
    rw [Nat.cast_sub hve]
    linarith
  have hklog : ((e - v : ℕ) : ℝ) * Real.log (n : ℝ) ≤
      A * (v : ℝ) := by
    calc
      ((e - v : ℕ) : ℝ) * Real.log (n : ℝ) ≤
          (A / Real.log (n : ℝ) * (v : ℝ)) *
            Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hk hlogpos.le
      _ = A * (v : ℝ) := by field_simp
  have hlogSquare : Real.log ((n : ℝ) ^ 2) =
      2 * Real.log (n : ℝ) := by
    rw [pow_two, Real.log_mul hnpos.ne' hnpos.ne']
    ring
  have hexponent :
      Real.log ((n : ℝ) ^ 2) * ((e - v : ℕ) : ℝ) ≤
        (2 * A) * (v : ℝ) := by
    rw [hlogSquare]
    nlinarith
  have hnSquarePos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hpowSquare :
      ((n : ℝ) ^ 2) ^ (e - v) ≤ (Real.exp (2 * A)) ^ v := by
    calc
      ((n : ℝ) ^ 2) ^ (e - v) =
          ((n : ℝ) ^ 2) ^ (((e - v : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = Real.exp (Real.log ((n : ℝ) ^ 2) *
          ((e - v : ℕ) : ℝ)) :=
        Real.rpow_def_of_pos hnSquarePos _
      _ ≤ Real.exp ((2 * A) * (v : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = (Real.exp (2 * A)) ^ v := by
        rw [← Real.exp_nat_mul]
        ring
  exact hpowBase.trans hpowSquare

end

end LowDegree
