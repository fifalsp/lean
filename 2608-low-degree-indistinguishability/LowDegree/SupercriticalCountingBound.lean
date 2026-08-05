import LowDegree.SupercriticalLargeC
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Uniform graph-counting bound for Appendix A

The labelled-graph factor in (A.9) is bounded here before the local-density
restriction is applied.  The only remaining nonconstant factor is
`v^(e-v)`, exactly the excess factor controlled by (A.7).
-/

namespace LowDegree

noncomputable section

open scoped BigOperators

/-- The graph-enumeration coefficient appearing in (A.9). -/
noncomputable def appendixGraphCountingFactor (v e : ℕ) : ℝ :=
  ((v.choose 2).choose e : ℝ) / (v.factorial : ℝ)

/-- A uniform exponential bound for the graph-enumeration coefficient.

The hypotheses are precisely the paper's elementary range
`v/2 ≤ e ≤ 2v`.  The factor `v^(e-v)` is one in the forest range and is the
only excess-dependent factor in the cyclic range. -/
theorem appendixGraphCountingFactor_le
    {v e : ℕ} (hv : 1 ≤ v) (hlower : v ≤ 2 * e)
    (hupper : e ≤ 2 * v) :
    appendixGraphCountingFactor v e ≤
      (4 * Real.exp 3) ^ v * (v : ℝ) ^ (e - v) := by
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hfacV : (0 : ℝ) < v.factorial := by positivity
  have hfacE : (0 : ℝ) < e.factorial := by positivity
  have hedgeSlots : ((v.choose 2 : ℕ) : ℝ) ≤ (v : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow v 2
  have hchoose : (((v.choose 2).choose e : ℕ) : ℝ) ≤
      ((v : ℝ) ^ 2) ^ e / (e.factorial : ℝ) := by
    calc
      (((v.choose 2).choose e : ℕ) : ℝ) ≤
          (((v.choose 2 : ℕ) : ℝ) ^ e) / (e.factorial : ℝ) :=
        Nat.choose_le_pow_div e (v.choose 2)
      _ ≤ ((v : ℝ) ^ 2) ^ e / (e.factorial : ℝ) := by
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hedgeSlots e) hfacE.le
  have hsplit :
      (((v : ℝ) ^ 2) ^ e / (e.factorial : ℝ)) /
          (v.factorial : ℝ) =
        ((v : ℝ) ^ e / (e.factorial : ℝ)) *
          ((v : ℝ) ^ e / (v.factorial : ℝ)) := by
    rw [← pow_mul]
    field_simp
    ring
  have hfirst :
      (v : ℝ) ^ e / (e.factorial : ℝ) ≤
        2 ^ e * Real.exp (e : ℝ) := by
    have hve : (v : ℝ) ≤ 2 * (e : ℝ) := by exact_mod_cast hlower
    have hpow : (v : ℝ) ^ e ≤ (2 * (e : ℝ)) ^ e :=
      pow_le_pow_left₀ hv0 hve e
    calc
      (v : ℝ) ^ e / (e.factorial : ℝ) ≤
          (2 * (e : ℝ)) ^ e / (e.factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow hfacE.le
      _ = 2 ^ e * ((e : ℝ) ^ e / (e.factorial : ℝ)) := by
        rw [mul_pow]
        ring
      _ ≤ 2 ^ e * Real.exp (e : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.pow_div_factorial_le_exp (x := (e : ℝ)) he0 e)
          (by positivity)
  have hsecond :
      (v : ℝ) ^ e / (v.factorial : ℝ) ≤
        (v : ℝ) ^ (e - v) * Real.exp (v : ℝ) := by
    by_cases hev : e ≤ v
    · have hpow : (v : ℝ) ^ e ≤ (v : ℝ) ^ v :=
        pow_le_pow_right₀ hv1 hev
      have hexp := Real.pow_div_factorial_le_exp (x := (v : ℝ)) hv0 v
      rw [Nat.sub_eq_zero_of_le hev, pow_zero, one_mul]
      exact (div_le_div_of_nonneg_right hpow hfacV.le).trans hexp
    · have hve : v ≤ e := Nat.le_of_not_ge hev
      have hpowEq : (v : ℝ) ^ e =
          (v : ℝ) ^ (e - v) * (v : ℝ) ^ v := by
        rw [mul_comm, ← pow_add, Nat.add_sub_of_le hve]
      rw [hpowEq]
      have hexp := Real.pow_div_factorial_le_exp (x := (v : ℝ)) hv0 v
      calc
        (v : ℝ) ^ (e - v) * (v : ℝ) ^ v /
            (v.factorial : ℝ) =
            (v : ℝ) ^ (e - v) *
              ((v : ℝ) ^ v / (v.factorial : ℝ)) := by ring
        _ ≤ (v : ℝ) ^ (e - v) * Real.exp (v : ℝ) :=
          mul_le_mul_of_nonneg_left hexp (pow_nonneg hv0 _)
  have hraw : appendixGraphCountingFactor v e ≤
      (2 ^ e * Real.exp (e : ℝ)) *
        ((v : ℝ) ^ (e - v) * Real.exp (v : ℝ)) := by
    unfold appendixGraphCountingFactor
    calc
      (((v.choose 2).choose e : ℕ) : ℝ) / (v.factorial : ℝ) ≤
          (((v : ℝ) ^ 2) ^ e / (e.factorial : ℝ)) /
            (v.factorial : ℝ) :=
        div_le_div_of_nonneg_right hchoose hfacV.le
      _ = ((v : ℝ) ^ e / (e.factorial : ℝ)) *
          ((v : ℝ) ^ e / (v.factorial : ℝ)) := hsplit
      _ ≤ (2 ^ e * Real.exp (e : ℝ)) *
          ((v : ℝ) ^ (e - v) * Real.exp (v : ℝ)) :=
        mul_le_mul hfirst hsecond
          (div_nonneg (pow_nonneg hv0 _) hfacV.le)
          (mul_nonneg (by positivity) (Real.exp_pos _).le)
  have htwoPow : (2 : ℝ) ^ e ≤ 4 ^ v := by
    calc
      (2 : ℝ) ^ e ≤ 2 ^ (2 * v) :=
        pow_le_pow_right₀ (by norm_num) hupper
      _ = 4 ^ v := by rw [pow_mul]; norm_num
  have hExp : Real.exp (e : ℝ) * Real.exp (v : ℝ) ≤
      (Real.exp 3) ^ v := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact_mod_cast (show e + v ≤ v * 3 by omega)
  calc
    appendixGraphCountingFactor v e ≤
        (2 ^ e * Real.exp (e : ℝ)) *
          ((v : ℝ) ^ (e - v) * Real.exp (v : ℝ)) := hraw
    _ = (2 ^ e * (Real.exp (e : ℝ) * Real.exp (v : ℝ))) *
          (v : ℝ) ^ (e - v) := by ring
    _ ≤ (4 ^ v * (Real.exp 3) ^ v) *
          (v : ℝ) ^ (e - v) := by
      gcongr
    _ = (4 * Real.exp 3) ^ v * (v : ℝ) ^ (e - v) := by
      rw [mul_pow]

end

end LowDegree
