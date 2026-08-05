import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Asymptotic vocabulary used by the paper

All sequences are indexed by `ℕ` and all limits are at `Filter.atTop`.
Keeping these definitions small makes the translation of `o(1)`,
`1 + o(1)`, and `aₙ = o(bₙ)` explicit in theorem statements.
-/

namespace LowDegree

open Filter Topology

/-- The paper's notation `xₙ = o(1)`. -/
def Vanishes (x : ℕ → ℝ) : Prop := Tendsto x atTop (𝓝 0)

/-- The paper's notation `xₙ = 1 + o(1)`. -/
def TendsToOne (x : ℕ → ℝ) : Prop := Tendsto x atTop (𝓝 1)

/-- The paper's notation `aₙ = o(bₙ)`. -/
def LittleO (a b : ℕ → ℝ) : Prop := a =o[atTop] b

/-- The paper's notation `aₙ = ω(bₙ)`, expressed without division. -/
def Omega (a b : ℕ → ℝ) : Prop := b =o[atTop] a

/-- A fixed edge-resampling rate `ε ∈ (0,1)`.

Quantifying `ε : NoiseRate` outside a `Tendsto` statement records the
pointwise quantifier order in the paper: first fix `ε`, then send `n → ∞`.
-/
abbrev NoiseRate := Set.Ioo (0 : ℝ) 1

/-- The scale hypothesis `(kₙ + 1) log n = o(Dₙ)` from Theorem 1.1.

The casts are part of the definition: treewidth bounds and degree cutoffs are
natural numbers, while asymptotic comparison takes place in `ℝ`.
-/
def TreewidthDegreeScale (k D : ℕ → ℕ) : Prop :=
  LittleO
    (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ))
    (fun n ↦ (D n : ℝ))

theorem vanishes_iff_tendsto {x : ℕ → ℝ} :
    Vanishes x ↔ Tendsto x atTop (𝓝 0) := Iff.rfl

theorem tendsToOne_iff_vanishes_sub {x : ℕ → ℝ} :
    TendsToOne x ↔ Vanishes (fun n ↦ x n - 1) := by
  simp only [TendsToOne, Vanishes]
  constructor
  · intro h
    simpa using h.sub_const 1
  · intro h
    have := h.add_const 1
    simpa [sub_add_cancel] using this

theorem tendsToOne_iff_one_add_vanishes {x : ℕ → ℝ} :
    TendsToOne x ↔ ∃ r, Vanishes r ∧ x = fun n ↦ 1 + r n := by
  constructor
  · intro hx
    refine ⟨fun n ↦ x n - 1, (tendsToOne_iff_vanishes_sub.mp hx), ?_⟩
    funext n
    ring
  · rintro ⟨r, hr, rfl⟩
    change Tendsto (fun n ↦ (1 : ℝ) + r n) atTop (𝓝 1)
    change Tendsto r atTop (𝓝 0) at hr
    simpa only [add_zero] using (tendsto_const_nhds.add hr :
      Tendsto (fun n ↦ (1 : ℝ) + r n) atTop (𝓝 ((1 : ℝ) + 0)))

theorem Vanishes.add {x y : ℕ → ℝ} (hx : Vanishes x) (hy : Vanishes y) :
    Vanishes (fun n ↦ x n + y n) := by
  change Tendsto x atTop (𝓝 0) at hx
  change Tendsto y atTop (𝓝 0) at hy
  change Tendsto (fun n ↦ x n + y n) atTop (𝓝 0)
  simpa only [add_zero] using (Filter.Tendsto.add hx hy)

theorem Vanishes.const_mul (a : ℝ) {x : ℕ → ℝ} (hx : Vanishes x) :
    Vanishes (fun n ↦ a * x n) := by
  change Tendsto x atTop (𝓝 0) at hx
  change Tendsto (fun n ↦ a * x n) atTop (𝓝 0)
  simpa only [mul_zero] using (tendsto_const_nhds.mul hx :
    Tendsto (fun n ↦ a * x n) atTop (𝓝 (a * 0)))

theorem TendsToOne.sub_one {x : ℕ → ℝ} (hx : TendsToOne x) :
    Vanishes (fun n ↦ x n - 1) := tendsToOne_iff_vanishes_sub.mp hx

theorem Vanishes.one_add {x : ℕ → ℝ} (hx : Vanishes x) :
    TendsToOne (fun n ↦ 1 + x n) := by
  change Tendsto x atTop (𝓝 0) at hx
  change Tendsto (fun n ↦ (1 : ℝ) + x n) atTop (𝓝 1)
  simpa only [add_zero] using (tendsto_const_nhds.add hx :
    Tendsto (fun n ↦ (1 : ℝ) + x n) atTop (𝓝 ((1 : ℝ) + 0)))

/-- The manuscript's treewidth/degree scale condition implies
`log n = o(Dₙ)`.  This is the precise content of the sentence following
Theorem 1.1 that the condition automatically gives `Dₙ = ω(log n)`.
-/
theorem TreewidthDegreeScale.log_isLittleO {k D : ℕ → ℕ}
    (h : TreewidthDegreeScale k D) :
    LittleO (fun n ↦ Real.log (n : ℝ)) (fun n ↦ (D n : ℝ)) := by
  apply (show (fun n : ℕ ↦ Real.log (n : ℝ)) =O[atTop]
      (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ)) from ?_).trans_isLittleO h
  apply Filter.Eventually.isBigO
  exact Filter.Eventually.of_forall fun n ↦ by
    have hk : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg (k n)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hlog]
    nlinarith

/-- Equivalent `ω`-notation for `TreewidthDegreeScale.log_isLittleO`. -/
theorem TreewidthDegreeScale.degree_isOmega_log {k D : ℕ → ℕ}
    (h : TreewidthDegreeScale k D) :
    Omega (fun n ↦ (D n : ℝ)) (fun n ↦ Real.log (n : ℝ)) :=
  h.log_isLittleO

end LowDegree
