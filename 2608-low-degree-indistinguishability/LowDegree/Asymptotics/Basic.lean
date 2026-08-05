import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Asymptotic vocabulary used by the paper

All sequences are indexed by `ℕ` and all limits are at `Filter.atTop`.
Keeping these definitions small makes the translation of `o(1)`,
`1 + o(1)`, and `aₙ = o(bₙ)` explicit in theorem statements.
-/

namespace LowDegree

open Asymptotics Filter Topology

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

/-- An explicit integer scale between two natural-valued sequences.  The
extra `1` makes the scale positive even when `a n = 0`. -/
def intermediateNatScale (a D : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.sqrt (a n * D n) + 1

theorem intermediateNatScale_pos (a D : ℕ → ℕ) (n : ℕ) :
    0 < intermediateNatScale a D n := by
  simp [intermediateNatScale]

/-- Select an integer scale strictly between `a` and `D`.

The divergence hypothesis on `D` is necessary: `a ≡ 0` is little-o of a
bounded positive `D`, but then no positive scale can eventually satisfy
`3 * ℓ ≤ D`.  No pointwise positivity hypothesis on `a` or `D` is needed. -/
theorem exists_intermediateScale_nat
    {a D : ℕ → ℕ}
    (hsmall : LittleO (fun n ↦ (a n : ℝ)) (fun n ↦ (D n : ℝ)))
    (hD : Tendsto D atTop atTop) :
    ∃ ℓ : ℕ → ℕ,
      (∀ n, 0 < ℓ n) ∧
      (∀ᶠ n in atTop, 3 * ℓ n ≤ D n) ∧
      LittleO (fun n ↦ (a n : ℝ)) (fun n ↦ (ℓ n : ℝ)) := by
  let ℓ : ℕ → ℕ := intermediateNatScale a D
  have hsqrt :
      (fun n ↦ Real.sqrt (a n : ℝ)) =o[atTop]
        (fun n ↦ Real.sqrt (D n : ℝ)) :=
    hsmall.sqrt (Filter.Eventually.of_forall fun n ↦ Nat.cast_nonneg (D n))
  have ha_sqrt :
      (fun n ↦ (a n : ℝ)) =o[atTop]
        (fun n ↦ Real.sqrt ((a n * D n : ℕ) : ℝ)) := by
    have hraw := (isBigO_refl (fun n ↦ Real.sqrt (a n : ℝ)) atTop).mul_isLittleO hsqrt
    exact hraw.congr
      (fun n ↦ Real.mul_self_sqrt (Nat.cast_nonneg (a n)))
      (fun n ↦ by
        simp only [Nat.cast_mul]
        exact (Real.sqrt_mul (Nat.cast_nonneg (a n)) (D n : ℝ)).symm)
  have hsqrt_D :
      (fun n ↦ Real.sqrt ((a n * D n : ℕ) : ℝ)) =o[atTop]
        (fun n ↦ (D n : ℝ)) := by
    have hraw := hsqrt.mul_isBigO
      (isBigO_refl (fun n ↦ Real.sqrt (D n : ℝ)) atTop)
    exact hraw.congr
      (fun n ↦ by
        simp only [Nat.cast_mul]
        exact (Real.sqrt_mul (Nat.cast_nonneg (a n)) (D n : ℝ)).symm)
      (fun n ↦ Real.mul_self_sqrt (Nat.cast_nonneg (D n)))
  have ha_ℓ :
      (fun n ↦ (a n : ℝ)) =o[atTop] (fun n ↦ (ℓ n : ℝ)) := by
    apply ha_sqrt.trans_le
    intro n
    have hℓ_nonneg : (0 : ℝ) ≤ (ℓ n : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg hℓ_nonneg]
    simpa only [ℓ, intermediateNatScale, Nat.cast_add, Nat.cast_one] using
      (Real.real_sqrt_le_nat_sqrt_succ (a := a n * D n))
  have hD_real : Tendsto (fun n ↦ (D n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hD
  have hone_D :
      (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n ↦ (D n : ℝ)) := by
    rw [isLittleO_const_left_of_ne one_ne_zero]
    exact hD_real.congr' <| Filter.Eventually.of_forall fun n ↦
      (Real.norm_of_nonneg (Nat.cast_nonneg (D n))).symm
  have hℓ_sqrt_add :
      (fun n ↦ (ℓ n : ℝ)) =O[atTop]
        (fun n ↦ Real.sqrt ((a n * D n : ℕ) : ℝ) + 1) := by
    apply Filter.Eventually.isBigO
    exact Filter.Eventually.of_forall fun n ↦ by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg (ℓ n))]
      simpa only [ℓ, intermediateNatScale, Nat.cast_add, Nat.cast_one] using
        add_le_add_right
          (Real.nat_sqrt_le_real_sqrt (a := a n * D n)) 1
  have hℓ_D :
      (fun n ↦ (ℓ n : ℝ)) =o[atTop] (fun n ↦ (D n : ℝ)) :=
    hℓ_sqrt_add.trans_isLittleO (hsqrt_D.add hone_D)
  have hthird := hℓ_D.bound (by norm_num : (0 : ℝ) < 1 / 3)
  have hthree : ∀ᶠ n in atTop, 3 * ℓ n ≤ D n := by
    filter_upwards [hthird] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg (ℓ n)),
      Real.norm_of_nonneg (Nat.cast_nonneg (D n))] at hn
    have hreal : (3 : ℝ) * (ℓ n : ℝ) ≤ (D n : ℝ) := by
      nlinarith
    exact_mod_cast hreal
  exact ⟨ℓ, fun n ↦ intermediateNatScale_pos a D n, hthree, ha_ℓ⟩

/-- The real scale in `TreewidthDegreeScale` rounded upward to a natural
number. -/
noncomputable def treewidthLogEnvelope (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌈((k n : ℝ) + 1) * Real.log (n : ℝ)⌉₊

theorem treewidthLogEnvelope_majorizes (k : ℕ → ℕ) (n : ℕ) :
    ((k n : ℝ) + 1) * Real.log (n : ℝ) ≤
      (treewidthLogEnvelope k n : ℝ) := by
  exact Nat.le_ceil _

/-- The paper's scale hypothesis forces the degree cutoff to diverge, so the
generic intermediate-scale selector needs no extra assumption in the main
application. -/
theorem TreewidthDegreeScale.degree_tendsto_atTop
    {k D : ℕ → ℕ} (h : TreewidthDegreeScale k D) :
    Tendsto D atTop atTop := by
  have hbound := h.log_isLittleO.bound one_pos
  have hle :
      ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (D n : ℝ) := by
    filter_upwards [hbound] with n hn
    rw [Real.norm_of_nonneg (Real.log_natCast_nonneg n),
      Real.norm_of_nonneg (Nat.cast_nonneg (D n)), one_mul] at hn
    exact hn
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hDreal : Tendsto (fun n ↦ (D n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hle hlog
  exact tendsto_natCast_atTop_iff.mp hDreal

/-- Paper Lemma 4.5's intermediate-scale selection.

Starting only from `(kₙ+1) log n = o(Dₙ)`, this produces positive integers
`ℓₙ` with `3ℓₙ ≤ Dₙ` eventually and
`(kₙ+1) log n = o(ℓₙ)`. -/
theorem TreewidthDegreeScale.exists_intermediateScale
    {k D : ℕ → ℕ} (h : TreewidthDegreeScale k D) :
    ∃ ℓ : ℕ → ℕ,
      (∀ n, 0 < ℓ n) ∧
      (∀ᶠ n in atTop, 3 * ℓ n ≤ D n) ∧
      LittleO
        (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ))
        (fun n ↦ (ℓ n : ℝ)) := by
  let a : ℕ → ℕ := treewidthLogEnvelope k
  have hDtop : Tendsto D atTop atTop := h.degree_tendsto_atTop
  have hDreal : Tendsto (fun n ↦ (D n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDtop
  have hone_D :
      (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n ↦ (D n : ℝ)) := by
    rw [isLittleO_const_left_of_ne one_ne_zero]
    exact hDreal.congr' <| Filter.Eventually.of_forall fun n ↦
      (Real.norm_of_nonneg (Nat.cast_nonneg (D n))).symm
  have ha_bigO :
      (fun n ↦ (a n : ℝ)) =O[atTop]
        (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ) + 1) := by
    apply Filter.Eventually.isBigO
    exact Filter.Eventually.of_forall fun n ↦ by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg (a n))]
      have hx_nonneg :
          0 ≤ ((k n : ℝ) + 1) * Real.log (n : ℝ) :=
        mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
      simpa only [a, treewidthLogEnvelope] using
        (Nat.ceil_lt_add_one hx_nonneg).le
  have ha_small :
      LittleO (fun n ↦ (a n : ℝ)) (fun n ↦ (D n : ℝ)) :=
    ha_bigO.trans_isLittleO (h.add hone_D)
  rcases exists_intermediateScale_nat ha_small hDtop with
    ⟨ℓ, hℓpos, hthree, haℓ⟩
  have hx_bigO :
      (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ)) =O[atTop]
        (fun n ↦ (a n : ℝ)) := by
    apply Filter.Eventually.isBigO
    exact Filter.Eventually.of_forall fun n ↦ by
      have hx_nonneg :
          0 ≤ ((k n : ℝ) + 1) * Real.log (n : ℝ) :=
        mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
      rw [Real.norm_of_nonneg hx_nonneg]
      simpa only [a] using treewidthLogEnvelope_majorizes k n
  exact ⟨ℓ, hℓpos, hthree, hx_bigO.trans_isLittleO haℓ⟩

end LowDegree
