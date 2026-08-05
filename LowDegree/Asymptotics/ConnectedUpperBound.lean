import LowDegree.Asymptotics.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic estimates for the connected noised mass

This file formalizes the asymptotic part of paper Lemma 4.5.  The finite
graph-class layer supplies the small/large decomposition inequalities; the
results here prove the uniform domination of the overlap penalty by fixed
edge noise and close the resulting geometric-series limit.
-/

namespace LowDegree

open Asymptotics Filter Topology

/-- The exponent occurring in the large connected-support estimate.  Here
`m` is the number of decomposition pieces, `ℓ` their lower edge scale, and
`k` the treewidth bound. -/
noncomputable def overlapNoiseExponent
    (noise : ℝ) (k ℓ : ℕ → ℕ) (n m : ℕ) : ℝ :=
  2 * (m : ℝ) * (ℓ n : ℝ) * Real.log (1 - noise) +
    ((k n : ℝ) + 1) * ((m - 1 : ℕ) : ℝ) * Real.log (n : ℝ)

/-- The scale condition `(kₙ+1) log n = o(ℓₙ)` makes the overlap
penalty uniformly smaller than the decay from any fixed positive noise rate,
simultaneously for every number `m ≥ 1` of pieces.  This is the exponential
comparison in the proof of paper Lemma 4.5. -/
theorem eventually_overlapNoiseExponent_nonpos
    (noise : NoiseRate) {k ℓ : ℕ → ℕ}
    (hscale : LittleO
      (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ))
      (fun n ↦ (ℓ n : ℝ))) :
    ∀ᶠ n in atTop, ∀ m : ℕ, 1 ≤ m →
      overlapNoiseExponent (noise : ℝ) k ℓ n m ≤ 0 := by
  let δ : ℝ := -Real.log (1 - (noise : ℝ))
  have hbase0 : 0 < 1 - (noise : ℝ) := sub_pos.mpr noise.2.2
  have hbase1 : 1 - (noise : ℝ) < 1 := by linarith [noise.2.1]
  have hδ : 0 < δ := by
    exact neg_pos.mpr (Real.log_neg hbase0 hbase1)
  have hbound := hscale.bound hδ
  filter_upwards [hbound] with n hn
  intro m hm
  have hx0 : 0 ≤ ((k n : ℝ) + 1) * Real.log (n : ℝ) :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
  have hℓ0 : 0 ≤ (ℓ n : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hx0, Real.norm_of_nonneg hℓ0] at hn
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hsub : (((m - 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
    exact_mod_cast Nat.sub_le m 1
  have hxsub :
      ((k n : ℝ) + 1) * Real.log (n : ℝ) * (((m - 1 : ℕ) : ℝ)) ≤
        ((k n : ℝ) + 1) * Real.log (n : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hsub hx0
  have hxm :
      ((k n : ℝ) + 1) * Real.log (n : ℝ) * (m : ℝ) ≤
        δ * (ℓ n : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right hn hm0
  unfold overlapNoiseExponent
  change
    2 * (m : ℝ) * (ℓ n : ℝ) * Real.log (1 - (noise : ℝ)) +
      ((k n : ℝ) + 1) * (((m - 1 : ℕ) : ℝ)) * Real.log (n : ℝ) ≤ 0
  have hlog : Real.log (1 - (noise : ℝ)) = -δ := by simp [δ]
  rw [hlog]
  nlinarith

/-- Equivalent exponential form of
`eventually_overlapNoiseExponent_nonpos`. -/
theorem eventually_exp_overlapNoiseExponent_le_one
    (noise : NoiseRate) {k ℓ : ℕ → ℕ}
    (hscale : LittleO
      (fun n ↦ ((k n : ℝ) + 1) * Real.log (n : ℝ))
      (fun n ↦ (ℓ n : ℝ))) :
    ∀ᶠ n in atTop, ∀ m : ℕ, 1 ≤ m →
      Real.exp (overlapNoiseExponent (noise : ℝ) k ℓ n m) ≤ 1 := by
  filter_upwards [eventually_overlapNoiseExponent_nonpos noise hscale] with n hn
  intro m hm
  exact Real.exp_le_one_iff.mpr (hn m hm)

/-- A vanishing nonnegative block mass has a vanishing geometric tail. -/
theorem geometricTail_vanishes
    {block : ℕ → ℝ} (hblock : Vanishes block) :
    Vanishes (fun n ↦ block n / (1 - block n)) := by
  have hden : Tendsto (fun n ↦ 1 - block n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hblock
  simpa only [zero_div] using
    hblock.div hden (by norm_num : (1 : ℝ) ≠ 0)

/-- Analytic closure of paper Lemma 4.5.

The graph argument splits the connected mass into a small-support term and a
large-support term bounded by the geometric tail of a block mass.  Once the
two input masses vanish, the complete connected noised mass vanishes. -/
theorem connectedNoisedMass_vanishes_of_decomposition
    {connectedMass smallMass blockMass : ℕ → ℝ}
    (hconnected_nonneg : ∀ᶠ n in atTop, 0 ≤ connectedMass n)
    (hsmall : Vanishes smallMass)
    (hblock : Vanishes blockMass)
    (hdecomposition : ∀ᶠ n in atTop,
      connectedMass n ≤
        smallMass n + blockMass n / (1 - blockMass n)) :
    Vanishes connectedMass := by
  have htail := geometricTail_vanishes hblock
  have hupper : Vanishes
      (fun n ↦ smallMass n + blockMass n / (1 - blockMass n)) :=
    hsmall.add htail
  exact squeeze_zero' hconnected_nonneg hdecomposition hupper

end LowDegree
