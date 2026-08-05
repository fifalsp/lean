import LowDegree.SupercriticalStatistical
import LowDegree.Asymptotics.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Canonical Appendix A scale conditions

This module discharges the deterministic side conditions left explicit in
the statistical supercritical theorem for the paper's canonical choices

* `mₙ = ⌊nʳ⌋`,
* `Dₙ = ⌈(log n)²⌉`, and
* `gₙ = max(3, ⌊log log n⌋)`.
-/

namespace LowDegree

open Filter Topology Asymptotics

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The real square-root power of `nʳ` is eventually below its natural
floor.  This deliberately loses half the exponent and is robust enough for
all Appendix A side conditions. -/
theorem eventually_rpow_half_le_appendixPlantSize
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (r / 2) ≤ (appendixPlantSize r n : ℝ) := by
  have hhalf : 0 < r / 2 := half_pos hr
  have hpowTop : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (r / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpowTop.eventually_ge_atTop 2,
      Filter.eventually_gt_atTop (0 : ℕ)] with n hnlarge hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy0 : 0 ≤ (n : ℝ) ^ (r / 2) := Real.rpow_nonneg hn0 _
  have hsquare : (n : ℝ) ^ r = ((n : ℝ) ^ (r / 2)) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hn0]
    congr 1
    ring
  have hbelow :
      (n : ℝ) ^ (r / 2) ≤ (n : ℝ) ^ r - 1 := by
    rw [hsquare]
    nlinarith
  exact hbelow.trans (Nat.sub_one_lt_floor ((n : ℝ) ^ r)).le

/-- Appendix A's canonical plant size satisfies the power-scale lower bound
used by the local-sparsity truncation. -/
theorem eventually_appendixPlantSize_log_ratio_ge_half
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      r / 2 ≤ Real.log (appendixPlantSize r n : ℝ) /
        Real.log (n : ℝ) := by
  filter_upwards [eventually_rpow_half_le_appendixPlantSize hr,
      Filter.eventually_gt_atTop (1 : ℕ)] with n hm hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans hnreal
  have hbase : 0 < (n : ℝ) ^ (r / 2) :=
    Real.rpow_pos_of_pos hnpos _
  have hlog := Real.log_le_log hbase hm
  rw [Real.log_rpow hnpos] at hlog
  rw [le_div_iff₀ (Real.log_pos hnreal)]
  simpa only [mul_comm] using hlog

/-- The canonical degree cutoff grows faster than `log n`, and in
particular is `Ω(log n)` in the paper's asymptotic notation. -/
theorem appendixDegreeCutoff_isOmega_log :
    Omega (fun n : ℕ ↦ (appendixDegreeCutoff n : ℝ))
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq :
      (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 2) := by
    simpa only [Function.comp_apply, pow_one] using
      (Asymptotics.isLittleO_pow_pow_atTop_of_lt
        (by omega : (1 : ℕ) < 2)).comp_tendsto hlogTop
  exact hsq.trans_le fun n ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.le_ceil ((Real.log (n : ℝ)) ^ 2)

/-- Every positive power of the canonical plant size eventually dominates
twice the logarithmic degree cutoff. -/
theorem eventually_two_appendixDegreeCutoff_le_appendixPlantSize_rpow
    {r gamma : ℝ} (hr : 0 < r) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,
      ((2 * appendixDegreeCutoff n : ℕ) : ℝ) ≤
        (appendixPlantSize r n : ℝ) ^ gamma := by
  let s : ℝ := r * gamma / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hlogsmall :
      (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 2) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ s) := by
    simpa only [Function.comp_apply, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hlogbound := hlogsmall.bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hpowTop : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogbound, hpowTop.eventually_ge_atTop 4,
      eventually_rpow_half_le_appendixPlantSize hr,
      Filter.eventually_gt_atTop (0 : ℕ)] with n hlog hpow hm hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0 _)] at hlog
  have hD : (appendixDegreeCutoff n : ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 + 1 := by
    exact (Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))).le
  have hcutoff : ((2 * appendixDegreeCutoff n : ℕ) : ℝ) ≤
      (n : ℝ) ^ s := by
    push_cast
    nlinarith
  have hplantpow : (n : ℝ) ^ s ≤
      (appendixPlantSize r n : ℝ) ^ gamma := by
    calc
      (n : ℝ) ^ s = ((n : ℝ) ^ (r / 2)) ^ gamma := by
        rw [← Real.rpow_mul hn0]
        congr 1
        dsimp [s]
        ring
      _ ≤ (appendixPlantSize r n : ℝ) ^ gamma :=
        Real.rpow_le_rpow (Real.rpow_nonneg hn0 _) hm hgamma.le
  exact hcutoff.trans hplantpow

/-- The canonical cycle cutoff is at most `log log n + 3` eventually. -/
theorem eventually_appendixCycleCutoff_le_loglog_add_three :
    ∀ᶠ n : ℕ in atTop,
      (appendixCycleCutoff n : ℝ) ≤
        Real.log (Real.log (n : ℝ)) + 3 := by
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogTop : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTop
  filter_upwards [hloglogTop.eventually_ge_atTop 0] with n hloglog
  have hfloor :
      (⌊Real.log (Real.log (n : ℝ))⌋₊ : ℝ) ≤
        Real.log (Real.log (n : ℝ)) :=
    Nat.floor_le hloglog
  have hmax : appendixCycleCutoff n ≤
      3 + ⌊Real.log (Real.log (n : ℝ))⌋₊ := by
    unfold appendixCycleCutoff
    omega
  have hmaxReal : (appendixCycleCutoff n : ℝ) ≤
      3 + (⌊Real.log (Real.log (n : ℝ))⌋₊ : ℝ) := by
    exact_mod_cast hmax
  linarith

/-- The canonical short-cycle pruning prefactor is negligible compared to
the canonical plant size, for every fixed positive plant exponent `r` and
every fixed `lambda`. -/
theorem appendixCyclePrefactor_vanishes
    (lam : ℝ) {r : ℝ} (hr : 0 < r) :
    Vanishes fun n : ℕ ↦
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          (max 1 lam) ^ appendixCycleCutoff n) /
        (appendixPlantSize r n : ℝ) := by
  let A : ℝ := max 1 lam
  let p : ℝ := A + 2
  let C : ℝ := 4 * A ^ 3
  have hA : 1 ≤ A := by exact le_max_left _ _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hhalf : 0 < r / 2 := half_pos hr
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratioRaw : Tendsto
      (fun x : ℝ ↦ Real.log x ^ p / x ^ (r / 2)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop p hhalf).tendsto_div_nhds_zero
  have hratio : Vanishes fun n : ℕ ↦
      Real.log (n : ℝ) ^ p / (n : ℝ) ^ (r / 2) :=
    hratioRaw.comp tendsto_natCast_atTop_atTop
  have htarget : Vanishes fun n : ℕ ↦
      C * (Real.log (n : ℝ) ^ p / (n : ℝ) ^ (r / 2)) :=
    hratio.const_mul C
  have hnum : ∀ᶠ n : ℕ in atTop,
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          A ^ appendixCycleCutoff n) ≤
        C * Real.log (n : ℝ) ^ p := by
    filter_upwards [eventually_appendixCycleCutoff_le_loglog_add_three,
        hlogTop.eventually_ge_atTop 4] with n hg hlog
    have hlogpos : 0 < Real.log (n : ℝ) := by linarith
    have hlogone : 1 ≤ Real.log (n : ℝ) := by linarith
    have hloglog_le : Real.log (Real.log (n : ℝ)) ≤
        Real.log (n : ℝ) :=
      Real.log_le_self hlogpos.le
    have hgOne : ((appendixCycleCutoff n + 1 : ℕ) : ℝ) ≤
        2 * Real.log (n : ℝ) := by
      push_cast
      linarith
    have hApow : A ^ appendixCycleCutoff n ≤
        A ^ 3 * Real.log (n : ℝ) ^ A := by
      calc
        A ^ appendixCycleCutoff n = A ^ (appendixCycleCutoff n : ℝ) := by
          rw [Real.rpow_natCast]
        _ ≤ A ^ (Real.log (Real.log (n : ℝ)) + 3) :=
          Real.rpow_le_rpow_of_exponent_le hA hg
        _ = A ^ 3 * A ^ Real.log (Real.log (n : ℝ)) := by
          rw [Real.rpow_add hApos]
          rw [Real.rpow_ofNat]
          exact mul_comm _ _
        _ = A ^ 3 * Real.log (n : ℝ) ^ Real.log A := by
          congr 1
          rw [Real.rpow_def_of_pos hApos,
            Real.rpow_def_of_pos hlogpos]
          congr 1
          ring
        _ ≤ A ^ 3 * Real.log (n : ℝ) ^ A := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlogone
              (Real.log_le_self hApos.le))
          positivity
    have hsq :
        (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2) ≤
          (2 * Real.log (n : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hgOne 2
    calc
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          A ^ appendixCycleCutoff n) ≤
        (2 * Real.log (n : ℝ)) ^ 2 *
          (A ^ 3 * Real.log (n : ℝ) ^ A) := by
        exact mul_le_mul hsq hApow (pow_nonneg hApos.le _)
          (sq_nonneg _)
      _ = C * Real.log (n : ℝ) ^ p := by
        dsimp [C, p]
        rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
        have hcombine :
            Real.log (n : ℝ) ^ 2 * Real.log (n : ℝ) ^ A =
              Real.log (n : ℝ) ^ (A + 2) := by
          rw [← Real.rpow_two (Real.log (n : ℝ)),
            ← Real.rpow_add hlogpos]
          congr 1
          ring
        calc
          4 * Real.log (n : ℝ) ^ 2 *
              (A ^ 3 * Real.log (n : ℝ) ^ A) =
            4 * A ^ 3 *
              (Real.log (n : ℝ) ^ 2 *
                Real.log (n : ℝ) ^ A) := by ring
          _ = 4 * A ^ 3 * Real.log (n : ℝ) ^ (A + 2) := by
            rw [hcombine]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg
        (mul_nonneg (sq_nonneg _)
          (pow_nonneg (le_max_of_le_left zero_le_one) _))
        (Nat.cast_nonneg _)
  · filter_upwards [hnum, eventually_rpow_half_le_appendixPlantSize hr,
      Filter.eventually_gt_atTop (0 : ℕ)] with n hnumer hm hn
    have hmpos : (0 : ℝ) < appendixPlantSize r n := by
      have hrpowpos : 0 < (n : ℝ) ^ (r / 2) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      exact hrpowpos.trans_le hm
    have hdenpos : 0 < (n : ℝ) ^ (r / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hlogpow0 : 0 ≤ Real.log (n : ℝ) ^ p :=
      Real.rpow_nonneg (Real.log_natCast_nonneg n) _
    calc
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
            (max 1 lam) ^ appendixCycleCutoff n) /
          (appendixPlantSize r n : ℝ) =
        (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
            A ^ appendixCycleCutoff n) /
          (appendixPlantSize r n : ℝ) := by rfl
      _ ≤ (C * Real.log (n : ℝ) ^ p) /
          (appendixPlantSize r n : ℝ) :=
        div_le_div_of_nonneg_right hnumer hmpos.le
      _ ≤ (C * Real.log (n : ℝ) ^ p) /
          (n : ℝ) ^ (r / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hC0 hlogpow0) hdenpos hm
      _ = C * (Real.log (n : ℝ) ^ p /
          (n : ℝ) ^ (r / 2)) := by ring
  · exact htarget

/-- Since `r<1/2`, the square of the canonical plant size is negligible
relative to the ambient size. -/
theorem appendixPlantSize_sq_div_index_vanishes
    {r : ℝ} (hr : r < 1 / 2) :
    Vanishes fun n : ℕ ↦
      (appendixPlantSize r n : ℝ) ^ 2 / (n : ℝ) := by
  have hexp : 0 < 1 - 2 * r := by linarith
  have htarget : Vanishes fun n : ℕ ↦
      (n : ℝ) ^ (-(1 - 2 * r)) :=
    (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hfloor : (appendixPlantSize r n : ℝ) ≤ (n : ℝ) ^ r :=
      Nat.floor_le (Real.rpow_nonneg hnreal.le _)
    calc
      (appendixPlantSize r n : ℝ) ^ 2 / (n : ℝ) ≤
          ((n : ℝ) ^ r) ^ 2 / (n : ℝ) := by gcongr
      _ = (n : ℝ) ^ (r * 2) / (n : ℝ) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hnreal.le]
      _ = (n : ℝ) ^ (r * 2) / (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (r * 2 - 1) :=
        (Real.rpow_sub hnreal (r * 2) 1).symm
      _ = (n : ℝ) ^ (2 * r - 1) := by
        congr 1
        ring
      _ = (n : ℝ) ^ (-(1 - 2 * r)) := by ring_nf
  · exact htarget

/-- **Canonical paper Lemma A.3 (edge-density form).**  The twice-truncated
sparse Erdős--Rényi plant at the printed Appendix A scales retains limiting
edge density `lambda / 2` in probability. -/
theorem appendix_locallyTruncatedPruned_edgeDensity_tendstoInProbability
    (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    TendstoInProbability
      (fun n ↦ erdosRenyiLaw (n := appendixPlantSize r n)
        (sparseBernoulliParameter lam (appendixPlantSize r n)))
      (locallyTruncatedPrunedEdgeDensityAt lam r gamma
        (appendixPlantSize r) appendixCycleCutoff)
      (lam / 2) := by
  exact locallyTruncatedPruned_edgeDensity_tendstoInProbability
    lam r gamma hlam hr hgamma (appendixPlantSize r) appendixCycleCutoff
    (appendixPlantSize_tendsto_atTop hr.1)
    (eventually_appendixPlantSize_log_ratio_ge_half hr.1)
    (appendixCyclePrefactor_vanishes lam hr.1)

/-- The statistical conclusion with all canonical scale hypotheses
discharged internally. -/
theorem appendix_statisticalDistinguishability_of_supercritical_canonical
    (epsilon : NoiseRate) (c lam r gamma : ℝ)
    (hc : 0 < c) (hlam : 0 < lam)
    (hsuper : 2 / (1 - (epsilon : ℝ)) < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    TendsToOne fun n ↦
      (appendixNoisedAlternativeLaw epsilon c lam r gamma hr n).tv
        (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)) := by
  exact appendix_statisticalDistinguishability_of_supercritical
    epsilon c lam r gamma hc hlam hsuper hr hgamma
    (eventually_appendixPlantSize_log_ratio_ge_half hr.1)
    (appendixCyclePrefactor_vanishes lam hr.1)

end

end LowDegree
