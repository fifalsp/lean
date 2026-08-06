import LowDegree.DeterministicConfigurationShortCycles
import LowDegree.DeterministicConfigurationModelBridge
import LowDegree.SupercriticalCanonicalScales

/-!
# The logarithmic cutoff used by Appendix A.1

Appendix A.5 naturally controls cycles of length at most
`deterministicConfigurationCycleCutoff d m`.  Pruning at one more than this
integer deletes exactly those cycles.  The deterministic witness in Appendix
A.1, however, asks for a lower bound by `κ log n` at every index, not merely
eventually.  This module makes the harmless finite-prefix patch explicit.

It also defines the natural-valued edge-deletion budget obtained from the
short-cycle presentation bound and proves that this budget is sublinear.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## A pointwise logarithmic cutoff -/

/-- The explicit logarithmic-girth constant used in the cutoff patch. -/
noncomputable def appendixConfigurationCycleKappa (d : ℕ) (r : ℝ) : ℝ :=
  r / (4 * Real.log (deterministicConfigurationCycleFactor d : ℝ))

theorem appendixConfigurationCycleKappa_pos
    (d : ℕ) (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    0 < appendixConfigurationCycleKappa d r := by
  have hK : (1 : ℝ) < deterministicConfigurationCycleFactor d := by
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt
      (show 1 ≤ d by omega)
  exact div_pos hr (mul_pos (by norm_num) (Real.log_pos hK))

/-- The unpatched pruning cutoff furnished directly by Appendix A.5. -/
noncomputable def appendixConfigurationBaseCycleCutoff
    (d : ℕ) (r : ℝ) (n : ℕ) : ℕ :=
  deterministicConfigurationCycleCutoff d (appendixPlantSize r n) + 1

/-- The finite-prefix-patched cutoff.  The first term enforces the paper's
pointwise `κ log n` lower bound, while the second is the A.5 cutoff. -/
noncomputable def appendixConfigurationCycleCutoff
    (d : ℕ) (r : ℝ) (n : ℕ) : ℕ :=
  max
    (Nat.ceil (appendixConfigurationCycleKappa d r * Real.log (n : ℝ)))
    (appendixConfigurationBaseCycleCutoff d r n)

/-- The patched cutoff satisfies the logarithmic lower bound at every
natural index, including the finite prefix where Appendix A.5 is not used. -/
theorem appendixConfigurationCycleCutoff_lower
    (d : ℕ) (r : ℝ) (n : ℕ) :
    appendixConfigurationCycleKappa d r * Real.log (n : ℝ) ≤
      (appendixConfigurationCycleCutoff d r n : ℝ) := by
  have hceil :
      appendixConfigurationCycleKappa d r * Real.log (n : ℝ) ≤
        (Nat.ceil
          (appendixConfigurationCycleKappa d r * Real.log (n : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hmax :
      Nat.ceil (appendixConfigurationCycleKappa d r * Real.log (n : ℝ)) ≤
        appendixConfigurationCycleCutoff d r n := by
    exact le_max_left _ _
  exact hceil.trans (by exact_mod_cast hmax)

/-- Eventually the finite-prefix patch disappears, so the cutoff is exactly
one more than the largest cycle length counted in Appendix A.5. -/
theorem eventually_appendixConfigurationCycleCutoff_eq_base
    (d : ℕ) (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      appendixConfigurationCycleCutoff d r n =
        appendixConfigurationBaseCycleCutoff d r n := by
  let K : ℝ := deterministicConfigurationCycleFactor d
  have hd1 : 1 ≤ d := by omega
  have hKone : 1 < K := by
    dsimp [K]
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt hd1
  have hlogK : 0 < Real.log K := Real.log_pos hKone
  filter_upwards [eventually_appendixPlantSize_log_ratio_ge_half hr,
      eventually_gt_atTop (1 : ℕ)] with n hratio hn
  have hlogn : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn)
  have hlogm :
      (r / 2) * Real.log (n : ℝ) ≤
        Real.log (appendixPlantSize r n : ℝ) := by
    exact (le_div_iff₀ hlogn).mp hratio
  have hkappaRatio :
      appendixConfigurationCycleKappa d r * Real.log (n : ℝ) ≤
        Real.log (appendixPlantSize r n : ℝ) / (2 * Real.log K) := by
    calc
      appendixConfigurationCycleKappa d r * Real.log (n : ℝ) =
          ((r / 2) * Real.log (n : ℝ)) / (2 * Real.log K) := by
        dsimp [appendixConfigurationCycleKappa, K]
        field_simp [hlogK.ne']
        ring
      _ ≤ Real.log (appendixPlantSize r n : ℝ) /
          (2 * Real.log K) :=
        div_le_div_of_nonneg_right hlogm (mul_pos (by norm_num) hlogK).le
  have hfloor :
      Real.log (appendixPlantSize r n : ℝ) / (2 * Real.log K) <
        (deterministicConfigurationCycleCutoff d
            (appendixPlantSize r n) + 1 : ℕ) := by
    simpa only [deterministicConfigurationCycleCutoff, K, Nat.cast_add,
      Nat.cast_one] using
      Nat.lt_floor_add_one
        (Real.log (appendixPlantSize r n : ℝ) / (2 * Real.log K))
  have hceil :
      Nat.ceil
          (appendixConfigurationCycleKappa d r * Real.log (n : ℝ)) ≤
        appendixConfigurationBaseCycleCutoff d r n := by
    apply Nat.ceil_le.mpr
    dsimp [appendixConfigurationBaseCycleCutoff]
    exact hkappaRatio.trans hfloor.le
  exact max_eq_right hceil

/-! ## The A.5 edge-deletion budget -/

/-- Real envelope supplied by the A.5 presentation-to-edge comparison on
the event where the number of short-cycle presentations is at most
`m^(3/4)`. -/
noncomputable def configurationShortCycleEdgeBudgetReal
    (d m : ℕ) : ℝ :=
  2 * (deterministicConfigurationCycleCutoff d m : ℝ) ^ 2 *
    (m : ℝ) ^ (3 / 4 : ℝ)

/-- Natural-valued edge-deletion budget used by the finite selection
bridge. -/
noncomputable def configurationShortCycleEdgeBudget
    (d m : ℕ) : ℕ :=
  Nat.ceil (configurationShortCycleEdgeBudgetReal d m)

/-- The cycle budget along the paper's plant-size sequence. -/
noncomputable def appendixConfigurationShortCycleEdgeBudget
    (d : ℕ) (r : ℝ) (n : ℕ) : ℕ :=
  configurationShortCycleEdgeBudget d (appendixPlantSize r n)

theorem configurationShortCycleEdgeBudgetReal_nonneg (d m : ℕ) :
    0 ≤ configurationShortCycleEdgeBudgetReal d m := by
  unfold configurationShortCycleEdgeBudgetReal
  positivity

/-- The real A.5 edge envelope is bounded by its natural ceiling. -/
theorem configurationShortCycleEdgeBudgetReal_le_budget
    (d m : ℕ) :
    configurationShortCycleEdgeBudgetReal d m ≤
      (configurationShortCycleEdgeBudget d m : ℝ) := by
  exact Nat.le_ceil _

/-! ## From the A.5 count event to the pruning event -/

/-- On the A.5 good-count event, pruning through length `h` costs no more
than the natural edge budget with the same `h`. -/
theorem randomConfiguration_shortCycleEdges_card_le_budget_of_count_le
    (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d)))
    (hcount :
      configurationShortCycleCountReal
          (Configuration.standardConfiguration m d).partner
          (deterministicConfigurationCycleCutoff d m) sigma ≤
        (m : ℝ) ^ (3 / 4 : ℝ)) :
    (shortCycleEdges (randomConfiguration m d sigma).projectedGraph
        (deterministicConfigurationCycleCutoff d m + 1)).card ≤
      configurationShortCycleEdgeBudget d m := by
  let h := deterministicConfigurationCycleCutoff d m
  have hedge :=
    shortCycleEdges_card_cast_le_two_mul_sq_mul_shortCycleCountReal
      (randomConfiguration m d sigma) h
  have hcount' :
      configurationShortCycleCountReal
          (randomConfiguration m d sigma).partner h (Equiv.refl _) ≤
        (m : ℝ) ^ (3 / 4 : ℝ) := by
    simpa only [h,
      configurationShortCycleCountReal_randomConfiguration_refl] using hcount
  have hreal :
      ((shortCycleEdges (randomConfiguration m d sigma).projectedGraph
          (h + 1)).card : ℝ) ≤
        (configurationShortCycleEdgeBudget d m : ℝ) := by
    calc
      ((shortCycleEdges (randomConfiguration m d sigma).projectedGraph
          (h + 1)).card : ℝ) ≤
          2 * (h : ℝ) ^ 2 *
            configurationShortCycleCountReal
              (randomConfiguration m d sigma).partner h (Equiv.refl _) := hedge
      _ ≤ 2 * (h : ℝ) ^ 2 * (m : ℝ) ^ (3 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hcount' (by positivity)
      _ = configurationShortCycleEdgeBudgetReal d m := by
        rfl
      _ ≤ (configurationShortCycleEdgeBudget d m : ℝ) :=
        configurationShortCycleEdgeBudgetReal_le_budget d m
  exact_mod_cast hreal

/-- The natural cycle-deletion budget is sublinear along every size sequence
tending to infinity. -/
theorem configurationShortCycleEdgeBudget_div_vanishes
    (d : ℕ) (hd : 3 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (configurationShortCycleEdgeBudget d (m n) : ℝ) / (m n : ℝ) := by
  let K : ℝ := deterministicConfigurationCycleFactor d
  have hd1 : 1 ≤ d := by omega
  have hKone : 1 < K := by
    dsimp [K]
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt hd1
  have hlogK : 0 < Real.log K := Real.log_pos hKone
  have hmReal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hlogSq : Vanishes fun n ↦
      Real.log (m n : ℝ) ^ 2 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
    have hraw :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hquarter).tendsto_div_nhds_zero
    have hreal : Tendsto
        (fun x : ℝ ↦ Real.log x ^ 2 / x ^ (1 / 4 : ℝ))
        atTop (nhds 0) := by
      simpa only [Real.rpow_two] using hraw
    exact hreal.comp hmReal
  have hrealEnvelope : Vanishes fun n ↦
      2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 /
        (m n : ℝ) ^ (1 / 4 : ℝ) := by
    have hscaled := hlogSq.const_mul (1 / (2 * Real.log K ^ 2))
    apply hscaled.congr'
    filter_upwards with n
    field_simp [hlogK.ne']
  have hinv : Vanishes fun n ↦ (1 : ℝ) / (m n : ℝ) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hmReal
  have htarget : Vanishes fun n ↦
      2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 /
          (m n : ℝ) ^ (1 / 4 : ℝ) +
        1 / (m n : ℝ) :=
    hrealEnvelope.add hinv
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hmn
    have hmpos : (0 : ℝ) < m n := by
      exact_mod_cast (Nat.zero_lt_of_lt hmn)
    have hcut :
        (deterministicConfigurationCycleCutoff d (m n) : ℝ) ≤
          Real.log (m n : ℝ) / (2 * Real.log K) := by
      simpa only [K] using
        deterministicConfigurationCycleCutoff_le_logRatio hd1 hmn
    have hratioNonneg :
        0 ≤ Real.log (m n : ℝ) / (2 * Real.log K) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hmn))
        (mul_pos (by norm_num) hlogK).le
    have hpowRatio :
        (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) =
          1 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
      calc
        (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) =
            (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (m n : ℝ) ^ ((3 / 4 : ℝ) - 1) := by
          rw [← Real.rpow_sub hmpos]
        _ = 1 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [show (3 / 4 : ℝ) - 1 = -(1 / 4) by norm_num,
            Real.rpow_neg hmpos.le]
          exact (one_div ((m n : ℝ) ^ (1 / 4 : ℝ))).symm
    have hrawRatio :
        configurationShortCycleEdgeBudgetReal d (m n) / (m n : ℝ) ≤
          2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 /
            (m n : ℝ) ^ (1 / 4 : ℝ) := by
      unfold configurationShortCycleEdgeBudgetReal
      calc
        (2 * (deterministicConfigurationCycleCutoff d (m n) : ℝ) ^ 2 *
            (m n : ℝ) ^ (3 / 4 : ℝ)) / (m n : ℝ) =
            2 * (deterministicConfigurationCycleCutoff d (m n) : ℝ) ^ 2 *
              ((m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ)) := by ring
        _ ≤ 2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 *
              ((m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ)) := by
          gcongr
        _ = 2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 /
              (m n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [hpowRatio]
          ring
    have hceil :
        (configurationShortCycleEdgeBudget d (m n) : ℝ) ≤
          configurationShortCycleEdgeBudgetReal d (m n) + 1 := by
      exact (Nat.ceil_lt_add_one
        (configurationShortCycleEdgeBudgetReal_nonneg d (m n))).le
    calc
      (configurationShortCycleEdgeBudget d (m n) : ℝ) / (m n : ℝ) ≤
          (configurationShortCycleEdgeBudgetReal d (m n) + 1) /
            (m n : ℝ) :=
        div_le_div_of_nonneg_right hceil hmpos.le
      _ = configurationShortCycleEdgeBudgetReal d (m n) / (m n : ℝ) +
          1 / (m n : ℝ) := by rw [add_div]
      _ ≤ 2 * (Real.log (m n : ℝ) / (2 * Real.log K)) ^ 2 /
            (m n : ℝ) ^ (1 / 4 : ℝ) + 1 / (m n : ℝ) := by
        exact add_le_add_right hrawRatio _
  · exact htarget

/-- Appendix-facing specialization of sublinearity of the cycle-deletion
budget. -/
theorem appendixConfigurationShortCycleEdgeBudget_div_vanishes
    (d : ℕ) (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    Vanishes fun n ↦
      (appendixConfigurationShortCycleEdgeBudget d r n : ℝ) /
        (appendixPlantSize r n : ℝ) := by
  simpa only [appendixConfigurationShortCycleEdgeBudget] using
    configurationShortCycleEdgeBudget_div_vanishes d hd
      (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr)

/-- With the patched cutoff and the sublinear edge budget above, the bad
short-cycle pruning event appearing in the asymptotic selection bridge has
vanishing probability. -/
theorem appendixConfigurationBadCycle_probability_vanishes
    (d : ℕ) (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadCycleEvent d r
          (appendixConfigurationCycleCutoff d r)
          (appendixConfigurationShortCycleEdgeBudget d r) n) := by
  have hd1 : 1 ≤ d := by omega
  have hcountFailure : Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (FiniteLaw.event fun sigma ↦
          (appendixPlantSize r n : ℝ) ^ (3 / 4 : ℝ) ≤
            configurationShortCycleCountReal
              (Configuration.standardConfiguration
                (appendixPlantSize r n) d).partner
              (deterministicConfigurationCycleCutoff d
                (appendixPlantSize r n)) sigma) :=
    deterministicConfiguration_fewShortCycles_failure_vanishes d hd1
      (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob_nonneg _
  · filter_upwards [eventually_appendixConfigurationCycleCutoff_eq_base
      d hd hr] with n hcutoff
    apply (configurationPermutationLaw (appendixPlantSize r n) d).prob_mono
    intro sigma hsigma
    rw [configurationBadCycleEvent, FiniteLaw.mem_event] at hsigma
    rw [FiniteLaw.mem_event]
    by_contra hnotCount
    have hcount :
        configurationShortCycleCountReal
            (Configuration.standardConfiguration
              (appendixPlantSize r n) d).partner
            (deterministicConfigurationCycleCutoff d
              (appendixPlantSize r n)) sigma ≤
          (appendixPlantSize r n : ℝ) ^ (3 / 4 : ℝ) :=
      (lt_of_not_ge hnotCount).le
    have hedge :=
      randomConfiguration_shortCycleEdges_card_le_budget_of_count_le
        (appendixPlantSize r n) d sigma hcount
    have hsigma' :
        configurationShortCycleEdgeBudget d (appendixPlantSize r n) <
          (shortCycleEdges
            (randomConfiguration (appendixPlantSize r n) d sigma).projectedGraph
            (deterministicConfigurationCycleCutoff d
              (appendixPlantSize r n) + 1)).card := by
      simpa only [appendixConfigurationShortCycleEdgeBudget,
        appendixConfigurationBaseCycleCutoff, hcutoff] using hsigma
    omega
  · exact hcountFailure

end

end LowDegree
