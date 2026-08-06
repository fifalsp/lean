import LowDegree.DeterministicConfigurationAsymptoticBridge
import LowDegree.DeterministicConfigurationCutoffBridge
import LowDegree.DeterministicConfigurationDefect

/-!
# Unconditional configuration-model construction for Appendix A.1

This module combines the three finite-configuration estimates:

* the local-sparsity failure probability from Appendix A.4;
* the short-cycle pruning estimate from Appendix A.5; and
* the loop/parallel-collapse projection-defect estimate.

Their sum vanishes, hence is eventually strictly below one.  The asymptotic
selection bridge then chooses deterministic configurations, patches the
finite prefix, and returns the exact `DeterministicPlantWitness` used by the
rest of the formalization.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The explicit local-sparsity slack constant supplied by Appendix A.4 for
the `2d`-regular configuration model. -/
noncomputable def appendixConfigurationLocalSparsityConstant
    (d : ℕ) (r gamma : ℝ) : ℝ :=
  localSparsitySlackConstant
    (2 * ((d + d : ℕ) : ℝ)) r gamma

theorem appendixConfigurationLocalSparsityConstant_pos
    (d : ℕ) {r gamma : ℝ} (hr : 0 < r) (hgamma : gamma < 1) :
    0 < appendixConfigurationLocalSparsityConstant d r gamma := by
  exact localSparsitySlackConstant_pos
    (2 * ((d + d : ℕ) : ℝ)) hr hgamma

/-- Assemble Appendix A.1 once the A.4 local-failure estimate has been
established.  Keeping this constructor explicit makes the three probabilistic
inputs and the union-bound step transparent. -/
noncomputable def asymptoticConfigurationModelEstimatesOfLocalFailureVanishes
    (d : ℕ) (hd : 3 ≤ d) (r gamma A : ℝ) (hA : 0 < A)
    (hr : 0 < r)
    (hlocal : Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma A n)) :
    AsymptoticConfigurationModelEstimates d r gamma := by
  have hcycle :=
    appendixConfigurationBadCycle_probability_vanishes d hd hr
  have hdefect :=
    appendixConfigurationBadDefect_probability_vanishes d (by omega) hr
  have hsum : Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
          (configurationBadLocalEvent d r gamma A n) +
        (configurationPermutationLaw (appendixPlantSize r n) d).prob
          (configurationBadCycleEvent d r
            (appendixConfigurationCycleCutoff d r)
            (appendixConfigurationShortCycleEdgeBudget d r) n) +
        (configurationPermutationLaw (appendixPlantSize r n) d).prob
          (configurationBadDefectEvent d r
            (appendixConfigurationProjectionDefectBudget r) n) :=
    (hlocal.add hcycle).add hdefect
  exact
    { A := A
      kappa := appendixConfigurationCycleKappa d r
      A_pos := hA
      kappa_pos := appendixConfigurationCycleKappa_pos d hd hr
      cutoff := appendixConfigurationCycleCutoff d r
      cycleBudget := appendixConfigurationShortCycleEdgeBudget d r
      defectBudget := appendixConfigurationProjectionDefectBudget r
      cutoff_lower := appendixConfigurationCycleCutoff_lower d r
      badProbability := hsum.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      cycleBudgetVanishes :=
        appendixConfigurationShortCycleEdgeBudget_div_vanishes d hd hr
      defectBudgetVanishes :=
        appendixConfigurationProjectionDefectBudget_div_vanishes hr }

/-- The corresponding unconditional deterministic witness, abstracting only
the A.4 local-failure theorem. -/
noncomputable def deterministicPlantWitnessOfLocalFailureVanishes
    (d : ℕ) (hd : 3 ≤ d) (r gamma A : ℝ) (hA : 0 < A)
    (hr : 0 < r)
    (hlocal : Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma A n)) :
    DeterministicPlantWitness (d + d) r gamma :=
  (asymptoticConfigurationModelEstimatesOfLocalFailureVanishes
    d hd r gamma A hA hr hlocal).toDeterministicPlantWitness hr

/-! ## Unconditional Appendix A.1 -/

/-- All configuration-model estimates needed by Appendix A.1, with the
explicit constants and budgets constructed in A.4--A.5 and the projection
defect calculation. -/
noncomputable def appendixA1_configurationModelEstimates
    (d : ℕ) (hd : 3 ≤ d) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    AsymptoticConfigurationModelEstimates d r gamma := by
  let A := appendixConfigurationLocalSparsityConstant d r gamma
  have hA : 0 < A :=
    appendixConfigurationLocalSparsityConstant_pos d hr.1 hgamma.2
  have hlocal : Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma A n) := by
    simpa only [A, appendixConfigurationLocalSparsityConstant] using
      appendixConfigurationBadLocal_probability_vanishes
        d (by omega) r gamma hr hgamma
  exact asymptoticConfigurationModelEstimatesOfLocalFailureVanishes
    d hd r gamma A hA hr.1 hlocal

/-- **Appendix Lemma A.1, half-degree form.**  For every `d ≥ 3`, the
configuration estimates construct the deterministic `2d`-regular-degree
witness used by the remainder of the appendix. -/
noncomputable def appendixA1_deterministicPlantWitness
    (d : ℕ) (hd : 3 ≤ d) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    DeterministicPlantWitness (d + d) r gamma :=
  AsymptoticConfigurationModelEstimates.toDeterministicPlantWitness
    (appendixA1_configurationModelEstimates d hd r gamma hr hgamma) hr.1

/-- **Appendix Lemma A.1 (paper-facing form).**  Every even total degree
`D ≥ 6` admits the required deterministic planted-graph witness. -/
theorem appendixA1_evenDegree_deterministicPlantWitness
    (D : ℕ) (hD : Even D) (hD6 : 6 ≤ D)
    (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    Nonempty (DeterministicPlantWitness D r gamma) := by
  obtain ⟨d, rfl⟩ := hD
  exact ⟨appendixA1_deterministicPlantWitness
    d (by omega) r gamma hr hgamma⟩

end

end LowDegree
