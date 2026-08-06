import LowDegree.DeterministicConfigurationModelBridge

/-!
# Asymptotic selection from configuration-model estimates

The probability estimates in Appendix A.4--A.5 are asymptotic: their bad
probabilities have sum below one only for all sufficiently large indices.
This file supplies the finite-prefix patch needed to turn those estimates
into the pointwise deterministic graph sequence of Appendix A.1.  At an
index where the strict probability bound is not available, we use the
canonical all-loop configuration; its projected simple graph is edgeless.
Consequently the local-sparsity condition remains true, while changing only
finitely many defect and pruning-loss terms does not affect their limits.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Configuration

/-- The canonical configuration pairs sockets at the same vertex, so its
simple projection has no edges. -/
@[simp] theorem standardConfiguration_projectedGraph
    (m d : ℕ) :
    (standardConfiguration m d).projectedGraph = ⊥ := by
  ext u v
  constructor
  · rintro ⟨huv, i, hi⟩
    apply huv
    simpa [socketNeighbor, standardConfiguration] using hi
  · simp

end Configuration

/-- The exact estimates needed only eventually in the configuration-model
argument.  This is the natural interface produced by probability bounds
that vanish as `n → ∞`. -/
structure AsymptoticConfigurationModelEstimates
    (d : ℕ) (r gamma : ℝ) where
  A : ℝ
  kappa : ℝ
  A_pos : 0 < A
  kappa_pos : 0 < kappa
  cutoff : ℕ → ℕ
  cycleBudget : ℕ → ℕ
  defectBudget : ℕ → ℕ
  cutoff_lower : ∀ n : ℕ,
    kappa * Real.log (n : ℝ) ≤ (cutoff n : ℝ)
  badProbability : ∀ᶠ n : ℕ in atTop,
    (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma A n) +
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadCycleEvent d r cutoff cycleBudget n) +
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadDefectEvent d r defectBudget n) < 1
  cycleBudgetVanishes : Tendsto
    (fun n ↦ ((cycleBudget n : ℝ) / (appendixPlantSize r n : ℝ)))
    atTop (nhds 0)
  defectBudgetVanishes : Tendsto
    (fun n ↦ ((defectBudget n : ℝ) / (appendixPlantSize r n : ℝ)))
    atTop (nhds 0)

namespace AsymptoticConfigurationModelEstimates

variable {d : ℕ} {r gamma : ℝ}

/-- The strict union-bound condition at one index. -/
def GoodIndex (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) : Prop :=
  (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma E.A n) +
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadCycleEvent d r E.cutoff E.cycleBudget n) +
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadDefectEvent d r E.defectBudget n) < 1

theorem eventually_goodIndex
    (E : AsymptoticConfigurationModelEstimates d r gamma) :
    ∀ᶠ n : ℕ in atTop, E.GoodIndex n :=
  E.badProbability

/-- At a good index, the finite union bound supplies a relabelling outside
all three bad events. -/
theorem exists_goodPermutation_of_goodIndex
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : E.GoodIndex n) :
    ∃ sigma : Equiv.Perm
        (ConfigurationHalfEdge (appendixPlantSize r n) (d + d)),
      sigma ∉ configurationBadLocalEvent d r gamma E.A n ∧
      sigma ∉ configurationBadCycleEvent d r E.cutoff E.cycleBudget n ∧
      sigma ∉ configurationBadDefectEvent d r E.defectBudget n := by
  exact FiniteLaw.exists_notMem_three_of_sum_prob_lt_one
    (configurationPermutationLaw (appendixPlantSize r n) d)
    (configurationBadLocalEvent d r gamma E.A n)
    (configurationBadCycleEvent d r E.cutoff E.cycleBudget n)
    (configurationBadDefectEvent d r E.defectBudget n) hn

/-- Use a selected good configuration when the strict probability estimate
is available, and the canonical all-loop configuration otherwise. -/
noncomputable def configuration
    (E : AsymptoticConfigurationModelEstimates d r gamma) (n : ℕ) :
    Configuration (appendixPlantSize r n) (d + d) :=
  if hn : E.GoodIndex n then
    randomConfiguration (appendixPlantSize r n) d
      (Classical.choose (E.exists_goodPermutation_of_goodIndex n hn))
  else
    Configuration.standardConfiguration (appendixPlantSize r n) d

theorem configuration_eq_of_goodIndex
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : E.GoodIndex n) :
    E.configuration n =
      randomConfiguration (appendixPlantSize r n) d
        (Classical.choose (E.exists_goodPermutation_of_goodIndex n hn)) := by
  simp [configuration, hn]

theorem chosenPermutation_not_badLocal
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : E.GoodIndex n) :
    Classical.choose (E.exists_goodPermutation_of_goodIndex n hn) ∉
      configurationBadLocalEvent d r gamma E.A n :=
  (Classical.choose_spec (E.exists_goodPermutation_of_goodIndex n hn)).1

theorem chosenPermutation_not_badCycle
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : E.GoodIndex n) :
    Classical.choose (E.exists_goodPermutation_of_goodIndex n hn) ∉
      configurationBadCycleEvent d r E.cutoff E.cycleBudget n :=
  (Classical.choose_spec (E.exists_goodPermutation_of_goodIndex n hn)).2.1

theorem chosenPermutation_not_badDefect
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : E.GoodIndex n) :
    Classical.choose (E.exists_goodPermutation_of_goodIndex n hn) ∉
      configurationBadDefectEvent d r E.defectBudget n :=
  (Classical.choose_spec (E.exists_goodPermutation_of_goodIndex n hn)).2.2

theorem configuration_localSparsity
    (E : AsymptoticConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : 2 ≤ n)
    (U : Finset (Fin (appendixPlantSize r n))) (hUtwo : 2 ≤ U.card)
    (hUsize : (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma) :
    (deterministicInducedEdgeCount (E.configuration n).projectedGraph U : ℝ) ≤
      (1 + E.A / Real.log (n : ℝ)) * (U.card : ℝ) := by
  by_cases hgood : E.GoodIndex n
  · rw [E.configuration_eq_of_goodIndex n hgood]
    have hnot := E.chosenPermutation_not_badLocal n hgood
    unfold configurationBadLocalEvent at hnot
    rw [FiniteLaw.mem_event] at hnot
    change ¬ ∃ U : Finset (Fin (appendixPlantSize r n)),
      2 ≤ n ∧
      2 ≤ U.card ∧
      (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma ∧
      (1 + E.A / Real.log (n : ℝ)) * (U.card : ℝ) <
        (deterministicInducedEdgeCount
          (randomConfiguration (appendixPlantSize r n) d
            (Classical.choose
              (E.exists_goodPermutation_of_goodIndex n hgood))).projectedGraph U : ℝ)
      at hnot
    by_contra hcontra
    apply hnot
    exact ⟨U, hn, hUtwo, hUsize, lt_of_not_ge hcontra⟩
  · rw [configuration, dif_neg hgood,
      Configuration.standardConfiguration_projectedGraph]
    simp only [deterministicInducedEdgeCount]
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnReal
    have hfactor : 0 ≤ 1 + E.A / Real.log (n : ℝ) := by
      have hquot : 0 ≤ E.A / Real.log (n : ℝ) :=
        div_nonneg E.A_pos.le hlog.le
      linarith
    simpa [deterministicInducedEdgeCount] using
      (mul_nonneg hfactor (Nat.cast_nonneg U.card))

theorem eventually_configuration_shortCycleLoss_le
    (E : AsymptoticConfigurationModelEstimates d r gamma) :
    ∀ᶠ n : ℕ in atTop,
      (shortCycleEdges (E.configuration n).projectedGraph
        (E.cutoff n)).card ≤ E.cycleBudget n := by
  filter_upwards [E.eventually_goodIndex] with n hn
  rw [E.configuration_eq_of_goodIndex n hn]
  have hnot := E.chosenPermutation_not_badCycle n hn
  unfold configurationBadCycleEvent at hnot
  rw [FiniteLaw.mem_event] at hnot
  change ¬ E.cycleBudget n <
    (shortCycleEdges
      (randomConfiguration (appendixPlantSize r n) d
        (Classical.choose
          (E.exists_goodPermutation_of_goodIndex n hn))).projectedGraph
      (E.cutoff n)).card at hnot
  exact Nat.le_of_not_gt hnot

theorem eventually_configuration_projectionDefect_le
    (E : AsymptoticConfigurationModelEstimates d r gamma) :
    ∀ᶠ n : ℕ in atTop,
      (E.configuration n).projectionDefect ≤ E.defectBudget n := by
  filter_upwards [E.eventually_goodIndex] with n hn
  rw [E.configuration_eq_of_goodIndex n hn]
  have hnot := E.chosenPermutation_not_badDefect n hn
  unfold configurationBadDefectEvent at hnot
  rw [FiniteLaw.mem_event] at hnot
  change ¬ E.defectBudget n <
    (randomConfiguration (appendixPlantSize r n) d
      (Classical.choose
        (E.exists_goodPermutation_of_goodIndex n hn))).projectionDefect at hnot
  exact Nat.le_of_not_gt hnot

theorem configuration_shortCycleLossVanishes
    (E : AsymptoticConfigurationModelEstimates d r gamma) : Tendsto
    (fun n ↦
      (((shortCycleEdges (E.configuration n).projectedGraph
        (E.cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ)))
    atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [E.eventually_configuration_shortCycleLoss_le] with n hn
    have hcast :
        ((shortCycleEdges (E.configuration n).projectedGraph
          (E.cutoff n)).card : ℝ) ≤ (E.cycleBudget n : ℝ) := by
      exact_mod_cast hn
    exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
  · exact E.cycleBudgetVanishes

theorem configuration_projectionDefectVanishes
    (E : AsymptoticConfigurationModelEstimates d r gamma) : Tendsto
    (fun n ↦ (((E.configuration n).projectionDefect : ℝ) /
      (appendixPlantSize r n : ℝ)))
    atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [E.eventually_configuration_projectionDefect_le] with n hn
    have hcast : ((E.configuration n).projectionDefect : ℝ) ≤
        (E.defectBudget n : ℝ) := by
      exact_mod_cast hn
    exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
  · exact E.defectBudgetVanishes

/-- Eventual probabilistic estimates produce the exact deterministic
selection data used by the pruning construction. -/
noncomputable def toConfigurationSelectionData
    (E : AsymptoticConfigurationModelEstimates d r gamma) :
    ConfigurationSelectionData d r gamma where
  A := E.A
  kappa := E.kappa
  A_pos := E.A_pos
  kappa_pos := E.kappa_pos
  configuration := E.configuration
  cutoff := E.cutoff
  localSparsity := E.configuration_localSparsity
  cutoff_lower := E.cutoff_lower
  projectionDefectVanishes := E.configuration_projectionDefectVanishes
  shortCycleLossVanishes := E.configuration_shortCycleLossVanishes

/-- Final Appendix A.1 witness from estimates holding for all sufficiently
large indices; the finite prefix is handled canonically. -/
noncomputable def toDeterministicPlantWitness
    (E : AsymptoticConfigurationModelEstimates d r gamma) (hr : 0 < r) :
    DeterministicPlantWitness (d + d) r gamma :=
  E.toConfigurationSelectionData.toDeterministicPlantWitness hr

end AsymptoticConfigurationModelEstimates

end

end LowDegree
