import LowDegree.DeterministicConfigurationProbability

/-!
# Selecting deterministic plants from configuration-model estimates

This file is the paper-facing bridge between the two probabilistic
configuration-model lemmas and Appendix Lemma A.1.  It names the three bad
events that have to be controlled: failure of local sparsity, excessive
short-cycle pruning loss, and excessive loss when loops and parallel pairs
are collapsed.  A strict union-bound estimate selects one permutation for
every `n`; all remaining conclusions are deterministic.

The structure `ConfigurationModelEstimates` deliberately contains only
numerical/probabilistic estimates.  In particular, its conversion theorem
does not hide a graph-theoretic existence assumption.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Failure of the local-sparsity inequality required in Appendix Lemma A.1.

For `n < 2` the event is empty, since the displayed paper inequality has a
`log n` denominator and is only used in the asymptotic range. -/
noncomputable def configurationBadLocalEvent
    (d : ℕ) (r gamma A : ℝ) (n : ℕ) :
    Finset (Equiv.Perm
      (ConfigurationHalfEdge (appendixPlantSize r n) (d + d))) :=
  FiniteLaw.event fun sigma ↦
    ∃ U : Finset (Fin (appendixPlantSize r n)),
      2 ≤ n ∧
      2 ≤ U.card ∧
      (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma ∧
      (1 + A / Real.log (n : ℝ)) * (U.card : ℝ) <
        (deterministicInducedEdgeCount
          (randomConfiguration (appendixPlantSize r n) d sigma).projectedGraph U : ℝ)

/-- The event that deleting every edge lying on a cycle below `cutoff n`
would cost more than the allotted short-cycle budget. -/
noncomputable def configurationBadCycleEvent
    (d : ℕ) (r : ℝ) (cutoff cycleBudget : ℕ → ℕ) (n : ℕ) :
    Finset (Equiv.Perm
      (ConfigurationHalfEdge (appendixPlantSize r n) (d + d))) :=
  FiniteLaw.event fun sigma ↦
    cycleBudget n <
      (shortCycleEdges
        (randomConfiguration (appendixPlantSize r n) d sigma).projectedGraph
        (cutoff n)).card

/-- The event that loop deletion and parallel-edge collapse cost more than
the allotted projection-defect budget. -/
noncomputable def configurationBadDefectEvent
    (d : ℕ) (r : ℝ) (defectBudget : ℕ → ℕ) (n : ℕ) :
    Finset (Equiv.Perm
      (ConfigurationHalfEdge (appendixPlantSize r n) (d + d))) :=
  FiniteLaw.event fun sigma ↦
    defectBudget n <
      (randomConfiguration (appendixPlantSize r n) d sigma).projectionDefect

/-- The exact estimates needed from the configuration model.

The Appendix A.4 union bound supplies `badProbability`; Appendix A.5 and a
loop/parallel-pair estimate supply the two vanishing budgets.  The strict
bound by one is intentionally finite and pointwise, so it also handles the
finitely many small values of `n` without an eventual-choice side condition. -/
structure ConfigurationModelEstimates (d : ℕ) (r gamma : ℝ) where
  A : ℝ
  kappa : ℝ
  A_pos : 0 < A
  kappa_pos : 0 < kappa
  cutoff : ℕ → ℕ
  cycleBudget : ℕ → ℕ
  defectBudget : ℕ → ℕ
  cutoff_lower : ∀ n : ℕ,
    kappa * Real.log (n : ℝ) ≤ (cutoff n : ℝ)
  badProbability : ∀ n : ℕ,
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

namespace ConfigurationModelEstimates

variable {d : ℕ} {r gamma : ℝ}

/-- A permutation outside all three bad events exists for each `n`. -/
theorem exists_goodPermutation (E : ConfigurationModelEstimates d r gamma)
    (n : ℕ) :
    ∃ sigma : Equiv.Perm
        (ConfigurationHalfEdge (appendixPlantSize r n) (d + d)),
      sigma ∉ configurationBadLocalEvent d r gamma E.A n ∧
      sigma ∉ configurationBadCycleEvent d r E.cutoff E.cycleBudget n ∧
      sigma ∉ configurationBadDefectEvent d r E.defectBudget n := by
  exact FiniteLaw.exists_notMem_three_of_sum_prob_lt_one
    (configurationPermutationLaw (appendixPlantSize r n) d)
    (configurationBadLocalEvent d r gamma E.A n)
    (configurationBadCycleEvent d r E.cutoff E.cycleBudget n)
    (configurationBadDefectEvent d r E.defectBudget n)
    (E.badProbability n)

/-- Choose one good relabelling of the canonical pairing for every `n`. -/
noncomputable def goodPermutation (E : ConfigurationModelEstimates d r gamma)
    (n : ℕ) :
    Equiv.Perm (ConfigurationHalfEdge (appendixPlantSize r n) (d + d)) :=
  Classical.choose (E.exists_goodPermutation n)

theorem goodPermutation_not_badLocal
    (E : ConfigurationModelEstimates d r gamma) (n : ℕ) :
    E.goodPermutation n ∉
      configurationBadLocalEvent d r gamma E.A n :=
  (Classical.choose_spec (E.exists_goodPermutation n)).1

theorem goodPermutation_not_badCycle
    (E : ConfigurationModelEstimates d r gamma) (n : ℕ) :
    E.goodPermutation n ∉
      configurationBadCycleEvent d r E.cutoff E.cycleBudget n :=
  (Classical.choose_spec (E.exists_goodPermutation n)).2.1

theorem goodPermutation_not_badDefect
    (E : ConfigurationModelEstimates d r gamma) (n : ℕ) :
    E.goodPermutation n ∉
      configurationBadDefectEvent d r E.defectBudget n :=
  (Classical.choose_spec (E.exists_goodPermutation n)).2.2

/-- The selected configuration sequence. -/
noncomputable def configuration (E : ConfigurationModelEstimates d r gamma)
    (n : ℕ) : Configuration (appendixPlantSize r n) (d + d) :=
  randomConfiguration (appendixPlantSize r n) d (E.goodPermutation n)

theorem configuration_localSparsity
    (E : ConfigurationModelEstimates d r gamma)
    (n : ℕ) (hn : 2 ≤ n)
    (U : Finset (Fin (appendixPlantSize r n))) (hUtwo : 2 ≤ U.card)
    (hUsize : (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma) :
    (deterministicInducedEdgeCount (E.configuration n).projectedGraph U : ℝ) ≤
      (1 + E.A / Real.log (n : ℝ)) * (U.card : ℝ) := by
  have hgood := E.goodPermutation_not_badLocal n
  rw [configurationBadLocalEvent, FiniteLaw.mem_event] at hgood
  change ¬ ∃ U : Finset (Fin (appendixPlantSize r n)), _ at hgood
  by_contra hnot
  apply hgood
  exact ⟨U, hn, hUtwo, hUsize, lt_of_not_ge hnot⟩

theorem configuration_shortCycleLoss_le
    (E : ConfigurationModelEstimates d r gamma) (n : ℕ) :
    (shortCycleEdges (E.configuration n).projectedGraph
      (E.cutoff n)).card ≤ E.cycleBudget n := by
  have hgood := E.goodPermutation_not_badCycle n
  rw [configurationBadCycleEvent, FiniteLaw.mem_event] at hgood
  exact Nat.le_of_not_gt hgood

theorem configuration_projectionDefect_le
    (E : ConfigurationModelEstimates d r gamma) (n : ℕ) :
    (E.configuration n).projectionDefect ≤ E.defectBudget n := by
  have hgood := E.goodPermutation_not_badDefect n
  rw [configurationBadDefectEvent, FiniteLaw.mem_event] at hgood
  exact Nat.le_of_not_gt hgood

theorem configuration_shortCycleLossVanishes
    (E : ConfigurationModelEstimates d r gamma) : Tendsto
    (fun n ↦
      (((shortCycleEdges (E.configuration n).projectedGraph
        (E.cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ)))
    atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    have hcast :
        ((shortCycleEdges (E.configuration n).projectedGraph
          (E.cutoff n)).card : ℝ) ≤ (E.cycleBudget n : ℝ) := by
      exact_mod_cast E.configuration_shortCycleLoss_le n
    exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
  · exact E.cycleBudgetVanishes

theorem configuration_projectionDefectVanishes
    (E : ConfigurationModelEstimates d r gamma) : Tendsto
    (fun n ↦ (((E.configuration n).projectionDefect : ℝ) /
      (appendixPlantSize r n : ℝ)))
    atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    have hcast : ((E.configuration n).projectionDefect : ℝ) ≤
        (E.defectBudget n : ℝ) := by
      exact_mod_cast E.configuration_projectionDefect_le n
    exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
  · exact E.defectBudgetVanishes

/-- The probabilistic estimates produce the exact deterministic selection
data consumed by the finite pruning construction. -/
noncomputable def toConfigurationSelectionData
    (E : ConfigurationModelEstimates d r gamma) :
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

/-- Final paper-facing conclusion of Appendix Lemma A.1 from precisely the
three finite configuration-model estimates. -/
noncomputable def toDeterministicPlantWitness
    (E : ConfigurationModelEstimates d r gamma) (hr : 0 < r) :
    DeterministicPlantWitness (d + d) r gamma :=
  E.toConfigurationSelectionData.toDeterministicPlantWitness hr

end ConfigurationModelEstimates

end

end LowDegree
