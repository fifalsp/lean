import LowDegree.DeterministicConfiguration

/-!
# From good finite configurations to the Appendix plant witness

This module isolates the deterministic-selection step of Appendix Lemma A.1.
The remaining genuinely probabilistic task is to produce the data below by
the configuration-model union bounds.  Once those estimates are available,
the conversion to the exact paper-facing `DeterministicPlantWitness` is
fully deterministic.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A selected sequence of even-degree configurations with the two
sublinear losses required by the self-contained defect-deletion route.

`projectionDefectVanishes` accounts for loops and collapsed parallel pairs;
`shortCycleLossVanishes` accounts for the subsequent girth pruning. -/
structure ConfigurationSelectionData (d : ℕ) (r gamma : ℝ) where
  A : ℝ
  kappa : ℝ
  A_pos : 0 < A
  kappa_pos : 0 < kappa
  configuration : (n : ℕ) → Configuration (appendixPlantSize r n) (d + d)
  cutoff : ℕ → ℕ
  localSparsity : ∀ n, 2 ≤ n →
    ∀ U : Finset (Fin (appendixPlantSize r n)),
      2 ≤ U.card →
      (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma →
      (deterministicInducedEdgeCount
        ((configuration n).projectedGraph) U : ℝ) ≤
        (1 + A / Real.log (n : ℝ)) * (U.card : ℝ)
  cutoff_lower : ∀ n : ℕ,
    kappa * Real.log (n : ℝ) ≤ (cutoff n : ℝ)
  projectionDefectVanishes : Tendsto
    (fun n ↦ (((configuration n).projectionDefect : ℝ) /
      (appendixPlantSize r n : ℝ)))
    atTop (nhds 0)
  shortCycleLossVanishes : Tendsto
    (fun n ↦ (((shortCycleEdges ((configuration n).projectedGraph)
      (cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ)))
    atTop (nhds 0)

namespace ConfigurationSelectionData

variable {d : ℕ} {r gamma : ℝ}

/-- The final simple graph: collapse configuration defects, then delete all
edges lying on a cycle below the selected cutoff. -/
noncomputable def graph (S : ConfigurationSelectionData d r gamma) (n : ℕ) :
    SimpleGraph (Fin (appendixPlantSize r n)) :=
  shortCyclePrunedGraph (S.configuration n).projectedGraph (S.cutoff n)

theorem graph_maxDegree (S : ConfigurationSelectionData d r gamma)
    (n : ℕ) (v : Fin (appendixPlantSize r n)) :
    (S.graph n).degree v ≤ d + d := by
  exact (shortCyclePrunedGraph_degree_le
    (S.configuration n).projectedGraph (S.cutoff n) v).trans
      ((S.configuration n).projectedGraph_degree_le v)

theorem graph_localSparsity (S : ConfigurationSelectionData d r gamma)
    (n : ℕ) (hn : 2 ≤ n)
    (U : Finset (Fin (appendixPlantSize r n))) (hUtwo : 2 ≤ U.card)
    (hUsize : (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma) :
    (deterministicInducedEdgeCount (S.graph n) U : ℝ) ≤
      (1 + S.A / Real.log (n : ℝ)) * (U.card : ℝ) := by
  calc
    (deterministicInducedEdgeCount (S.graph n) U : ℝ) ≤
        (deterministicInducedEdgeCount
          (S.configuration n).projectedGraph U : ℝ) := by
      exact_mod_cast shortCyclePrunedGraph_inducedEdgeCount_le
        (S.configuration n).projectedGraph (S.cutoff n) U
    _ ≤ _ := S.localSparsity n hn U hUtwo hUsize

theorem graph_girth (S : ConfigurationSelectionData d r gamma) (n : ℕ) :
    HasRealGirthAtLeast (S.graph n) (S.kappa * Real.log (n : ℝ)) := by
  intro v p hp
  exact (S.cutoff_lower n).trans
    (shortCyclePrunedGraph_hasRealGirthAtLeast
      (S.configuration n).projectedGraph (S.cutoff n) v p hp)

/-- The two defect counts give an exact finite edge bookkeeping identity. -/
theorem graph_edge_add_losses (S : ConfigurationSelectionData d r gamma)
    (n : ℕ) :
    (S.graph n).edgeFinset.card +
        (shortCycleEdges (S.configuration n).projectedGraph (S.cutoff n)).card +
        (S.configuration n).projectionDefect =
      appendixPlantSize r n * d := by
  let G := (S.configuration n).projectedGraph
  let R := shortCycleEdges G (S.cutoff n)
  have hRsubset : R ⊆ G.edgeFinset := shortCycleEdges_subset_edgeFinset G (S.cutoff n)
  have hprune : (S.graph n).edgeFinset.card + R.card = G.edgeFinset.card := by
    rw [graph, shortCyclePrunedGraph_edgeFinset_card]
    exact Nat.sub_add_cancel (Finset.card_le_card hRsubset)
  have hprojection := (S.configuration n).projectedGraph_card_add_projectionDefect
  have heven : appendixPlantSize r n * (d + d) / 2 =
      appendixPlantSize r n * d := by
    calc
      appendixPlantSize r n * (d + d) / 2 =
          (appendixPlantSize r n * d + appendixPlantSize r n * d) / 2 := by
        rw [Nat.mul_add]
      _ = appendixPlantSize r n * d := by omega
  rw [heven] at hprojection
  change G.edgeFinset.card + (S.configuration n).projectionDefect =
    appendixPlantSize r n * d at hprojection
  calc
    (S.graph n).edgeFinset.card + R.card +
        (S.configuration n).projectionDefect =
        G.edgeFinset.card + (S.configuration n).projectionDefect := by
      rw [hprune]
    _ = appendixPlantSize r n * d := hprojection

/-- Dividing the exact bookkeeping identity by `mₙ` gives the pointwise
density formula whenever `mₙ > 0`. -/
theorem graph_edgeDensity_eq_sub_losses (S : ConfigurationSelectionData d r gamma)
    (n : ℕ) (hm : 0 < appendixPlantSize r n) :
    ((S.graph n).edgeFinset.card : ℝ) / (appendixPlantSize r n : ℝ) =
      (d : ℝ) -
        ((shortCycleEdges (S.configuration n).projectedGraph
          (S.cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ) -
        ((S.configuration n).projectionDefect : ℝ) /
          (appendixPlantSize r n : ℝ) := by
  have hsum := S.graph_edge_add_losses n
  have hmReal : (appendixPlantSize r n : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsumReal :
      ((S.graph n).edgeFinset.card : ℝ) +
          ((shortCycleEdges (S.configuration n).projectedGraph
            (S.cutoff n)).card : ℝ) +
          ((S.configuration n).projectionDefect : ℝ) =
        (appendixPlantSize r n : ℝ) * (d : ℝ) := by
    exact_mod_cast hsum
  field_simp [hmReal]
  linarith [hsumReal]

theorem graph_edgeDensity (S : ConfigurationSelectionData d r gamma)
    (hr : 0 < r) :
    Tendsto
      (fun n ↦ ((S.graph n).edgeFinset.card : ℝ) /
        (appendixPlantSize r n : ℝ))
      atTop (nhds (((d + d : ℕ) : ℝ) / 2)) := by
  have hmTop := appendixPlantSize_tendsto_atTop hr
  have hmPos : ∀ᶠ n : ℕ in atTop, 0 < appendixPlantSize r n :=
    hmTop.eventually_gt_atTop 0
  have heq : ∀ᶠ n : ℕ in atTop,
      ((S.graph n).edgeFinset.card : ℝ) / (appendixPlantSize r n : ℝ) =
        (d : ℝ) -
          ((shortCycleEdges (S.configuration n).projectedGraph
            (S.cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ) -
          ((S.configuration n).projectionDefect : ℝ) /
            (appendixPlantSize r n : ℝ) := by
    filter_upwards [hmPos] with n hn
    exact S.graph_edgeDensity_eq_sub_losses n hn
  have hlimit : Tendsto
      (fun n ↦ (d : ℝ) -
        ((shortCycleEdges (S.configuration n).projectedGraph
          (S.cutoff n)).card : ℝ) / (appendixPlantSize r n : ℝ) -
        ((S.configuration n).projectionDefect : ℝ) /
          (appendixPlantSize r n : ℝ))
      atTop (nhds (d : ℝ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub S.shortCycleLossVanishes).sub
        S.projectionDefectVanishes
  have hmain := hlimit.congr' (Filter.EventuallyEq.symm heq)
  convert hmain using 1
  push_cast
  ring

/-- The deterministic finite selection data packages directly into the
paper-facing witness of Appendix Lemma A.1. -/
noncomputable def toDeterministicPlantWitness
    (S : ConfigurationSelectionData d r gamma) (hr : 0 < r) :
    DeterministicPlantWitness (d + d) r gamma where
  A := S.A
  kappa := S.kappa
  A_pos := S.A_pos
  kappa_pos := S.kappa_pos
  graph := S.graph
  maxDegree := S.graph_maxDegree
  localSparsity := S.graph_localSparsity
  girth := S.graph_girth
  edgeDensity := S.graph_edgeDensity hr

end ConfigurationSelectionData

end

end LowDegree
