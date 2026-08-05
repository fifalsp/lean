import LowDegree.Asymptotics.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Critical/subcritical proof kernels

The graph-theoretic cycle encoding and the finite Bernoulli model are separate
dependencies.  This module verifies the asymptotic contradiction, first-moment,
and forest-truncation steps used in Theorem 1.2.
-/

namespace LowDegree

open Filter Topology

/-- Abstract contradiction step behind Lemma 3.3: a uniformly positive
penalty cannot occur eventually when the entire low-degree excess vanishes. -/
theorem no_shortCycles_of_lowDegree_core
    {hasShortCycle : ℕ → Prop} {lowDegreeExcess : ℕ → ℝ}
    (hlow : Vanishes lowDegreeExcess)
    (hpenalty : ∀ᶠ n in atTop, hasShortCycle n → (3 : ℝ) ≤ lowDegreeExcess n) :
    ∀ᶠ n in atTop, ¬hasShortCycle n := by
  have hsmall : ∀ᶠ n in atTop, lowDegreeExcess n < 3 :=
    (tendsto_order.1 hlow).2 3 (by norm_num)
  filter_upwards [hpenalty, hsmall] with n hpen hlt
  intro hcycle
  exact (not_le_of_gt hlt) (hpen hcycle)

/-- First-moment step in Lemma 4.6.  The graph-specific cycle encoding supplies
the expected-count majorant. -/
theorem percolatedPlant_acyclic_inProbability_core
    {cycleProbability expectedCycleCount : ℕ → ℝ}
    (hprob_nonneg : ∀ n, 0 ≤ cycleProbability n)
    (hfirstMoment : ∀ n, cycleProbability n ≤ expectedCycleCount n)
    (hexpect : Vanishes expectedCycleCount) :
    Vanishes cycleProbability :=
  squeeze_zero hprob_nonneg hfirstMoment hexpect

/-- Scalar form of the forest-truncation comparison.  `cycleProbability`
bounds the coupling failure event; `truncatedTV` is controlled by its `L²`
second moment. -/
structure ForestTruncationCertificate where
  actualTV : ℕ → ℝ
  truncatedTV : ℕ → ℝ
  cycleProbability : ℕ → ℝ
  actualTV_nonneg : ∀ n, 0 ≤ actualTV n
  actualTV_le : ∀ n, actualTV n ≤ cycleProbability n + truncatedTV n

namespace ForestTruncationCertificate

/-- Triangle/coupling endgame of Theorem 1.2.  Notice that the conclusion is
TV only, matching the manuscript; no full noised-`L²` conclusion is asserted. -/
theorem totalVariation_vanishes (C : ForestTruncationCertificate)
    (hcycle : Vanishes C.cycleProbability)
    (htruncated : Vanishes C.truncatedTV) :
    Vanishes C.actualTV := by
  apply squeeze_zero (fun n ↦ C.actualTV_nonneg n) (fun n ↦ C.actualTV_le n)
  exact hcycle.add htruncated

end ForestTruncationCertificate

end LowDegree
