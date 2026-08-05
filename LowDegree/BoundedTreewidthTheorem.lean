import LowDegree.Asymptotics.BoundedTreewidthEndgame
import LowDegree.Asymptotics.LargeConnectedBetaMass
import LowDegree.Combinatorics.GraphComponentExpansion

/-!
# The bounded-treewidth low-degree consequence

This module assembles the graph decomposition, connected-mass estimate,
component expansion, exact Fourier comparison, and finite-law second-moment
argument into the paper-facing form of Theorem 1.1.
-/

namespace LowDegree

open Filter Topology

namespace BoundedTreewidthPlantModel

/-- **Paper Theorem 1.1 (bounded-treewidth low-degree consequence).**

For every fixed edge-noise rate in `(0,1)`, a planted sequence satisfying the
treewidth/degree scale and asymptotically trivial low-degree second moment has
full noised second moment tending to one and noised total variation tending
to zero.
-/
theorem main_lowDegree_to_noisedL2_and_tv
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthDegreeScale M.treewidthBound M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation := by
  apply M.fixedNoiseConclusion_of_noisedBetaMass hlow
  intro noise
  apply M.noisedBetaMass_vanishes_of_connectedNoisedBetaMass
    hlow noise
  exact M.connectedNoisedBetaMass_vanishes hscale hlow noise

/-- The proposition-valued statement declared in `LowDegree.Main` is
inhabited by the end-to-end theorem above. -/
theorem main_lowDegree_to_noisedL2_and_tv_statement_proved
    (M : BoundedTreewidthPlantModel) :
    main_lowDegree_to_noisedL2_and_tv_statement M := by
  intro hscale hlow
  exact M.main_lowDegree_to_noisedL2_and_tv hscale hlow

end BoundedTreewidthPlantModel

/-- Root-namespace paper-facing alias for Theorem 1.1. -/
theorem main_lowDegree_to_noisedL2_and_tv
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthDegreeScale M.treewidthBound M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation :=
  M.main_lowDegree_to_noisedL2_and_tv hscale hlow

end LowDegree
