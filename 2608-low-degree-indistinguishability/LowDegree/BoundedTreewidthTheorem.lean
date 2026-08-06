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

/-- The actual numerical treewidth of the `n`th planted graph.  The revised
paper statement is phrased using this sequence, rather than an auxiliary
upper-bound sequence. -/
noncomputable def numericalTreewidth (M : BoundedTreewidthPlantModel)
    (n : ℕ) : ℕ :=
  TreeDecomposition.treewidth (M.plant n)

/-- The plant model used to bridge the revised product scale to the original
`(kₙ+1) log n` proof.  On zero-treewidth indices its cutoff is increased to
`n+1`; those plants are edgeless, so every likelihood observable is unchanged. -/
noncomputable def zeroWidthRepairedModel (M : BoundedTreewidthPlantModel) :
    BoundedTreewidthPlantModel where
  backgroundDensity := M.backgroundDensity
  backgroundDensity_pos := M.backgroundDensity_pos
  plant := M.plant
  treewidthBound := M.numericalTreewidth
  treewidth_le := fun n ↦
    TreeDecomposition.hasTreewidthAtMost_treewidth (M.plant n)
  degreeCutoff :=
    zeroWidthRepairedDegreeCutoff M.numericalTreewidth M.degreeCutoff
  degreeCutoff_pos :=
    zeroWidthRepairedDegreeCutoff_pos M.degreeCutoff_pos

/-- Zero numerical treewidth means that the planted graph is edgeless. -/
theorem plant_eq_bot_of_numericalTreewidth_eq_zero
    (M : BoundedTreewidthPlantModel) {n : ℕ}
    (hzero : M.numericalTreewidth n = 0) :
    M.plant n = ⊥ := by
  apply TreeDecomposition.eq_bot_of_hasTreewidthAtMost_zero
  have htw := TreeDecomposition.hasTreewidthAtMost_treewidth (M.plant n)
  change TreeDecomposition.HasTreewidthAtMost
    (M.plant n) (M.numericalTreewidth n) at htw
  simpa only [hzero] using htw

/-- Repairing the cutoff on zero-width indices leaves the concrete
low-degree norm unchanged. -/
theorem zeroWidthRepairedModel_lowDegreeNormSq
    (M : BoundedTreewidthPlantModel) (n : ℕ) :
    M.zeroWidthRepairedModel.lowDegreeNormSq n = M.lowDegreeNormSq n := by
  by_cases hzero : M.numericalTreewidth n = 0
  · have hbot := M.plant_eq_bot_of_numericalTreewidth_eq_zero hzero
    simp [BoundedTreewidthPlantModel.lowDegreeNormSq,
      BoundedTreewidthPlantModel.parameter,
      zeroWidthRepairedModel, hbot]
  · simp [BoundedTreewidthPlantModel.lowDegreeNormSq,
      BoundedTreewidthPlantModel.parameter,
      zeroWidthRepairedModel, zeroWidthRepairedDegreeCutoff, hzero]

@[simp]
theorem zeroWidthRepairedModel_noisedNormSq
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    M.zeroWidthRepairedModel.noisedNormSq noise n = M.noisedNormSq noise n :=
  rfl

@[simp]
theorem zeroWidthRepairedModel_noisedTotalVariation
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    M.zeroWidthRepairedModel.noisedTotalVariation noise n =
      M.noisedTotalVariation noise n :=
  rfl

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

/-- **Revised paper Theorem 1.1 (numerical-treewidth product scale).**

This is the exact formal counterpart of
`tw(Γₙ) = o(Dₙ / log n)`: the hypothesis is written without division as
`tw(Γₙ) log n = o(Dₙ)`.  Positive-width indices reduce to the original
theorem because `tw+1 ≤ 2 tw`.  At zero-width indices the plant is edgeless;
the cutoff repair above supplies the missing logarithmic scale while leaving
all likelihood quantities exactly unchanged. -/
theorem main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthProductDegreeScale
      M.numericalTreewidth M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation := by
  let R := M.zeroWidthRepairedModel
  have hRscale : TreewidthDegreeScale R.treewidthBound R.degreeCutoff := by
    simpa only [R, zeroWidthRepairedModel] using hscale.repaired
  have hRlow : TendsToOne R.lowDegreeNormSq := by
    rw [show R.lowDegreeNormSq = M.lowDegreeNormSq by
      funext n
      exact M.zeroWidthRepairedModel_lowDegreeNormSq n]
    exact hlow
  have hR := R.main_lowDegree_to_noisedL2_and_tv hRscale hRlow
  simpa only [R, FixedNoiseConclusion,
    zeroWidthRepairedModel_noisedNormSq,
    zeroWidthRepairedModel_noisedTotalVariation] using hR

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

/-- Root-namespace alias for the revised numerical-treewidth statement. -/
theorem main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthProductDegreeScale
      M.numericalTreewidth M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation :=
  M.main_lowDegree_to_noisedL2_and_tv_of_numericalTreewidth hscale hlow

end LowDegree
