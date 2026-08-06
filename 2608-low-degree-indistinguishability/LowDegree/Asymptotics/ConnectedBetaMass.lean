import LowDegree.Asymptotics.BetaMass
import LowDegree.Asymptotics.ConnectedUpperBound

/-!
# Small, block, and large connected leading masses

This file formalizes the small-support and block-mass parts of paper Lemma
4.5.  The remaining large-support inequality is the aggregate restriction
injection supplied by the treewidth-division layer.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace BoundedTreewidthPlantModel

/-- One graph-class summand in the full noised leading mass. -/
noncomputable def noisedBetaClassWeight
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) {n : ℕ}
    (C : AmbientSupportClass n) : ℝ :=
  (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
    C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

/-- The connected mass `θ_{n,ε}` from paper Lemmas 4.4--4.5. -/
noncomputable def connectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with C.shape.graph.Connected,
    M.noisedBetaClassWeight noise C

/-- Connected contribution with fewer than `ℓₙ` edges. -/
noncomputable def smallConnectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (ℓ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.edgeCount < ℓ n,
    M.noisedBetaClassWeight noise C

/-- Connected contribution with at least `ℓₙ` edges. -/
noncomputable def largeConnectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (ℓ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ ℓ n ≤ C.shape.edgeCount,
    M.noisedBetaClassWeight noise C

/-- Unnoised leading mass of possible decomposition pieces with edge counts
in `[ℓₙ,3ℓₙ]`. -/
noncomputable def blockBetaMass
    (M : BoundedTreewidthPlantModel) (ℓ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      ℓ n ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * ℓ n,
    C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

private theorem classBeta_nonneg
    (M : BoundedTreewidthPlantModel) {n : ℕ}
    (C : AmbientSupportClass n) :
    0 ≤ C.shape.graphBetaWeight M.backgroundDensity n (M.plant n) := by
  unfold FiniteGraphShape.graphBetaWeight betaWeight
  exact mul_nonneg
    (div_nonneg
      (div_nonneg (pow_nonneg (Nat.cast_nonneg n) C.shape.edgeCount)
        (pow_nonneg (Nat.cast_nonneg n) C.shape.vertexCount))
      (pow_nonneg M.backgroundDensity_pos.le C.shape.edgeCount))
    (mul_nonneg
      (sq_nonneg (C.shape.nonInducedCopyCount (M.plant n) : ℝ))
      (Nat.cast_nonneg _))

private theorem noisedClassBeta_nonneg
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) {n : ℕ}
    (C : AmbientSupportClass n) :
    0 ≤ M.noisedBetaClassWeight noise C := by
  exact mul_nonneg
    (pow_nonneg (sub_nonneg.mpr noise.2.2.le) _)
    (classBeta_nonneg M C)

/-- The connected mass splits exactly into its small- and large-edge parts. -/
theorem connectedNoisedBetaMass_eq_small_add_large
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (ℓ : ℕ → ℕ) (n : ℕ) :
    M.connectedNoisedBetaMass noise n =
      M.smallConnectedNoisedBetaMass noise ℓ n +
        M.largeConnectedNoisedBetaMass noise ℓ n := by
  unfold connectedNoisedBetaMass smallConnectedNoisedBetaMass
    largeConnectedNoisedBetaMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _hC
  by_cases hconn : C.shape.graph.Connected
  · by_cases hedge : C.shape.edgeCount < ℓ n
    · have hedge' : C.representative.1.card < ℓ n := by
        rw [← C.shape_edgeCount_eq_representative_card]
        exact hedge
      simp [hconn, hedge']
    · have hle : ℓ n ≤ C.shape.edgeCount := Nat.le_of_not_gt hedge
      have hle' : ℓ n ≤ C.representative.1.card := by
        rw [← C.shape_edgeCount_eq_representative_card]
        exact hle
      simp [hconn, hle']
  · simp [hconn]

/-- Fixed-rate noise can only decrease a nonnegative class weight. -/
private theorem noisedBetaClassWeight_le_beta
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) {n : ℕ}
    (C : AmbientSupportClass n) :
    M.noisedBetaClassWeight noise C ≤
      C.shape.graphBetaWeight M.backgroundDensity n (M.plant n) := by
  unfold noisedBetaClassWeight
  have hbase0 : 0 ≤ 1 - (noise : ℝ) := sub_nonneg.mpr noise.2.2.le
  have hbase1 : 1 - (noise : ℝ) ≤ 1 := by linarith [noise.2.1]
  exact mul_le_of_le_one_left (classBeta_nonneg M C)
    (pow_le_one₀ hbase0 hbase1)

/-- Equation (4.5), pointwise form: when `ℓₙ ≤ Dₙ`, the small
connected noised mass is bounded by the full low-degree `β` mass. -/
theorem smallConnectedNoisedBetaMass_le_lowDegreeBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (ℓ : ℕ → ℕ) {n : ℕ} (hℓD : ℓ n ≤ M.degreeCutoff n) :
    M.smallConnectedNoisedBetaMass noise ℓ n ≤
      M.lowDegreeBetaMass n := by
  unfold smallConnectedNoisedBetaMass lowDegreeBetaMass
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro C _hC
  by_cases hsmall : C.shape.graph.Connected ∧ C.shape.edgeCount < ℓ n
  · have hdegree : C.shape.edgeCount ≤ M.degreeCutoff n :=
      (Nat.le_of_lt hsmall.2).trans hℓD
    simp only [if_pos hsmall, if_pos hdegree]
    exact noisedBetaClassWeight_le_beta M noise C
  · simp only [if_neg hsmall]
    split
    · exact classBeta_nonneg M C
    · exact le_rfl

/-- A block range lying below `Dₙ` is part of the low-degree `β` mass. -/
theorem blockBetaMass_le_lowDegreeBetaMass
    (M : BoundedTreewidthPlantModel) (ℓ : ℕ → ℕ)
    {n : ℕ} (hthree : 3 * ℓ n ≤ M.degreeCutoff n) :
    M.blockBetaMass ℓ n ≤ M.lowDegreeBetaMass n := by
  unfold blockBetaMass lowDegreeBetaMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact hC.2.trans hthree
  · intro C _hC _hnot
    exact classBeta_nonneg M C

/-- The small connected term in Equation (4.5) is `o(1)`. -/
theorem smallConnectedNoisedBetaMass_vanishes
    (M : BoundedTreewidthPlantModel) (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate) (ℓ : ℕ → ℕ)
    (hℓD : ∀ᶠ n in atTop, ℓ n ≤ M.degreeCutoff n) :
    Vanishes (M.smallConnectedNoisedBetaMass noise ℓ) := by
  have hbeta := M.lowDegreeBetaMass_vanishes hlow
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun C _ ↦ noisedClassBeta_nonneg M noise C
  · filter_upwards [hℓD] with n hn
    exact M.smallConnectedNoisedBetaMass_le_lowDegreeBetaMass noise ℓ hn
  · exact hbeta

/-- The decomposition block mass is `o(1)` whenever `3ℓₙ ≤ Dₙ`
eventually. -/
theorem blockBetaMass_vanishes
    (M : BoundedTreewidthPlantModel) (hlow : TendsToOne M.lowDegreeNormSq)
    (ℓ : ℕ → ℕ)
    (hthree : ∀ᶠ n in atTop, 3 * ℓ n ≤ M.degreeCutoff n) :
    Vanishes (M.blockBetaMass ℓ) := by
  have hbeta := M.lowDegreeBetaMass_vanishes hlow
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun C _ ↦ classBeta_nonneg M C
  · filter_upwards [hthree] with n hn
    exact M.blockBetaMass_le_lowDegreeBetaMass ℓ hn
  · exact hbeta

/-- Closure of paper Lemma 4.5 once the aggregate large-support injection
supplies its geometric majorant. -/
theorem connectedNoisedBetaMass_vanishes_of_large_bound
    (M : BoundedTreewidthPlantModel) (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate) (ℓ : ℕ → ℕ)
    (hthree : ∀ᶠ n in atTop, 3 * ℓ n ≤ M.degreeCutoff n)
    (hlarge : ∀ᶠ n in atTop,
      M.largeConnectedNoisedBetaMass noise ℓ n ≤
        M.blockBetaMass ℓ n / (1 - M.blockBetaMass ℓ n)) :
    Vanishes (M.connectedNoisedBetaMass noise) := by
  have hsmall := M.smallConnectedNoisedBetaMass_vanishes hlow noise ℓ
    (hthree.mono fun n hn ↦ (Nat.le_mul_of_pos_left _ (by norm_num)).trans hn)
  have hblock := M.blockBetaMass_vanishes hlow ℓ hthree
  apply connectedNoisedMass_vanishes_of_decomposition
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun C _ ↦ noisedClassBeta_nonneg M noise C
  · exact hsmall
  · exact hblock
  · filter_upwards [hlarge] with n hn
    rw [M.connectedNoisedBetaMass_eq_small_add_large noise ℓ n]
    exact add_le_add_left hn _

end BoundedTreewidthPlantModel

end

end LowDegree
