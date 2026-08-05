import LowDegree.Asymptotics.BetaMass
import LowDegree.Asymptotics.ConnectedBetaMass
import LowDegree.Main

/-!
# Model-facing endgame for the bounded-treewidth theorem

These theorems assemble the exact classwise Fourier identities, the leading
weight transfer, the cluster-expansion limit, and the finite-law TV bound.
-/

namespace LowDegree

open Filter Topology

namespace BoundedTreewidthPlantModel

/-- Once the connected leading mass vanishes and the component injection
supplies the geometric majorant, the full noised leading mass vanishes. -/
theorem noisedBetaMass_vanishes_of_connected
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (hconnected : Vanishes (M.connectedNoisedBetaMass noise))
    (hcluster : ∀ᶠ n in atTop,
      M.noisedBetaMass noise n ≤
        M.connectedNoisedBetaMass noise n /
          (1 - M.connectedNoisedBetaMass noise n)) :
    Vanishes (M.noisedBetaMass noise) := by
  have hnonneg : ∀ n, 0 ≤ M.noisedBetaMass noise n := by
    intro n
    exact Finset.sum_nonneg fun C _ ↦ by
      exact mul_nonneg
        (pow_nonneg (sub_nonneg.mpr noise.2.2.le) _)
        (by
          unfold FiniteGraphShape.graphBetaWeight betaWeight
          exact mul_nonneg
            (div_nonneg
              (div_nonneg (pow_nonneg (Nat.cast_nonneg n) C.shape.edgeCount)
                (pow_nonneg (Nat.cast_nonneg n) C.shape.vertexCount))
              (pow_nonneg M.backgroundDensity_pos.le C.shape.edgeCount))
            (mul_nonneg
              (sq_nonneg (C.shape.nonInducedCopyCount (M.plant n) : ℝ))
              (Nat.cast_nonneg _)))
  have htail := geometricTail_vanishes hconnected
  exact squeeze_zero' (Eventually.of_forall hnonneg) hcluster htail

/-- All graph-specific work in Theorem 1.1 reduces to the vanishing of the
full noised leading mass.  The conclusion here concerns the actual noised
likelihood and actual finite-law total variation. -/
theorem fixedNoiseConclusion_of_noisedBetaMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (hbeta : ∀ noise : NoiseRate, Vanishes (M.noisedBetaMass noise)) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation := by
  apply SecondMomentCertificate.fixedNoiseConclusion_of_model
  intro noise
  exact M.noisedNormSq_tendsToOne_of_betaMass_vanishes
    hlow noise (hbeta noise)

/-- End-to-end version with the connected-mass and component-expansion
outputs exposed as the two remaining combinatorial inputs. -/
theorem fixedNoiseConclusion_of_connectedMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (hconnected : ∀ noise : NoiseRate,
      Vanishes (M.connectedNoisedBetaMass noise))
    (hcluster : ∀ noise : NoiseRate, ∀ᶠ n in atTop,
      M.noisedBetaMass noise n ≤
        M.connectedNoisedBetaMass noise n /
          (1 - M.connectedNoisedBetaMass noise n)) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation := by
  apply M.fixedNoiseConclusion_of_noisedBetaMass hlow
  intro noise
  exact M.noisedBetaMass_vanishes_of_connected noise
    (hconnected noise) (hcluster noise)

end BoundedTreewidthPlantModel

end LowDegree
