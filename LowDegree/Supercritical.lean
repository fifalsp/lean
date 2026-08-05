import LowDegree.Asymptotics.Basic
import LowDegree.Probability.Finite

/-!
# Supercritical appendix: asymptotic proof kernels

The appendix's random-graph enumeration and concentration estimates must be
proved in the model layer.  Here we verify the reusable limit arguments that
turn those estimates into Lemmas A.2/A.3 and the statistical half of Theorem
A.1.  The names carry a `_core` suffix so these are not confused with a full
formalization of the random graph construction.
-/

namespace LowDegree

open Filter Topology

/-- Union-bound/first-moment limit used for the local-sparsity event. -/
theorem eventually_localSparsity_core
    {badProbability unionBound : ℕ → ℝ}
    (hbad_nonneg : ∀ n, 0 ≤ badProbability n)
    (hunion : ∀ n, badProbability n ≤ unionBound n)
    (hbound : Vanishes unionBound) :
    Vanishes badProbability :=
  squeeze_zero hbad_nonneg hunion hbound

/-- Removing `o(1)` normalized edge mass preserves a limiting edge density.
This is the deterministic limit calculation inside Lemma A.3. -/
theorem truncatedPlant_edgeDensity_core
    {original removed truncated : ℕ → ℝ} {density : ℝ}
    (hidentity : ∀ n, truncated n = original n - removed n)
    (horiginal : Tendsto original atTop (𝓝 density))
    (hremoved : Vanishes removed) :
    Tendsto truncated atTop (𝓝 density) := by
  have hsub : Tendsto (fun n ↦ original n - removed n) atTop (𝓝 (density - 0)) :=
    horiginal.sub hremoved
  have hfun : truncated = fun n ↦ original n - removed n := funext hidentity
  rw [hfun]
  simpa only [sub_zero] using hsub

/-- Error probabilities for a separating scan test. -/
structure TestSeparationCertificate where
  nullReject : ℕ → ℝ
  plantedMiss : ℕ → ℝ
  totalVariation : ℕ → ℝ
  tv_le_one : ∀ n, totalVariation n ≤ 1
  test_le_tv : ∀ n,
    1 - nullReject n - plantedMiss n ≤ totalVariation n

namespace TestSeparationCertificate

/-- A test with both errors tending to zero forces TV to tend to one.  This is
the final scan-statistic argument in Theorem A.1. -/
theorem totalVariation_tendsToOne (C : TestSeparationCertificate)
    (hnull : Vanishes C.nullReject)
    (hplant : Vanishes C.plantedMiss) :
    TendsToOne C.totalVariation := by
  have hlower : Tendsto
      (fun n ↦ 1 - C.nullReject n - C.plantedMiss n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hnull).sub hplant
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    C.test_le_tv C.tv_le_one

end TestSeparationCertificate

/-- Finite-law version of the scan-test conclusion: if an event has null
probability tending to zero and planted probability tending to one, then the
two laws have total variation tending to one. -/
theorem totalVariation_tendsToOne_of_tests
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (planted null : ∀ n, FiniteLaw (Ω n))
    (reject : ∀ n, Finset (Ω n))
    (hnull : Vanishes (fun n ↦ (null n).prob (reject n)))
    (hplanted : TendsToOne (fun n ↦ (planted n).prob (reject n))) :
    TendsToOne (fun n ↦ (planted n).tv (null n)) := by
  have hdiff : Tendsto
      (fun n ↦ (planted n).prob (reject n) - (null n).prob (reject n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using hplanted.sub hnull
  have habs : Tendsto
      (fun n ↦ |(planted n).prob (reject n) - (null n).prob (reject n)|)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (continuous_abs.tendsto 1).comp hdiff
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le habs tendsto_const_nhds
    (fun n ↦ FiniteLaw.abs_prob_sub_prob_le_tv (planted n) (null n) (reject n))
    (fun n ↦ FiniteLaw.tv_le_one (planted n) (null n))

end LowDegree
