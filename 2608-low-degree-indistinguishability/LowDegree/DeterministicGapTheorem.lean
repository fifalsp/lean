import LowDegree.DeterministicLowDegree
import LowDegree.DeterministicModelBridge

/-!
# The deterministic low-degree--statistical gap

This module packages the graph-theoretic witness from Appendix Lemma A.1
into the two conclusions of revised Appendix Theorem A.2.  The source graph,
its uniformly injected copy, and the canonically padded uniformly permuted
graph have already been identified exactly in
`DeterministicModelBridge.lean`.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- An explicit admissible value of the paper's constant `c₀`.  The first
term makes `c₀>1`; the second is the analytic threshold required by the tree
and cyclic geometric sums. -/
noncomputable def DeterministicPlantWitness.gapThreshold
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma) : Real :=
  max 2 (deterministicLargeCThreshold D W.A r W.kappa)

theorem DeterministicPlantWitness.one_lt_gapThreshold
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma) :
    1 < W.gapThreshold := by
  exact lt_of_lt_of_le (by norm_num) (le_max_left 2 _)

theorem DeterministicPlantWitness.coreThreshold_le_gapThreshold
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma) :
    deterministicLargeCThreshold D W.A r W.kappa <= W.gapThreshold :=
  le_max_right _ _

/-- **Revised Appendix Theorem A.2, fixed-witness form.**

Every deterministic graph sequence satisfying Lemma A.1 has asymptotically
trivial squared low-degree norm at the logarithmic cutoff, while its noisy
planted law has total variation tending to one from `G(n,c/n)`. -/
theorem deterministicGap_of_witness
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma)
    (hD : 6 <= D)
    (hr : r ∈ Set.Ioo (0 : Real) (1 / 2 : Real))
    (hgamma : gamma ∈ Set.Ioo (0 : Real) 1)
    (epsilon : NoiseRate)
    (hsuper : 1 < (1 - (epsilon : Real)) * (D : Real) / 2)
    {c : Real} (hc : W.gapThreshold <= c) :
    TendsToOne (fun n =>
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
        (W.ambientGraph hr n) (appendixDegreeCutoff n)) ∧
    TendsToOne (fun n =>
      plantedNoisedTotalVariation (sparseBernoulliParameter c n) epsilon
        (W.ambientGraph hr n)) := by
  have hcCore :
      deterministicLargeCThreshold D W.A r W.kappa <= c :=
    W.coreThreshold_le_gapThreshold.trans hc
  have hcpos : 0 < c := by
    have htwo : (2 : Real) <= W.gapThreshold := le_max_left _ _
    linarith
  have hcount : forall n e,
      connectedShapeTripleMass (W.ambientGraph hr n) e <=
        appendixPlantSize r n ^ 2 * D ^ (3 * e) := by
    intro n e
    rcases e.eq_zero_or_pos with rfl | he
    · simp
    · exact deterministicConnectedCount (W.ambientGraph hr n)
        (appendixPlantSize r n) D e he hD
        (W.ambientGraph_hasSupportCardAtMost hr n)
        (W.ambientGraph_hasMaximumDegreeAtMost hr n)
  have hrestrictions :=
    W.eventually_occurringConnectedShape_restrictions hr hgamma
  have hlocal : ∀ᶠ n in atTop, forall C : AmbientSupportClass n,
      C.shape.graph.Connected -> ¬C.shape.graph.IsAcyclic ->
      0 < C.shape.nonInducedCopyCount (W.ambientGraph hr n) ->
      C.shape.edgeCount <= appendixDegreeCutoff n ->
      (C.shape.edgeCount : Real) <=
        (1 + W.A / Real.log (n : Real)) * (C.shape.vertexCount : Real) := by
    filter_upwards [hrestrictions] with n hn
    intro C hconn _hcyclic hocc hcutoff
    exact (hn C.shape hconn hocc hcutoff).1
  have hgirth : ∀ᶠ n in atTop, forall C : AmbientSupportClass n,
      C.shape.graph.Connected -> ¬C.shape.graph.IsAcyclic ->
      0 < C.shape.nonInducedCopyCount (W.ambientGraph hr n) ->
      W.kappa * Real.log (n : Real) <= (C.shape.edgeCount : Real) := by
    exact Eventually.of_forall fun n C hconn hcyclic hocc =>
      W.occurringConnectedCyclicShape_girth
        hr n C.shape hconn hcyclic hocc
  have hlow : TendsToOne (fun n =>
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
        (W.ambientGraph hr n) (appendixDegreeCutoff n)) :=
    deterministic_lowDegreeIndistinguishability
      D W.A r W.kappa hr W.A_pos.le W.kappa_pos
      (W.ambientGraph hr) hcount hlocal hgirth hcCore
  let hfit : forall n, appendixPlantSize r n <= n :=
    fun n => appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n
  have hdensity : Tendsto
      (fun n => ((W.sourceEdges n).card : Real) /
        (appendixPlantSize r n : Real))
      atTop (nhds ((D : Real) / 2)) := by
    simpa only [DeterministicPlantWitness.card_sourceEdges] using W.edgeDensity
  have hstatInjected := deterministic_statisticalDistinguishability
    epsilon c D (appendixPlantSize r) hfit W.sourceEdges hcpos
    (appendixPlantSize_tendsto_atTop hr.1)
    (appendixPlantSize_div_index_vanishes (by linarith [hr.2]))
    hdensity hsuper
  have hstat : TendsToOne (fun n =>
      plantedNoisedTotalVariation (sparseBernoulliParameter c n) epsilon
        (W.ambientGraph hr n)) := by
    rw [show (fun n =>
        plantedNoisedTotalVariation (sparseBernoulliParameter c n) epsilon
          (W.ambientGraph hr n)) =
        (fun n =>
          (deterministicNoisedAlternativeLaw epsilon c
            (appendixPlantSize r) hfit W.sourceEdges n).tv
            (erdosRenyiLaw (sparseBernoulliParameter c n))) by
      funext n
      unfold plantedNoisedTotalVariation
      rw [W.deterministicNoisedAlternativeLaw_eq hr epsilon c n]]
    exact hstatInjected
  exact ⟨hlow, hstat⟩

/-- Strong uniform-noise formulation: the threshold depends only on the
deterministic witness (hence on `D,r,gamma` in Lemma A.1), not on the noise
rate.  Every noise rate satisfying the supercritical inequality shares the
same threshold. -/
theorem deterministicGap_exists_threshold_uniform_noise
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma)
    (hD : 6 <= D)
    (hr : r ∈ Set.Ioo (0 : Real) (1 / 2 : Real))
    (hgamma : gamma ∈ Set.Ioo (0 : Real) 1) :
    exists c0 : Real, 1 < c0 ∧ forall epsilon : NoiseRate,
      1 < (1 - (epsilon : Real)) * (D : Real) / 2 ->
      forall c : Real, c0 <= c ->
      TendsToOne (fun n =>
        plantedLowDegreeNormSq (sparseBernoulliParameter c n)
          (W.ambientGraph hr n) (appendixDegreeCutoff n)) ∧
      TendsToOne (fun n =>
        plantedNoisedTotalVariation (sparseBernoulliParameter c n) epsilon
          (W.ambientGraph hr n)) := by
  refine ⟨W.gapThreshold, W.one_lt_gapThreshold, ?_⟩
  intro epsilon hsuper c hc
  exact deterministicGap_of_witness W hD hr hgamma epsilon hsuper hc

/-- Existential formulation matching the manuscript after its noise rate has
been fixed: “there exists `c₀>1` such that for every `c≥c₀`”. -/
theorem deterministicGap_exists_threshold
    {D : Nat} {r gamma : Real} (W : DeterministicPlantWitness D r gamma)
    (hD : 6 <= D)
    (hr : r ∈ Set.Ioo (0 : Real) (1 / 2 : Real))
    (hgamma : gamma ∈ Set.Ioo (0 : Real) 1)
    (epsilon : NoiseRate)
    (hsuper : 1 < (1 - (epsilon : Real)) * (D : Real) / 2) :
    exists c0 : Real, 1 < c0 ∧ forall c : Real, c0 <= c ->
      TendsToOne (fun n =>
        plantedLowDegreeNormSq (sparseBernoulliParameter c n)
          (W.ambientGraph hr n) (appendixDegreeCutoff n)) ∧
      TendsToOne (fun n =>
        plantedNoisedTotalVariation (sparseBernoulliParameter c n) epsilon
          (W.ambientGraph hr n)) := by
  obtain ⟨c0, hc0, hall⟩ :=
    deterministicGap_exists_threshold_uniform_noise W hD hr hgamma
  exact ⟨c0, hc0, hall epsilon hsuper⟩

end

end LowDegree
