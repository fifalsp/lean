import LowDegree.Probability.Dirac
import LowDegree.SupercriticalStatistical

/-!
# Scan test for a deterministic planted graph sequence

The revised appendix plants one fixed graph on `m_n` vertices, uniformly
injects it into the ambient `n` vertices, and then applies edge noise.  The
scan analysis already proved for arbitrary finite plant laws specializes to
this point-mass source law.  This module records that specialization without
introducing any additional probabilistic assumption on the deterministic
graphs beyond their asymptotic edge density.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The point-mass law of one deterministic source edge set. -/
noncomputable def deterministicSourcePlantLaw {m : Nat}
    (A : Finset (AmbientEdge m)) : FiniteLaw (Finset (AmbientEdge m)) :=
  FiniteLaw.dirac A

/-- Uniformly inject a fixed `m_n`-vertex plant into the ambient `n` vertices. -/
noncomputable def deterministicInjectedPlantLaw
    (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n))) (n : Nat) :
    FiniteLaw (Finset (AmbientEdge n)) :=
  uniformlyInjectedPlantLaw (hfit n) (deterministicSourcePlantLaw (A n))

/-- The observation law before noise for a uniformly injected deterministic
plant. -/
noncomputable def deterministicAlternativeLaw
    (c : Real) (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n))) (n : Nat) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  randomForcedLaw (sparseBernoulliParameter c n)
    (deterministicInjectedPlantLaw m hfit A n)

/-- The deterministic alternative after retaining every planted edge with
probability `1-epsilon` and superposing the result on the null graph. -/
noncomputable def deterministicNoisedAlternativeLaw
    (epsilon : NoiseRate) (c : Real)
    (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n))) (n : Nat) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  randomForcedLaw (sparseBernoulliParameter c n)
    (retainedRandomPlantLaw (retentionParameter epsilon)
      (deterministicInjectedPlantLaw m hfit A n))

/-- The generative retained-edge law is exactly the paper's noise operator
applied to the deterministic planted observation law. -/
theorem resampleLaw_deterministicAlternativeLaw
    (epsilon : NoiseRate) (c : Real)
    (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n))) (n : Nat) :
    resampleLaw (sparseBernoulliParameter c n) epsilon
        (deterministicAlternativeLaw c m hfit A n) =
      deterministicNoisedAlternativeLaw epsilon c m hfit A n := by
  unfold deterministicAlternativeLaw deterministicNoisedAlternativeLaw
  exact resampleLaw_randomForcedLaw_eq_retainedRandomPlantLaw
    (sparseBernoulliParameter c n) epsilon
    (deterministicInjectedPlantLaw m hfit A n)

/-- Under a point-mass source law, convergence of the deterministic edge
density is convergence in probability of the sampled source edge density. -/
theorem deterministicSource_edgeDensity_tendstoInProbability
    (m : Nat -> Nat) (A : forall n, Finset (AmbientEdge (m n))) (a : Real)
    (hA : Tendsto (fun n => (A n).card / (m n : Real)) atTop (nhds a)) :
    TendstoInProbability
      (fun n => deterministicSourcePlantLaw (A n))
      (fun n B => (B.card : Real) / (m n : Real)) a := by
  exact tendstoInProbability_dirac A
    (fun n B => (B.card : Real) / (m n : Real)) a hA

/-- Exact finite-`n` scan lower bound for a retained deterministic plant. -/
theorem deterministicNoisedAlternativeLaw_prob_scan_ge
    (epsilon : NoiseRate) (c tau : Real)
    (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n))) (n : Nat) :
    (retainedRandomPlantLaw (retentionParameter epsilon)
        (deterministicInjectedPlantLaw m hfit A n)).prob
      (FiniteLaw.event fun B => Nat.ceil (tau * (m n : Real)) <= B.card) <=
    (deterministicNoisedAlternativeLaw epsilon c m hfit A n).prob
      (graphScanRejectEvent n (m n) (Nat.ceil (tau * (m n : Real)))) := by
  unfold deterministicNoisedAlternativeLaw
  apply randomForcedLaw_prob_graphScanRejectEvent_ge
  intro B hB
  exact retainedUniformlyInjectedPlantLaw_mass_pos_fits
    (hfit n) (retentionParameter epsilon)
    (deterministicSourcePlantLaw (A n)) hB

/-- Paper Appendix A's scan-test argument for an arbitrary deterministic
plant sequence.  If the source has edge density `D/2+o(1)` and the retained
density exceeds one, then its noised uniformly planted law has total
variation tending to one from `G(n,c/n)`. -/
theorem deterministic_statisticalDistinguishability
    (epsilon : NoiseRate) (c : Real) (D : Nat)
    (m : Nat -> Nat) (hfit : forall n, m n <= n)
    (A : forall n, Finset (AmbientEdge (m n)))
    (hc : 0 < c)
    (hm : Tendsto m atTop atTop)
    (hratio : Vanishes fun n => (m n : Real) / (n : Real))
    (hdensity : Tendsto
      (fun n => ((A n).card : Real) / (m n : Real))
      atTop (nhds ((D : Real) / 2)))
    (hsuper : 1 < (1 - (epsilon : Real)) * (D : Real) / 2) :
    TendsToOne fun n =>
      (deterministicNoisedAlternativeLaw epsilon c m hfit A n).tv
        (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)) := by
  let tau : Real := appendixCanonicalScanFactor epsilon (D : Real)
  have htauRange : tau ∈ Set.Ioo (1 : Real) 2 :=
    appendixCanonicalScanFactor_mem_Ioo epsilon (D : Real) hsuper
  have htauDensity :
      tau < (1 - (epsilon : Real)) * (D : Real) / 2 :=
    appendixCanonicalScanFactor_lt_density epsilon (D : Real) hsuper
  have hsource : TendstoInProbability
      (fun n => deterministicSourcePlantLaw (A n))
      (fun n B => (B.card : Real) / (m n : Real))
      ((D : Real) / 2) :=
    deterministicSource_edgeDensity_tendstoInProbability m A
      ((D : Real) / 2) hdensity
  have hinjected : TendstoInProbability
      (fun n => deterministicInjectedPlantLaw m hfit A n)
      (fun n B => (B.card : Real) / (m n : Real))
      ((D : Real) / 2) := by
    simpa only [deterministicInjectedPlantLaw,
      deterministicSourcePlantLaw] using
      uniformlyInjectedPlantLaw_edgeDensity_tendstoInProbability
        m (fun n => n) m hfit
        (fun n => deterministicSourcePlantLaw (A n))
        ((D : Real) / 2) hsource
  have hretainedRaw := retainedRandomPlant_edgeDensity_tendstoInProbability
    (fun n => deterministicInjectedPlantLaw m hfit A n)
    (retentionParameter epsilon) m ((D : Real) / 2) hm hinjected
  have hretained : TendstoInProbability
      (fun n => retainedRandomPlantLaw (retentionParameter epsilon)
        (deterministicInjectedPlantLaw m hfit A n))
      (fun n B => (B.card : Real) / (m n : Real))
      ((1 - (epsilon : Real)) * (D : Real) / 2) := by
    simpa only [retentionParameter_p, mul_div_assoc] using hretainedRaw
  have hcard := prob_card_ge_ceil_mul_tendsToOne
    (fun n => retainedRandomPlantLaw (retentionParameter epsilon)
      (deterministicInjectedPlantLaw m hfit A n))
    m ((1 - (epsilon : Real)) * (D : Real) / 2) tau
    hm htauDensity hretained
  have hplant : TendsToOne fun n =>
      (deterministicNoisedAlternativeLaw epsilon c m hfit A n).prob
        (graphScanRejectEvent n (m n) (Nat.ceil (tau * (m n : Real)))) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hcard
      tendsto_const_nhds
      (fun n => deterministicNoisedAlternativeLaw_prob_scan_ge
        epsilon c tau m hfit A n)
      (fun n =>
        (deterministicNoisedAlternativeLaw epsilon c m hfit A n).prob_le_one
          (graphScanRejectEvent n (m n)
            (Nat.ceil (tau * (m n : Real)))))
  apply totalVariation_tendsToOne_of_tests
    (fun n => deterministicNoisedAlternativeLaw epsilon c m hfit A n)
    (fun n => erdosRenyiLaw (n := n) (sparseBernoulliParameter c n))
    (fun n => graphScanRejectEvent n (m n)
      (Nat.ceil (tau * (m n : Real))))
  · exact sparseErdosRenyi_graphScanRejectEvent_vanishes
      c tau hc htauRange m hm hratio
  · exact hplant

end

end LowDegree
