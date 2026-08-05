import LowDegree.Asymptotics.Basic
import LowDegree.Combinatorics.TreeDecomposition
import LowDegree.PlantedModel
import LowDegree.Probability.Finite
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic endgame of the bounded-treewidth theorem

This module isolates the parts of Theorem 1.1 that depend only on nonnegative
Fourier mass.  The graph-specific transport and treewidth certificates live in
the combinatorics modules; the exact Bernoulli identities live in `Fourier`.
-/

namespace LowDegree

open Filter Topology

/-- The pointwise-in-noise conclusion of paper Theorem 1.1.

The subtype quantifier is deliberately outside `TendsToOne` and `Vanishes`:
the paper fixes each `ε ∈ (0,1)` before taking `n → ∞`; it does not assert a
limit uniform in `ε`.
-/
def FixedNoiseConclusion
    (noisedNormSq noisedTotalVariation : NoiseRate → ℕ → ℝ) : Prop :=
  ∀ ε : NoiseRate,
    TendsToOne (noisedNormSq ε) ∧ Vanishes (noisedTotalVariation ε)

/-- The concrete model data appearing in paper Theorem 1.1.

Writing each plant on `Fin n` incorporates the printed condition
`|V(Γₙ)| ≤ n`: a smaller plant is represented by adding isolated ambient
vertices.  `treewidthBound` is an upper bound rather than a numerical
treewidth equality, exactly matching what the proof consumes.
-/
structure BoundedTreewidthPlantModel where
  backgroundDensity : ℝ
  backgroundDensity_pos : 0 < backgroundDensity
  plant : (n : ℕ) → SimpleGraph (Fin n)
  treewidthBound : ℕ → ℕ
  treewidth_le : ∀ n,
    TreeDecomposition.HasTreewidthAtMost (plant n) (treewidthBound n)
  degreeCutoff : ℕ → ℕ
  degreeCutoff_pos : ∀ n, 0 < degreeCutoff n

namespace BoundedTreewidthPlantModel

/-- The honest Bernoulli parameter sequence for the sparse background. -/
noncomputable def parameter (M : BoundedTreewidthPlantModel) (n : ℕ) :
    BernoulliParameter :=
  sparseBernoulliParameter M.backgroundDensity n

/-- The model-realized low-degree second moment in Theorem 1.1's premise. -/
noncomputable def lowDegreeNormSq (M : BoundedTreewidthPlantModel) (n : ℕ) : ℝ :=
  plantedLowDegreeNormSq (M.parameter n) (M.plant n) (M.degreeCutoff n)

/-- The model-realized full second moment after fixed-rate edge noise. -/
noncomputable def noisedNormSq (M : BoundedTreewidthPlantModel)
    (ε : NoiseRate) (n : ℕ) : ℝ :=
  plantedNoisedNormSq (M.parameter n) ε (M.plant n)

/-- The actual total variation distance between the noised planted and null
finite laws. -/
noncomputable def noisedTotalVariation (M : BoundedTreewidthPlantModel)
    (ε : NoiseRate) (n : ℕ) : ℝ :=
  plantedNoisedTotalVariation (M.parameter n) ε (M.plant n)

end BoundedTreewidthPlantModel

/-- **Formal statement of paper Theorem 1.1 (proof pending).**

This definition encodes the exact logical implication and quantifier order of
the bounded-treewidth low-degree consequence.  Unlike the earlier scalar
profile, all three observables are definitionally tied to the concrete planted
and noised laws and their likelihood ratios.  It remains a `Prop`, not an axiom
or a proved theorem: the graph-sum transfer and tree-decomposition existence
proof are still required.
-/
def main_lowDegree_to_noisedL2_and_tv_statement
    (M : BoundedTreewidthPlantModel) : Prop :=
  TreewidthDegreeScale M.treewidthBound M.degreeCutoff →
  TendsToOne M.lowDegreeNormSq →
  FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation

/-- The geometric series used in the connected-component cluster expansion. -/
theorem geometric_connected_mass {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∑' m : ℕ, θ ^ (m + 1)) = θ / (1 - θ) := by
  rw [show (∑' m : ℕ, θ ^ (m + 1)) = θ * ∑' m : ℕ, θ ^ m by
    simp_rw [pow_succ']
    exact tsum_mul_left]
  rw [tsum_geometric_of_lt_one hθ0 hθ1]
  simp [div_eq_mul_inv]

/-- Premise-minimized analytic form of Lemma 4.4.

The combinatorial component injection supplies `hmajorize`.  This theorem
checks that the resulting geometric majorant is `o(1)`.
-/
theorem clusterExpansion_bound_core
    {θ total : ℕ → ℝ}
    (hθ : Vanishes θ)
    (htotal_nonneg : ∀ᶠ n in atTop, 0 ≤ total n)
    (hmajorize : ∀ᶠ n in atTop, total n ≤ θ n / (1 - θ n)) :
    Vanishes total := by
  have hden : Tendsto (fun n ↦ 1 - θ n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hθ
  have hfrac : Tendsto (fun n ↦ θ n / (1 - θ n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hθ.div hden (by norm_num : (1 : ℝ) ≠ 0)
  exact squeeze_zero' htotal_nonneg hmajorize hfrac

/-- Paper-faithful wrapper for Lemma 4.4: its printed low-degree premise is
retained even though the analytic proof does not use it. -/
theorem clusterExpansion_bound
    {θ total lowDegreeNormSq : ℕ → ℝ}
    (_hlow : TendsToOne lowDegreeNormSq)
    (hθ : Vanishes θ)
    (htotal_nonneg : ∀ᶠ n in atTop, 0 ≤ total n)
    (hmajorize : ∀ᶠ n in atTop, total n ≤ θ n / (1 - θ n)) :
    Vanishes total :=
  clusterExpansion_bound_core hθ htotal_nonneg hmajorize

/-- Spectral data needed for the last two lines of the proof of Theorem 1.1. -/
structure SecondMomentCertificate where
  normSq : ℕ → ℝ
  totalVariation : ℕ → ℝ
  chiSq_nonneg : ∀ n, 0 ≤ normSq n - 1
  tv_nonneg : ∀ n, 0 ≤ totalVariation n
  tv_le : ∀ n,
    totalVariation n ≤ (1 / 2 : ℝ) * Real.sqrt (normSq n - 1)

namespace SecondMomentCertificate

/-- Build the analytic endgame certificate from actual finite laws and a
pointwise likelihood ratio.  In the model-facing proof, `p n` will be the
noised planted law, `q n` the Erdős--Rényi law, and `L n` the noised
likelihood ratio. -/
noncomputable def ofLikelihood
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p q : ∀ n, FiniteLaw (Ω n))
    (L : ∀ n, Ω n → ℝ)
    (hL : ∀ n, FiniteLaw.IsLikelihoodRatio (p n) (q n) (L n)) :
    SecondMomentCertificate where
  normSq n := (q n).expect (fun ω ↦ (L n ω) ^ 2)
  totalVariation n := (p n).tv (q n)
  chiSq_nonneg n := by
    rw [← FiniteLaw.expect_sq_sub_one (hL n)]
    exact Finset.sum_nonneg fun ω _ ↦
      mul_nonneg ((q n).mass_nonneg ω) (sq_nonneg (L n ω - 1))
  tv_nonneg n := FiniteLaw.tv_nonneg (p n) (q n)
  tv_le n := FiniteLaw.tv_le_half_sqrt_chiSq (hL n)

/-- The analytic certificate attached to the actual noised planted model. -/
noncomputable def ofNoisedPlant
    (M : BoundedTreewidthPlantModel) (ε : NoiseRate) :
    SecondMomentCertificate :=
  ofLikelihood
    (fun n ↦ noisedPlantedLaw (M.parameter n) ε (M.plant n))
    (fun n ↦ erdosRenyiLaw (M.parameter n))
    (fun n ↦ noisedLikelihood (M.parameter n) ε (M.plant n))
    (fun n ↦ noisedLikelihood_isLikelihoodRatio
      (M.parameter n) ε (M.plant n))

@[simp]
theorem ofNoisedPlant_normSq
    (M : BoundedTreewidthPlantModel) (ε : NoiseRate) (n : ℕ) :
    (ofNoisedPlant M ε).normSq n = M.noisedNormSq ε n := by
  simp only [ofNoisedPlant, ofLikelihood, BoundedTreewidthPlantModel.noisedNormSq,
    plantedNoisedNormSq, FiniteLaw.expect, bernoulliInner,
    bernoulliExpectation, erdosRenyiLaw, bernoulliProductLaw]
  apply Finset.sum_congr rfl
  intro x hx
  ring

@[simp]
theorem ofNoisedPlant_totalVariation
    (M : BoundedTreewidthPlantModel) (ε : NoiseRate) (n : ℕ) :
    (ofNoisedPlant M ε).totalVariation n =
      M.noisedTotalVariation ε n :=
  rfl

/-- A noised likelihood ratio with second moment `1+o(1)` has TV `o(1)`.
This is the asymptotic Cauchy--Schwarz step in Theorem 1.1. -/
theorem totalVariation_vanishes (C : SecondMomentCertificate)
    (hnorm : TendsToOne C.normSq) : Vanishes C.totalVariation := by
  have hchi : Tendsto (fun n ↦ C.normSq n - 1) atTop (𝓝 0) :=
    tendsToOne_iff_vanishes_sub.mp hnorm
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (C.normSq n - 1)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hchi)
  have hupper : Tendsto
      (fun n ↦ (1 / 2 : ℝ) * Real.sqrt (C.normSq n - 1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  exact squeeze_zero (fun n ↦ C.tv_nonneg n) (fun n ↦ C.tv_le n) hupper

/-- The exact pair of analytic conclusions asserted in Theorem 1.1 once the
graph/Fourier argument has established the noised second-moment limit. -/
theorem noisedL2_and_tv (C : SecondMomentCertificate)
    (hnorm : TendsToOne C.normSq) :
    TendsToOne C.normSq ∧ Vanishes C.totalVariation :=
  ⟨hnorm, C.totalVariation_vanishes hnorm⟩

/-- The already verified analytic endgame, with the paper's fixed-noise
quantifier made explicit.  Once the graph/Fourier argument supplies the
noised second-moment limit for every fixed noise rate, TV convergence follows
for every such rate as well.
-/
theorem fixedNoiseConclusion
    (C : NoiseRate → SecondMomentCertificate)
    (hnorm : ∀ ε : NoiseRate, TendsToOne (C ε).normSq) :
    FixedNoiseConclusion
      (fun ε ↦ (C ε).normSq)
      (fun ε ↦ (C ε).totalVariation) := by
  intro ε
  exact (C ε).noisedL2_and_tv (hnorm ε)

/-- Model-realized analytic endgame: once the graph argument proves the full
noised second moment for each fixed rate, the paper's TV conclusion follows
for the actual planted and null laws. -/
theorem fixedNoiseConclusion_of_model
    (M : BoundedTreewidthPlantModel)
    (hnorm : ∀ ε : NoiseRate, TendsToOne (M.noisedNormSq ε)) :
    FixedNoiseConclusion M.noisedNormSq M.noisedTotalVariation := by
  intro ε
  refine ⟨hnorm ε, ?_⟩
  have hcert : TendsToOne (ofNoisedPlant M ε).normSq := by
    have heq : (ofNoisedPlant M ε).normSq = M.noisedNormSq ε := by
      funext n
      exact ofNoisedPlant_normSq M ε n
    rw [heq]
    exact hnorm ε
  have htv := (ofNoisedPlant M ε).totalVariation_vanishes hcert
  have heq : (ofNoisedPlant M ε).totalVariation =
      M.noisedTotalVariation ε := by
    funext n
    exact ofNoisedPlant_totalVariation M ε n
  rw [heq] at htv
  exact htv

end SecondMomentCertificate

end LowDegree
