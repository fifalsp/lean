import LowDegree.Asymptotics.Basic
import LowDegree.Combinatorics.TreeDecomposition
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

/-- The typed signature of the data appearing in paper Theorem 1.1.

Writing each plant on `Fin n` incorporates the printed condition
`|V(Γₙ)| ≤ n`: a smaller plant is represented by adding isolated ambient
vertices.  `treewidthBound` is an upper bound rather than a numerical
treewidth equality, exactly matching what the proof consumes.

The three scalar fields are the paper's low-degree second moment, noised full
second moment, and noised total-variation distance.  A future model-facing
module must construct them from `Qₙ`, `Pₙ`, and their likelihood ratios.  This
structure records their theorem-level types without pretending that bridge is
already implemented.
-/
structure BoundedTreewidthLowDegreeProfile where
  backgroundDensity : ℝ
  backgroundDensity_pos : 0 < backgroundDensity
  plant : (n : ℕ) → SimpleGraph (Fin n)
  treewidthBound : ℕ → ℕ
  treewidth_le : ∀ n,
    TreeDecomposition.HasTreewidthAtMost (plant n) (treewidthBound n)
  degreeCutoff : ℕ → ℕ
  degreeCutoff_pos : ∀ n, 0 < degreeCutoff n
  lowDegreeNormSq : ℕ → ℝ
  noisedNormSq : NoiseRate → ℕ → ℝ
  noisedTotalVariation : NoiseRate → ℕ → ℝ

/-- **Formal statement of paper Theorem 1.1 (proof pending).**

This definition encodes the exact logical implication and quantifier order of
the bounded-treewidth low-degree consequence.  It is a `Prop`, not an axiom or
a proved theorem: the central graph/Fourier transfer still requires the
model-facing likelihood-ratio construction and the tree-decomposition
existence proof documented in `docs/PAPER_MAP.md`.
-/
def main_lowDegree_to_noisedL2_and_tv_statement
    (P : BoundedTreewidthLowDegreeProfile) : Prop :=
  TreewidthDegreeScale P.treewidthBound P.degreeCutoff →
  TendsToOne P.lowDegreeNormSq →
  FixedNoiseConclusion P.noisedNormSq P.noisedTotalVariation

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

end SecondMomentCertificate

end LowDegree
