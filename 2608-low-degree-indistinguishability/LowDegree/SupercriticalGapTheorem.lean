import LowDegree.SupercriticalLowDegree
import LowDegree.SupercriticalCanonicalScales

/-!
# The supercritical low-degree/statistical gap

This module packages the low-degree and statistical halves of Appendix
Theorem A.1 at the paper's canonical scales.  All finite counting,
truncation, injection, and asymptotic estimates are discharged by the
imported modules.
-/

namespace LowDegree

open Filter Topology Asymptotics

noncomputable section

/-- **Appendix Theorem A.1 (canonical supercritical gap).**

For `lambda > 2 / (1 - epsilon)`, the canonical degree cutoff is
`Omega(log n)`, and there is one `c₀ > 1` such that, simultaneously for
every `c >= c₀`, the squared norm of the degree-`Dₙ` likelihood-ratio
projection tends to one while the noised alternative has total variation
distance tending to one from `G(n,c/n)`.
-/
theorem appendix_supercritical_gap_canonical
    (lam r gamma : ℝ)
    (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    Omega (fun n : ℕ ↦ (appendixDegreeCutoff n : ℝ))
        (fun n : ℕ ↦ Real.log (n : ℝ)) ∧
      ∃ c₀ : ℝ, 1 < c₀ ∧
        ∀ epsilon : NoiseRate,
          2 / (1 - (epsilon : ℝ)) < lam →
          ∀ c : ℝ, c₀ ≤ c →
            TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) ∧
              TendsToOne (fun n ↦
                (appendixNoisedAlternativeLaw
                    epsilon c lam r gamma hr n).tv
                  (erdosRenyiLaw (n := n)
                    (sparseBernoulliParameter c n))) := by
  refine ⟨appendixDegreeCutoff_isOmega_log, ?_⟩
  obtain ⟨c₀, hc₀, hlow⟩ :=
    appendix_lowDegreeIndistinguishability lam r gamma hr hgamma hlam
  refine ⟨c₀, hc₀, ?_⟩
  intro epsilon hsuper c hc
  refine ⟨hlow c hc, ?_⟩
  have hcpos : 0 < c := by linarith
  exact appendix_statisticalDistinguishability_of_supercritical_canonical
    epsilon c lam r gamma hcpos hlam hsuper hr hgamma

end

end LowDegree
