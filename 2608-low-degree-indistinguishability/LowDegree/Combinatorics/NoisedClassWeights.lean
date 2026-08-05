import LowDegree.Combinatorics.EmbeddedCopies

/-!
# One-class Fourier weights after edge noise

This file formalizes the one-isomorphism-class regrouping in paper
Equation (3.6).  Every embedded support representing a fixed finite graph
shape has the same number of edges, so edge noise contributes the common
factor `(1 - ε)^(2 e(F))` to the sum of squared Fourier coefficients.  The
remaining class sum is exactly the Equation (3.5) weight already computed in
`EmbeddedCopies.lean`.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace FiniteGraphShape

universe u

variable {n : ℕ} (F : FiniteGraphShape.{u})

/-- On a concrete copy of `F`, edge noise multiplies the Fourier coefficient
by the common class factor `(1-ε)^e(F)`. -/
theorem fourierCoeff_noisedLikelihood_concreteCopyEdges
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    fourierCoeff θ (noisedLikelihood θ ε plant)
        (F.concreteCopyEdges copy) =
      (1 - (ε : ℝ)) ^ F.edgeCount *
        fourierCoeff θ (plantedLikelihood θ plant)
          (F.concreteCopyEdges copy) := by
  rw [fourierCoeff_noisedLikelihood, fourierCoeff_plantedLikelihood,
    F.card_concreteCopyEdges]
  ring

/-- Factoring the common noise multiplier out of one complete
isomorphism-class sum. -/
theorem sum_fourierCoeff_sq_noised_over_concreteCopies_eq_noiseFactor_mul
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    (∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (noisedLikelihood θ ε plant)
          (F.concreteCopyEdges copy)) ^ 2) =
      (1 - (ε : ℝ)) ^ (2 * F.edgeCount) *
        ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff θ (plantedLikelihood θ plant)
            (F.concreteCopyEdges copy)) ^ 2 := by
  calc
    (∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (noisedLikelihood θ ε plant)
          (F.concreteCopyEdges copy)) ^ 2) =
        ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          ((1 - (ε : ℝ)) ^ F.edgeCount) ^ 2 *
            (fourierCoeff θ (plantedLikelihood θ plant)
              (F.concreteCopyEdges copy)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro copy _hcopy
      rw [F.fourierCoeff_noisedLikelihood_concreteCopyEdges θ ε plant copy]
      ring
    _ = ((1 - (ε : ℝ)) ^ F.edgeCount) ^ 2 *
        ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff θ (plantedLikelihood θ plant)
            (F.concreteCopyEdges copy)) ^ 2 := by
      rw [Finset.mul_sum]
    _ = (1 - (ε : ℝ)) ^ (2 * F.edgeCount) *
        ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff θ (plantedLikelihood θ plant)
            (F.concreteCopyEdges copy)) ^ 2 := by
      rw [show 2 * F.edgeCount = F.edgeCount * 2 by omega, pow_mul]

/-- **Equation (3.6), one exact isomorphism-class summand.**

The explicit `copy` is the domain guard ensuring that `F` embeds in the
ambient complete graph.  The right-hand factor after the noise multiplier is
the exact class weight from Equation (3.5). -/
theorem sum_fourierCoeff_sq_noised_over_concreteCopies
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (noisedLikelihood θ ε plant)
          (F.concreteCopyEdges other)) ^ 2) =
      (1 - (ε : ℝ)) ^ (2 * F.edgeCount) *
        (((1 - θ.p) / θ.p) ^ F.edgeCount *
          ((F.nonInducedCopyCount plant : ℝ) ^ 2 *
            (Fintype.card F.Automorphism : ℝ)) /
              fallingFactorial n F.vertexCount) := by
  rw [F.sum_fourierCoeff_sq_noised_over_concreteCopies_eq_noiseFactor_mul
      θ ε plant,
    F.sum_fourierCoeff_sq_over_concreteCopies θ plant copy]

/-- Sparse-parameter specialization of the noised class summand: Equation
(3.6) contributes `(1-ε)^(2e(F)) αₙ(F)` for this isomorphism class. -/
theorem sum_fourierCoeff_sq_noised_over_concreteCopies_eq_alphaWeight
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) (c : ℝ)
    (hp : θ.p = c / (n : ℝ))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (noisedLikelihood θ ε plant)
          (F.concreteCopyEdges other)) ^ 2) =
      (1 - (ε : ℝ)) ^ (2 * F.edgeCount) *
        alphaWeight c n F.edgeCount F.vertexCount
          (F.nonInducedCopyCount plant)
          (Fintype.card F.Automorphism) := by
  rw [F.sum_fourierCoeff_sq_noised_over_concreteCopies_eq_noiseFactor_mul
      θ ε plant,
    F.sum_fourierCoeff_sq_over_concreteCopies_eq_alphaWeight
      θ plant c hp copy]

end FiniteGraphShape

end

end LowDegree
