import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Regrouping a finite sum by two bounded natural statistics

This small utility is used by Appendix A to pass from Fourier supports to
the finite `(v,e)` enumeration without changing or duplicating summands.
-/

namespace LowDegree

open scoped BigOperators

attribute [local instance] Classical.decEq

/-- Regroup a finite sum exactly by two bounded natural-valued statistics. -/
theorem sum_eq_sum_two_count_fibers
    {Ω M : Type*} [AddCommMonoid M]
    (s : Finset Ω) (first second : Ω → ℕ) (weight : Ω → M)
    (firstCap secondCap : ℕ)
    (hfirst : ∀ x ∈ s, first x < firstCap)
    (hsecond : ∀ x ∈ s, second x < secondCap) :
    (∑ x ∈ s, weight x) =
      ∑ i ∈ Finset.range firstCap,
        ∑ j ∈ Finset.range secondCap,
          ∑ x ∈ s with first x = i ∧ second x = j, weight x := by
  let target := Finset.range firstCap ×ˢ Finset.range secondCap
  have hmaps : ∀ x ∈ s, (first x, second x) ∈ target := by
    intro x hx
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hfirst x hx),
        Finset.mem_range.mpr (hsecond x hx)⟩
  symm
  rw [← Finset.sum_product']
  simpa only [target, Prod.fst, Prod.snd, Prod.ext_iff] using
    (Finset.sum_fiberwise_of_maps_to
      (s := s) (t := target) (g := fun x ↦ (first x, second x))
      hmaps weight)

end LowDegree
