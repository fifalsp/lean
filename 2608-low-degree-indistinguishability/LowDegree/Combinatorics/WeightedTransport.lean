import LowDegree.Combinatorics.IsomorphismTriples
import Mathlib.Tactic.FieldSimp

/-!
# From triple-count injections to the `β` overlap bound

This is the numerical bookkeeping in Equation (4.4).  The input cardinality
inequality is supplied by `restrictIsomorphismTriples_injective`; this module
checks every power of `n` and `c`, including negative excess `e-v` represented
as a quotient.
-/

namespace LowDegree

open scoped BigOperators

/-- `β` written using an isomorphism-triple count. -/
noncomputable def betaFromTriple
    (n c : ℝ) (edgeCount vertexCount : ℕ) (tripleCount : ℝ) : ℝ :=
  (((n ^ edgeCount / n ^ vertexCount) / c ^ edgeCount) * tripleCount)

/-- Equation (4.4): an injective restriction of isomorphism triples yields
the product bound, and vertex overlap contributes exactly `n^overlap`. -/
theorem beta_le_overlap_mul_prod
    {ι : Type*} [Fintype ι]
    {n c : ℝ} {edgeCount vertexCount overlap : ℕ}
    {pieceEdges pieceVertices : ι → ℕ}
    {tripleCount : ℝ} {pieceTripleCount : ι → ℝ}
    (hn : 0 < n) (hc : 0 < c)
    (hedges : edgeCount = ∑ i, pieceEdges i)
    (hvertices : (∑ i, pieceVertices i) = vertexCount + overlap)
    (htriple_nonneg : 0 ≤ tripleCount)
    (hpiece_nonneg : ∀ i, 0 ≤ pieceTripleCount i)
    (htriple : tripleCount ≤ ∏ i, pieceTripleCount i) :
    betaFromTriple n c edgeCount vertexCount tripleCount ≤
      n ^ overlap *
        ∏ i, betaFromTriple n c (pieceEdges i) (pieceVertices i)
          (pieceTripleCount i) := by
  classical
  have hn0 : n ≠ 0 := hn.ne'
  have hc0 : c ≠ 0 := hc.ne'
  let scale : ℕ → ℕ → ℝ := fun e v ↦ (n ^ e / n ^ v) / c ^ e
  have hscale_nonneg : 0 ≤ scale edgeCount vertexCount := by
    exact div_nonneg (div_nonneg (pow_nonneg hn.le _) (pow_nonneg hn.le _))
      (pow_nonneg hc.le _)
  have hscale :
      n ^ overlap * ∏ i, scale (pieceEdges i) (pieceVertices i) =
        scale edgeCount vertexCount := by
    simp only [scale, Finset.prod_div_distrib]
    rw [Finset.prod_pow_eq_pow_sum Finset.univ pieceEdges n]
    rw [Finset.prod_pow_eq_pow_sum Finset.univ pieceVertices n]
    rw [Finset.prod_pow_eq_pow_sum Finset.univ pieceEdges c]
    rw [← hedges, hvertices, pow_add]
    field_simp
  calc
    betaFromTriple n c edgeCount vertexCount tripleCount =
        scale edgeCount vertexCount * tripleCount := rfl
    _ ≤ scale edgeCount vertexCount * ∏ i, pieceTripleCount i :=
      mul_le_mul_of_nonneg_left htriple hscale_nonneg
    _ = (n ^ overlap * ∏ i, scale (pieceEdges i) (pieceVertices i)) *
          ∏ i, pieceTripleCount i := by rw [hscale]
    _ = n ^ overlap *
          ∏ i, (scale (pieceEdges i) (pieceVertices i) * pieceTripleCount i) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = n ^ overlap *
          ∏ i, betaFromTriple n c (pieceEdges i) (pieceVertices i)
            (pieceTripleCount i) := rfl

end LowDegree
