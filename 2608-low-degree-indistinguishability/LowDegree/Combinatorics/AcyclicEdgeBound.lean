import LowDegree.Combinatorics.ConnectedComponentDecomposition

/-!
# Edge count of a finite forest without isolated vertices

This records the elementary implication used in Appendix (A.8): a nonempty
finite graph shape with at least as many edges as vertices contains a cycle.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace FiniteGraphShape

private theorem edgeCount_eq_edgeFinset_card (F : FiniteGraphShape) :
    F.edgeCount = F.graph.edgeFinset.card := by
  rw [edgeCount_eq_ncard]
  exact Set.ncard_eq_toFinset_card' F.graph.edgeSet

/-- Edge counts add exactly over the connected-component decomposition. -/
theorem edgeCount_eq_sum_connectedComponent_edgeCount
    (F : FiniteGraphShape) :
    F.edgeCount = ∑ i : Fin F.componentCount,
      (F.pieceShape F.connectedComponentDecomposition i).edgeCount := by
  let P := F.connectedComponentDecomposition
  calc
    F.edgeCount = F.graph.edgeFinset.card := edgeCount_eq_edgeFinset_card F
    _ = ∑ i, (P.piece i).edgeFinset.card := P.card_edges_eq_sum
    _ = ∑ i, (F.pieceShape P i).edgeCount := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [F.pieceShape_edgeCount P i]
      exact (Set.ncard_eq_toFinset_card' (P.piece i).edgeSet).symm

/-- Vertex counts also add exactly over connected components. -/
theorem vertexCount_eq_sum_connectedComponent_vertexCount
    (F : FiniteGraphShape) :
    F.vertexCount = ∑ i : Fin F.componentCount,
      (F.pieceShape F.connectedComponentDecomposition i).vertexCount := by
  let P := F.connectedComponentDecomposition
  symm
  calc
    (∑ i, (F.pieceShape P i).vertexCount) =
        ∑ i, (P.vertexFinset i).card := by
      simp only [F.pieceShape_vertexCount]
    _ = P.overlap + P.graphVertexFinset.card :=
      P.overlap_add_graphVertex_card.symm
    _ = P.graphVertexFinset.card := by
      rw [F.connectedComponentDecomposition_overlap, zero_add]
    _ = F.vertexCount := (F.vertexCount_eq_graphVertexFinset_card P).symm

/-- An acyclic nonempty finite graph shape has strictly fewer edges than
vertices.  Graph shapes have no isolated vertices by definition. -/
theorem edgeCount_lt_vertexCount_of_isAcyclic
    (F : FiniteGraphShape) (hacyclic : F.graph.IsAcyclic)
    (hedge : 0 < F.edgeCount) :
    F.edgeCount < F.vertexCount := by
  let P := F.connectedComponentDecomposition
  have hpieceTree (i : Fin F.componentCount) :
      (F.pieceShape P i).graph.IsTree := by
    refine ⟨F.pieceShape_connected_connectedComponentDecomposition i, ?_⟩
    have hpiece : (P.piece i).IsAcyclic :=
      hacyclic.anti (P.piece_le i)
    exact hpiece.induce _
  have hpieceCard (i : Fin F.componentCount) :
      (F.pieceShape P i).edgeCount + 1 =
        (F.pieceShape P i).vertexCount := by
    let H := F.pieceShape P i
    have hcard := (hpieceTree i).card_edgeFinset
    change H.graph.edgeFinset.card + 1 = Fintype.card H.Vertex at hcard
    change H.edgeCount + 1 = H.vertexCount
    rw [edgeCount_eq_edgeFinset_card H]
    exact hcard
  have hcomponentPos : 0 < F.componentCount := by
    have hedgeFinset : 0 < F.graph.edgeFinset.card := by
      rwa [← edgeCount_eq_edgeFinset_card F]
    obtain ⟨edge, _hedgeMem⟩ := Finset.card_pos.mp hedgeFinset
    unfold componentCount
    apply Fintype.card_pos_iff.mpr
    induction edge using Sym2.inductionOn with
    | _ u _v => exact ⟨F.graph.connectedComponentMk u⟩
  have hsum :
      (∑ i : Fin F.componentCount,
          (F.pieceShape P i).edgeCount) + F.componentCount =
        ∑ i : Fin F.componentCount,
          (F.pieceShape P i).vertexCount := by
    calc
      (∑ i : Fin F.componentCount,
          (F.pieceShape P i).edgeCount) + F.componentCount =
          ∑ i : Fin F.componentCount,
            ((F.pieceShape P i).edgeCount + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ i : Fin F.componentCount,
          (F.pieceShape P i).vertexCount := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hpieceCard i
  rw [← F.edgeCount_eq_sum_connectedComponent_edgeCount,
    ← F.vertexCount_eq_sum_connectedComponent_vertexCount] at hsum
  omega

/-- Contrapositive form used by A.8: `e ≥ v` forces a cycle. -/
theorem not_isAcyclic_of_vertexCount_le_edgeCount
    (F : FiniteGraphShape) (hedge : 0 < F.edgeCount)
    (h : F.vertexCount ≤ F.edgeCount) :
    ¬F.graph.IsAcyclic := by
  intro hacyclic
  exact (F.edgeCount_lt_vertexCount_of_isAcyclic hacyclic hedge).not_ge h

end FiniteGraphShape

end

end LowDegree
