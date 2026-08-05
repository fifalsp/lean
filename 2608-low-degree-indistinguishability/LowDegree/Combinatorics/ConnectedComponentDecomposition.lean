import LowDegree.Combinatorics.GraphCopies
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-!
# Ordered edge decomposition into connected components

This file turns mathlib's finite connected components into the exact
zero-overlap `OrderedEdgeDecomposition` needed by the cluster expansion.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace FiniteGraphShape

open TreeDecomposition

/-- Number of connected components of the shape. -/
noncomputable def componentCount (F : FiniteGraphShape) : ℕ :=
  Fintype.card F.graph.ConnectedComponent

/-- A canonical enumeration of the connected components. -/
noncomputable def componentAt (F : FiniteGraphShape)
    (i : Fin F.componentCount) : F.graph.ConnectedComponent :=
  (Fintype.equivFin F.graph.ConnectedComponent).symm i

/-- The spanning graph consisting of one enumerated connected component. -/
noncomputable def connectedComponentPiece (F : FiniteGraphShape)
    (i : Fin F.componentCount) : SimpleGraph F.Vertex :=
  (F.componentAt i).toSimpleGraph.spanningCoe

theorem connectedComponentPiece_adj_iff (F : FiniteGraphShape)
    (i : Fin F.componentCount) (u v : F.Vertex) :
    (F.connectedComponentPiece i).Adj u v ↔
      u ∈ (F.componentAt i).supp ∧ F.graph.Adj u v := by
  exact (F.componentAt i).adj_spanningCoe_toSimpleGraph

theorem connectedComponentPiece_support (F : FiniteGraphShape)
    (i : Fin F.componentCount) :
    (F.connectedComponentPiece i).support = (F.componentAt i).supp := by
  ext u
  rw [SimpleGraph.mem_support]
  constructor
  · rintro ⟨v, huv⟩
    exact (F.connectedComponentPiece_adj_iff i u v).mp huv |>.1
  · intro hu
    have huniv : u ∈ F.graph.support := by
      rw [F.support_eq_univ]
      exact Set.mem_univ u
    rw [SimpleGraph.mem_support] at huniv
    rcases huniv with ⟨v, huv⟩
    have hv : v ∈ (F.componentAt i).supp :=
      (F.componentAt i).mem_supp_of_adj_mem_supp hu huv
    exact ⟨v, (F.connectedComponentPiece_adj_iff i u v).2 ⟨hu, huv⟩⟩

/-- The connected components form a nonempty, edge-disjoint cover of every
finite graph shape (which by definition has no isolated vertices). -/
noncomputable def connectedComponentDecomposition (F : FiniteGraphShape) :
    OrderedEdgeDecomposition F.graph F.componentCount where
  piece := F.connectedComponentPiece
  piece_nonempty := by
    intro i hbot
    have hsupp : (F.connectedComponentPiece i).support = ∅ := by
      rw [hbot]
      ext u
      simp [SimpleGraph.mem_support]
    rw [F.connectedComponentPiece_support] at hsupp
    exact (F.componentAt i).nonempty_supp.ne_empty hsupp
  piece_le := by
    intro i u v huv
    exact (F.connectedComponentPiece_adj_iff i u v).mp huv |>.2
  edge_disjoint := by
    intro i _hi j _hj hij
    apply SimpleGraph.disjoint_edgeSet.mp
    apply Set.disjoint_left.2
    intro e hei hej
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at hei hej
      have hui := (F.connectedComponentPiece_adj_iff i u v).mp hei |>.1
      have huj := (F.connectedComponentPiece_adj_iff j u v).mp hej |>.1
      have hc : F.componentAt i = F.componentAt j :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex hui huj
      have heq : i = j := by
        apply (Fintype.equivFin F.graph.ConnectedComponent).symm.injective
        exact hc
      exact hij heq
  cover := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    rw [SimpleGraph.iSup_adj]
    constructor
    · rintro ⟨i, huv⟩
      exact (F.connectedComponentPiece_adj_iff i u v).mp huv |>.2
    · intro huv
      let c := F.graph.connectedComponentMk u
      let i : Fin F.componentCount :=
        Fintype.equivFin F.graph.ConnectedComponent c
      refine ⟨i, (F.connectedComponentPiece_adj_iff i u v).2 ⟨?_, huv⟩⟩
      change u ∈ (F.componentAt i).supp
      have hi : F.componentAt i = c := by
        exact (Fintype.equivFin F.graph.ConnectedComponent).symm_apply_apply c
      rw [hi]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- Each component piece is connected after isolated vertices are stripped. -/
theorem pieceShape_connected_connectedComponentDecomposition
    (F : FiniteGraphShape) (i : Fin F.componentCount) :
    (F.pieceShape F.connectedComponentDecomposition i).graph.Connected := by
  let c := F.componentAt i
  let H := F.connectedComponentPiece i
  let source : SimpleGraph F.Vertex := H
  have hsupport : H.support = c.supp := F.connectedComponentPiece_support i
  let e : H.support ≃ c.supp := Equiv.setCongr hsupport
  have hIsoInduced : H.induce H.support ≃g c.toSimpleGraph := by
    refine
      { toEquiv := e
        map_rel_iff' := ?_ }
    intro u v
    change F.graph.Adj (e u).1 (e v).1 ↔ H.Adj u.1 v.1
    have hu : u.1 ∈ c.supp := by
      rw [← hsupport]
      exact u.2
    change F.graph.Adj u.1 v.1 ↔
      (F.connectedComponentPiece i).Adj u.1 v.1
    constructor
    · intro huv
      exact (F.connectedComponentPiece_adj_iff i u.1 v.1).2 ⟨hu, huv⟩
    · intro huv
      exact (F.connectedComponentPiece_adj_iff i u.1 v.1).1 huv |>.2
  change (supportShape H).graph.Connected
  exact hIsoInduced.connected_iff.mpr c.connected_toSimpleGraph

/-- Every graph vertex belongs to exactly one component piece. -/
theorem connectedComponentDecomposition_vertexMultiplicity
    (F : FiniteGraphShape) (v : F.Vertex) :
    F.connectedComponentDecomposition.vertexMultiplicity v = 1 := by
  let c := F.graph.connectedComponentMk v
  let i : Fin F.componentCount :=
    Fintype.equivFin F.graph.ConnectedComponent c
  unfold OrderedEdgeDecomposition.vertexMultiplicity
  have hfilter :
      (Finset.univ.filter fun j : Fin F.componentCount ↦
          v ∈ F.connectedComponentDecomposition.vertexFinset j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [F.connectedComponentDecomposition.mem_vertexFinset]
    change v ∈ (F.connectedComponentPiece j).support ↔ j = i
    rw [F.connectedComponentPiece_support]
    constructor
    · intro hv
      have hc : F.componentAt j = c := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
        exact hv.symm
      have hi : F.componentAt i = c :=
        (Fintype.equivFin F.graph.ConnectedComponent).symm_apply_apply c
      apply (Fintype.equivFin F.graph.ConnectedComponent).symm.injective
      exact hc.trans hi.symm
    · intro hji
      subst j
      change v ∈ (F.componentAt i).supp
      have hi : F.componentAt i = c :=
        (Fintype.equivFin F.graph.ConnectedComponent).symm_apply_apply c
      rw [hi]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rw [hfilter]
  simp

/-- The connected-component edge decomposition has zero vertex overlap. -/
@[simp]
theorem connectedComponentDecomposition_overlap (F : FiniteGraphShape) :
    F.connectedComponentDecomposition.overlap = 0 := by
  rw [F.connectedComponentDecomposition.overlap_eq_sum_multiplicity_sub_one]
  apply Finset.sum_eq_zero
  intro v _hv
  rw [F.connectedComponentDecomposition_vertexMultiplicity]
  simp

/-- Beta weight is submultiplicative over connected components. -/
theorem graphBetaWeight_le_prod_connectedComponents
    {V : Type*} [Fintype V]
    (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n)
    (F : FiniteGraphShape) (G : SimpleGraph V) :
    F.graphBetaWeight c n G ≤
      ∏ i : Fin F.componentCount,
        (F.pieceShape F.connectedComponentDecomposition i).graphBetaWeight
          c n G := by
  have h := F.graphBetaWeight_le_overlap_mul_prod
    c hc n hn G F.connectedComponentDecomposition
  simpa only [F.connectedComponentDecomposition_overlap, pow_zero,
    one_mul] using h

end FiniteGraphShape

end

end LowDegree
