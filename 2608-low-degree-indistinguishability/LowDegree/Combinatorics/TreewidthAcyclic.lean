import LowDegree.Combinatorics.BoundedOverlapDivision
import LowDegree.Combinatorics.WeightedTreePartitionAdapter

/-!
# Treewidth one for finite trees

A rooted tree has the standard width-one tree decomposition whose bag at a
non-root vertex consists of that vertex and its parent, while the root bag is
the singleton root.  This module constructs that decomposition and records
the connected-acyclic consequence needed by the forest-truncation argument.
-/

namespace LowDegree

open WeightedTreePartitionAdapter

namespace TreeDecomposition

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

universe u v

variable {V : Type u} {X : Type v} [Fintype V] [Fintype X]
variable {G : SimpleGraph V}

/-! ## Reindexing decomposition nodes -/

/-- Relabel the node type of a tree decomposition by an equivalence. -/
noncomputable def Decomposition.reindex (D : Decomposition G X)
    {Y : Type*} [Fintype Y] (e : X ≃ Y) : Decomposition G Y where
  tree := D.tree.map e
  bag := fun y ↦ D.bag (e.symm y)
  isTree := (SimpleGraph.Iso.map e D.tree).isTree_iff.mp D.isTree
  vertex_mem := by
    intro a
    obtain ⟨x, hx⟩ := D.vertex_mem a
    exact ⟨e x, by simpa using hx⟩
  edge_mem := by
    intro a b hab
    obtain ⟨x, hax, hbx⟩ := D.edge_mem hab
    exact ⟨e x, by simpa using hax, by simpa using hbx⟩
  running_intersection := by
    intro a
    let source := D.tree.induce {x : X | a ∈ D.bag x}
    let target := (D.tree.map e).induce {y : Y | a ∈ D.bag (e.symm y)}
    let f : source →g target :=
      { toFun := fun x ↦ ⟨e x.1, by
          change a ∈ D.bag (e.symm (e x.1))
          rw [e.symm_apply_apply]
          exact x.2⟩
        map_rel' := by
          intro x y hxy
          change (D.tree.map e).Adj (e x.1) (e y.1)
          exact (SimpleGraph.Iso.map e D.tree).map_rel_iff.mpr hxy }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      refine ⟨⟨e.symm y, by
        change a ∈ D.bag (e.symm y)
        exact hy⟩, ?_⟩
      apply Subtype.ext
      simp [f]
    exact (D.running_intersection a).map f hf

theorem Decomposition.reindex_widthAtMost (D : Decomposition G X)
    {Y : Type*} [Fintype Y] (e : X ≃ Y) {k : ℕ}
    (hwidth : D.WidthAtMost k) : (D.reindex e).WidthAtMost k := by
  intro y
  exact hwidth (e.symm y)

/-- Any finite-node decomposition can be converted to the canonical `Fin`
node type used by `HasTreewidthAtMost`. -/
theorem hasTreewidthAtMost_of_decomposition
    (D : Decomposition G X) {k : ℕ} (hwidth : D.WidthAtMost k) :
    HasTreewidthAtMost G k := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  exact ⟨Fintype.card X, D.reindex e, D.reindex_widthAtMost e hwidth⟩

/-! ## The rooted two-vertex-bag decomposition -/

/-- A chosen root of a finite tree. -/
noncomputable def treeRoot (hG : G.IsTree) : V :=
  Classical.choice hG.isConnected.nonempty

/-- The standard width-one bag: the root alone at the root node, and a
vertex together with its parent everywhere else. -/
noncomputable def rootedTreeBag (hG : G.IsTree) (x : V) : Finset V :=
  if x = treeRoot hG then {treeRoot hG}
  else {parent hG (treeRoot hG) x, x}

@[simp]
theorem self_mem_rootedTreeBag (hG : G.IsTree) (x : V) :
    x ∈ rootedTreeBag hG x := by
  by_cases hx : x = treeRoot hG
  · simp [rootedTreeBag, hx]
  · simp [rootedTreeBag, hx]

/-- A vertex occurs in the bag at `x` exactly when `x` is that vertex or a
child of it (with the singleton root case included). -/
theorem mem_rootedTreeBag_iff (hG : G.IsTree) (r x : V) :
    r ∈ rootedTreeBag hG x ↔
      x = r ∨ (x ≠ treeRoot hG ∧ parent hG (treeRoot hG) x = r) := by
  by_cases hx : x = treeRoot hG
  · subst x
    simp [rootedTreeBag]
    aesop
  · simp only [rootedTreeBag, if_neg hx, Finset.mem_insert,
      Finset.mem_singleton]
    aesop

/-- The rooted parent bags form a width-one tree decomposition of a finite
tree. -/
noncomputable def decompositionOfIsTree (hG : G.IsTree) :
    Decomposition G V where
  tree := G
  bag := rootedTreeBag hG
  isTree := hG
  vertex_mem := fun v ↦ ⟨v, self_mem_rootedTreeBag hG v⟩
  edge_mem := by
    intro u v huv
    rw [adj_iff_parent hG (treeRoot hG) u v] at huv
    rcases huv with hchild | hchild
    · refine ⟨v, ?_, ?_⟩
      · rw [mem_rootedTreeBag_iff]
        exact Or.inr ⟨hchild.1, hchild.2⟩
      · exact self_mem_rootedTreeBag hG v
    · refine ⟨u, ?_, ?_⟩
      · exact self_mem_rootedTreeBag hG u
      · rw [mem_rootedTreeBag_iff]
        exact Or.inr ⟨hchild.1, hchild.2⟩
  running_intersection := by
    intro r
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨r, self_mem_rootedTreeBag hG r⟩, ?_⟩
    rintro ⟨x, hxmem⟩
    have hx := hxmem
    change r ∈ rootedTreeBag hG x at hx
    rw [mem_rootedTreeBag_iff] at hx
    rcases hx with rfl | hx
    · exact .rfl
    · have hadj : G.Adj r x := by
        simpa [hx.2] using parent_adj hG (treeRoot hG) x hx.1
      have hadjInduced :
          (G.induce {y : V | r ∈ rootedTreeBag hG y}).Adj
            ⟨r, self_mem_rootedTreeBag hG r⟩ ⟨x, hxmem⟩ := hadj
      exact hadjInduced.reachable

/-- Every bag in the rooted decomposition has at most two vertices. -/
theorem decompositionOfIsTree_widthAtMost_one (hG : G.IsTree) :
    (decompositionOfIsTree hG).WidthAtMost 1 := by
  intro x
  by_cases hx : x = treeRoot hG
  · simp [decompositionOfIsTree, rootedTreeBag, hx]
  · change (rootedTreeBag hG x).card ≤ 1 + 1
    rw [rootedTreeBag, if_neg hx]
    simpa using
      (Finset.card_le_two (a := parent hG (treeRoot hG) x) (b := x))

/-- A finite tree has treewidth at most one. -/
theorem hasTreewidthAtMost_one_of_isTree (hG : G.IsTree) :
    HasTreewidthAtMost G 1 :=
  hasTreewidthAtMost_of_decomposition (decompositionOfIsTree hG)
    (decompositionOfIsTree_widthAtMost_one hG)

/-- Paper-facing form used for forest supports: connectedness and acyclicity
together imply treewidth at most one. -/
theorem hasTreewidthAtMost_one_of_connected_isAcyclic
    (hconn : G.Connected) (hacyclic : G.IsAcyclic) :
    HasTreewidthAtMost G 1 :=
  hasTreewidthAtMost_one_of_isTree ⟨hconn, hacyclic⟩

/-- Every connected acyclic graph with at least `l > 0` edges has the
paper's block decomposition with overlap at most `2(m-1)`.  This is the
width-one specialization used for forest-supported Fourier mass. -/
theorem connectedAcyclic_exists_boundedOverlap_orderedEdgeDecomposition
    {l : ℕ} (hconn : G.Connected) (hacyclic : G.IsAcyclic)
    (hl : 0 < l) (htotal : l ≤ G.edgeFinset.card) :
    ∃ m : ℕ, ∃ P : OrderedEdgeDecomposition G m,
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ 2 * (m - 1) := by
  simpa using exists_boundedOverlap_orderedEdgeDecomposition
    (hasTreewidthAtMost_one_of_connected_isAcyclic hconn hacyclic)
    hl htotal

end

end TreeDecomposition
end LowDegree
