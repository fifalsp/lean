import LowDegree.Combinatorics.GraphShapeClasses
import LowDegree.Combinatorics.EmbeddedCopies
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Connected copy counting for deterministic bounded-degree plants

This module gives a genuinely finite interpretation of the sum over
connected abstract graph shapes in the deterministic appendix.  The index is
the existing quotient `AmbientSupportClass (Fintype.card V)`: it contains one
class for every nonempty graph shape that can occur in a graph on `V`, while
shapes that do not occur in the plant contribute zero.

The final algebraic step in the paper's connected-count lemma is proved in
`deterministicConnectedCount_of_finiteBounds`.  Its two hypotheses isolate
the finite graph-enumeration facts used in the manuscript proof:

* every connected `e`-edge shape has at most `m * D ^ e` labelled copies;
* the total number of unlabelled connected `e`-edge copies is at most
  `m * D ^ (2 * e)`.

Together with `labelledCopyCount_eq_nonInducedCopyCount_mul_aut`, these give
exactly `m ^ 2 * D ^ (3 * e)`.
-/

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace SimpleGraph

/-- A graph-theoretic maximum-degree bound.  This is unrelated to the
Fourier degree cutoff called `appendixDegreeCutoff`. -/
def HasMaximumDegreeAtMost {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ v : V, G.degree v ≤ D

/-- The number of non-isolated vertices of `G` is at most `m`.  Stating the
bound using the support makes it stable under padding a plant by isolated
ambient vertices. -/
def HasSupportCardAtMost {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.support.toFinset.card ≤ m

end SimpleGraph

namespace LowDegree

/-! ## A rooted-tree code for labelled copies -/

namespace RootedTreeCode

variable {W : Type*} [Fintype W]

/-- The unique path from `x` to the selected root in a finite tree. -/
noncomputable def pathToRoot (T : SimpleGraph W) (hT : T.IsTree)
    (root x : W) : T.Walk x root :=
  (hT.existsUnique_path x root).choose

theorem pathToRoot_isPath (T : SimpleGraph W) (hT : T.IsTree)
    (root x : W) : (pathToRoot T hT root x).IsPath :=
  (hT.existsUnique_path x root).choose_spec.1

/-- The next vertex on the tree path towards the root. -/
noncomputable def parent (T : SimpleGraph W) (hT : T.IsTree)
    (root x : W) : W :=
  (pathToRoot T hT root x).snd

/-- Distance to the root in the selected spanning tree. -/
noncomputable def level (T : SimpleGraph W) (hT : T.IsTree)
    (root x : W) : ℕ :=
  (pathToRoot T hT root x).length

theorem pathToRoot_notNil (T : SimpleGraph W) (hT : T.IsTree)
    {root x : W} (hx : x ≠ root) :
    ¬(pathToRoot T hT root x).Nil :=
  SimpleGraph.Walk.not_nil_of_ne hx

theorem adj_parent (T : SimpleGraph W) (hT : T.IsTree)
    {root x : W} (hx : x ≠ root) :
    T.Adj x (parent T hT root x) := by
  exact (pathToRoot T hT root x).adj_snd
    (pathToRoot_notNil T hT hx)

theorem pathToRoot_parent_eq_tail (T : SimpleGraph W) (hT : T.IsTree)
    {root x : W} (hx : x ≠ root) :
    pathToRoot T hT root (parent T hT root x) =
      (pathToRoot T hT root x).tail := by
  exact ((hT.existsUnique_path (parent T hT root x) root).choose_spec.2
    (pathToRoot T hT root x).tail
    (pathToRoot_isPath T hT root x).tail).symm

theorem level_parent_lt (T : SimpleGraph W) (hT : T.IsTree)
    {root x : W} (hx : x ≠ root) :
    level T hT root (parent T hT root x) < level T hT root x := by
  rw [level, pathToRoot_parent_eq_tail T hT hx]
  change (pathToRoot T hT root x).tail.length <
    (pathToRoot T hT root x).length
  rw [← SimpleGraph.Walk.length_tail_add_one
    (pathToRoot_notNil T hT hx)]
  omega

@[simp]
theorem level_root (T : SimpleGraph W) (hT : T.IsTree) (root : W) :
    level T hT root root = 0 := by
  have hpath : pathToRoot T hT root root = .nil :=
    ((hT.existsUnique_path root root).choose_spec.2 .nil
      SimpleGraph.Walk.IsPath.nil).symm
  simp [level, hpath]

theorem eq_root_of_level_eq_zero (T : SimpleGraph W) (hT : T.IsTree)
    {root x : W} (hx : level T hT root x = 0) : x = root := by
  exact (SimpleGraph.Walk.nil_iff_length_eq.mpr hx).eq

/-- The undirected edge from a nonroot vertex to its tree parent. -/
noncomputable def parentEdge (T : SimpleGraph W) (hT : T.IsTree)
    (root x : W) : Sym2 W :=
  s(parent T hT root x, x)

theorem parentEdge_injectiveOn_nonroot (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) : Set.InjOn (parentEdge T hT root) {x | x ≠ root} := by
  intro x hx y hy hxy
  change Sym2.mk (parent T hT root x, x) =
    Sym2.mk (parent T hT root y, y) at hxy
  rw [Sym2.mk_eq_mk_iff] at hxy
  rcases hxy with hxy | hxy
  · exact congrArg Prod.snd hxy
  · have hpxy : parent T hT root x = y := congrArg Prod.fst hxy
    have hxpy : x = parent T hT root y := congrArg Prod.snd hxy
    have hxlevel := level_parent_lt T hT hx
    have hylevel := level_parent_lt T hT hy
    rw [hpxy] at hxlevel
    rw [← hxpy] at hylevel
    omega

end RootedTreeCode

/-- A uniform numbering of the neighbours of every target vertex by
`Fin D`, available under a maximum-degree bound. -/
noncomputable def boundedNeighborEmbedding
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hD : G.HasMaximumDegreeAtMost D) (v : V) :
    G.neighborSet v ↪ Fin D :=
  (Function.Embedding.nonempty_of_card_le (by
    rw [SimpleGraph.card_neighborSet_eq_degree]
    simpa only [Fintype.card_fin] using hD v)).some

/-- The neighbour number as an ordinary (nondependent) function.  Away from
the neighbour set it is assigned the harmless default value zero. -/
noncomputable def boundedNeighborCode
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    (v w : V) : Fin D :=
  if h : G.Adj v w then
    boundedNeighborEmbedding G D hD v ⟨w, h⟩
  else
    ⟨0, hDpos⟩

theorem boundedNeighborCode_injective_on_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    {v x y : V} (hx : G.Adj v x) (hy : G.Adj v y)
    (hcode : boundedNeighborCode G D hD hDpos v x =
      boundedNeighborCode G D hD hDpos v y) : x = y := by
  simp only [boundedNeighborCode, dif_pos hx, dif_pos hy] at hcode
  exact congrArg Subtype.val
    ((boundedNeighborEmbedding G D hD v).injective hcode)

/-- Encode a labelled copy of a connected source graph by the image of a
root and, along a fixed spanning tree, one neighbour-number for every other
source vertex. -/
noncomputable def rootedCopyCode
    {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (T : SimpleGraph W) (hT : T.IsTree) (hTH : T ≤ H)
    (root : W) (hroot : root ∈ H.support)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D) :
    SimpleGraph.Copy H G ↪
      G.support × ({x : W // x ≠ root} → Fin D) where
  toFun f :=
    (⟨f root, by
        rw [SimpleGraph.mem_support] at hroot ⊢
        obtain ⟨w, hrw⟩ := hroot
        exact ⟨f w, f.toHom.map_rel hrw⟩⟩,
      fun x ↦
        boundedNeighborCode G D hD hDpos
          (f (RootedTreeCode.parent T hT root x.1)) (f x.1))
  inj' := by
    intro f g hfg
    apply SimpleGraph.Copy.ext
    have hrootfg : f root = g root :=
      congrArg (fun z ↦ z.1.1) hfg
    intro x
    induction hxlev : RootedTreeCode.level T hT root x using
        Nat.strong_induction_on generalizing x with
    | h k ih =>
        by_cases hxr : x = root
        · simpa [hxr] using hrootfg
        · let p := RootedTreeCode.parent T hT root x
          have hplev : RootedTreeCode.level T hT root p < k := by
            rw [← hxlev]
            exact RootedTreeCode.level_parent_lt T hT hxr
          have hpfg : f p = g p := ih _ hplev p rfl
          have hcode := congrFun (congrArg Prod.snd hfg) ⟨x, hxr⟩
          dsimp only at hcode
          apply boundedNeighborCode_injective_on_neighbors G D hD hDpos
            (v := g p)
          · have hfadj : G.Adj (f p) (f x) := f.toHom.map_rel
                (hTH (RootedTreeCode.adj_parent T hT hxr).symm)
            rw [hpfg] at hfadj
            exact hfadj
          · exact g.toHom.map_rel
              (hTH (RootedTreeCode.adj_parent T hT hxr).symm)
          · simpa only [p, hpfg] using hcode

/-- Cardinality consequence of the rooted spanning-tree code. -/
theorem card_copy_le_support_mul_pow_card_sub_one_of_spanningTree
    {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (T : SimpleGraph W) (hT : T.IsTree) (hTH : T ≤ H)
    (root : W) (hroot : root ∈ H.support)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D) :
    Fintype.card (SimpleGraph.Copy H G) ≤
      G.support.toFinset.card * D ^ (Fintype.card W - 1) := by
  calc
    Fintype.card (SimpleGraph.Copy H G) ≤
        Fintype.card
          (G.support × ({x : W // x ≠ root} → Fin D)) :=
      Fintype.card_le_of_embedding
        (rootedCopyCode H G T hT hTH root hroot D hD hDpos)
    _ = G.support.toFinset.card * D ^ (Fintype.card W - 1) := by
      have hne : Fintype.card {x : W // x ≠ root} =
          Fintype.card W - 1 := by
        simpa only [Set.mem_setOf_eq] using Set.card_ne_eq root
      rw [Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, hne]
      congr 1
      exact (Set.toFinset_card G.support).symm

/-- A connected, no-isolates source with `e` edges has at most
`|supp(G)| D^e` labelled copies in a graph of maximum degree `D`. -/
theorem card_copy_le_support_mul_pow_edgeFinset_of_connected
    {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hconn : H.Connected) (hsupport : H.support = Set.univ)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D) :
    Fintype.card (SimpleGraph.Copy H G) ≤
      G.support.toFinset.card * D ^ H.edgeFinset.card := by
  obtain ⟨T, hTH, hT⟩ := hconn.exists_isTree_le
  let root : W := hconn.nonempty.some
  have hroot : root ∈ H.support := by
    rw [hsupport]
    exact Set.mem_univ root
  have hbase :=
    card_copy_le_support_mul_pow_card_sub_one_of_spanningTree
      H G T hT hTH root hroot D hD hDpos
  have hvertices : Fintype.card W - 1 ≤ H.edgeFinset.card := by
    have hcard := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← H.edgeFinset_card] at hcard
    omega
  exact hbase.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hDpos hvertices))

/-! ## Closed backtracking tours -/

/-- Splice the two-step excursion `parent → child → parent` into a closed
walk at an occurrence of `parent`. -/
def insertBacktrack
    {W : Type*} {T : SimpleGraph W} {root parent child : W}
    (q : T.Walk root root) (hp : parent ∈ q.support)
    (hpc : T.Adj parent child) : T.Walk root root :=
  (((q.takeUntil parent hp).concat hpc).concat hpc.symm).append
    (q.dropUntil parent hp)

@[simp]
theorem length_insertBacktrack
    {W : Type*} {T : SimpleGraph W} {root parent child : W}
    (q : T.Walk root root) (hp : parent ∈ q.support)
    (hpc : T.Adj parent child) :
    (insertBacktrack q hp hpc).length = q.length + 2 := by
  have hsplit := congrArg SimpleGraph.Walk.length (q.take_spec hp)
  simp only [SimpleGraph.Walk.length_append] at hsplit
  simp only [insertBacktrack, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat]
  omega

theorem support_subset_insertBacktrack
    {W : Type*} {T : SimpleGraph W} {root parent child : W}
    (q : T.Walk root root) (hp : parent ∈ q.support)
    (hpc : T.Adj parent child) :
    q.support ⊆ (insertBacktrack q hp hpc).support := by
  intro x hx
  rw [← q.take_spec hp, SimpleGraph.Walk.mem_support_append_iff] at hx
  rw [insertBacktrack, SimpleGraph.Walk.mem_support_append_iff]
  rcases hx with hx | hx
  · left
    exact SimpleGraph.Walk.subset_support_append_left
      ((q.takeUntil parent hp).concat hpc)
      (SimpleGraph.Walk.cons hpc.symm .nil)
      (SimpleGraph.Walk.subset_support_append_left
        (q.takeUntil parent hp) (SimpleGraph.Walk.cons hpc .nil) hx)
  · exact Or.inr hx

theorem child_mem_support_insertBacktrack
    {W : Type*} {T : SimpleGraph W} {root parent child : W}
    (q : T.Walk root root) (hp : parent ∈ q.support)
    (hpc : T.Adj parent child) :
    child ∈ (insertBacktrack q hp hpc).support := by
  rw [insertBacktrack, SimpleGraph.Walk.mem_support_append_iff]
  left
  exact SimpleGraph.Walk.subset_support_append_left
    ((q.takeUntil parent hp).concat hpc)
    (SimpleGraph.Walk.cons hpc.symm .nil)
    (SimpleGraph.Walk.end_mem_support _)

@[simp]
theorem edges_toFinset_insertBacktrack
    {W : Type*}
    {T : SimpleGraph W} {root parent child : W}
    (q : T.Walk root root) (hp : parent ∈ q.support)
    (hpc : T.Adj parent child) :
    (insertBacktrack q hp hpc).edges.toFinset =
      q.edges.toFinset ∪ {s(parent, child)} := by
  classical
  have hsplit := congrArg SimpleGraph.Walk.edges (q.take_spec hp)
  simp only [SimpleGraph.Walk.edges_append] at hsplit
  simp only [insertBacktrack, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_concat, List.concat_eq_append,
    List.toFinset_append]
  have hset : (q.takeUntil parent hp).edges.toFinset ∪
      (q.dropUntil parent hp).edges.toFinset = q.edges.toFinset := by
    rw [← List.toFinset_append, hsplit]
  rw [Sym2.eq_swap (a := child) (b := parent), ← hset]
  ext z
  simp [Finset.mem_union, or_assoc, or_left_comm, or_comm]

/-- Insert a finite family of two-step excursions.  All attachment vertices
are assumed to occur in the original walk; this is exactly what is needed
when one tree level is exposed at a time. -/
theorem exists_insertBacktracks_finset
    {W : Type*} [Fintype W] {T : SimpleGraph W} {root : W}
    (parent : W → W) (S : Finset W) (q : T.Walk root root)
    (hadj : ∀ x ∈ S, T.Adj (parent x) x)
    (hparent : ∀ x ∈ S, parent x ∈ q.support) :
    ∃ q' : T.Walk root root,
      q.support ⊆ q'.support ∧
      (∀ x ∈ S, x ∈ q'.support) ∧
      q'.length = q.length + 2 * S.card ∧
      q'.edges.toFinset =
        q.edges.toFinset ∪ S.image (fun x ↦ s(parent x, x)) := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty =>
      exact ⟨q, fun _ h ↦ h, by simp, by simp, by simp⟩
  | @insert x S hx ih =>
      have hxadj : T.Adj (parent x) x := hadj x (Finset.mem_insert_self x S)
      have hxp : parent x ∈ q.support :=
        hparent x (Finset.mem_insert_self x S)
      let qx := insertBacktrack q hxp hxadj
      have hqsub : q.support ⊆ qx.support :=
        support_subset_insertBacktrack q hxp hxadj
      obtain ⟨q', hqxsub, hchildren, hlength, hedges⟩ := ih qx
        (fun y hy ↦ hadj y (Finset.mem_insert_of_mem hy))
        (fun y hy ↦ hqsub (hparent y (Finset.mem_insert_of_mem hy)))
      refine ⟨q', hqsub.trans hqxsub, ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hqxsub (child_mem_support_insertBacktrack q hxp hxadj)
        · exact hchildren y hy
      · rw [hlength, length_insertBacktrack, Finset.card_insert_of_notMem hx]
        omega
      · rw [hedges, edges_toFinset_insertBacktrack,
          Finset.image_insert]
        ext z
        simp [Finset.mem_union, or_assoc, or_left_comm, or_comm]

/-- Indexed version of `exists_insertBacktracks_finset`, used to insert one
two-step excursion for every non-tree edge. -/
theorem exists_insertBacktracks_indexed_finset
    {I W : Type*} [Fintype I] [Fintype W]
    {T : SimpleGraph W} {root : W}
    (parent child : I → W) (S : Finset I) (q : T.Walk root root)
    (hadj : ∀ i ∈ S, T.Adj (parent i) (child i))
    (hparent : ∀ i ∈ S, parent i ∈ q.support) :
    ∃ q' : T.Walk root root,
      q.support ⊆ q'.support ∧
      q'.length = q.length + 2 * S.card ∧
      q'.edges.toFinset =
        q.edges.toFinset ∪ S.image (fun i ↦ s(parent i, child i)) := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty =>
      exact ⟨q, fun _ h ↦ h, by simp, by simp⟩
  | @insert i S hi ih =>
      have hiadj : T.Adj (parent i) (child i) :=
        hadj i (Finset.mem_insert_self i S)
      have hip : parent i ∈ q.support :=
        hparent i (Finset.mem_insert_self i S)
      let qi := insertBacktrack q hip hiadj
      have hqsub : q.support ⊆ qi.support :=
        support_subset_insertBacktrack q hip hiadj
      obtain ⟨q', hqisub, hlength, hedges⟩ := ih qi
        (fun j hj ↦ hadj j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hqsub (hparent j (Finset.mem_insert_of_mem hj)))
      refine ⟨q', hqsub.trans hqisub, ?_, ?_⟩
      · rw [hlength, length_insertBacktrack, Finset.card_insert_of_notMem hi]
        omega
      · rw [hedges, edges_toFinset_insertBacktrack, Finset.image_insert]
        ext z
        simp [Finset.mem_union, or_assoc, or_left_comm, or_comm]

/-- Nonroot vertices at tree distance at most `k` from the root. -/
noncomputable def rootedVerticesUpTo
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) (k : ℕ) : Finset W :=
  Finset.univ.filter fun x ↦
    x ≠ root ∧ RootedTreeCode.level T hT root x ≤ k

/-- Nonroot vertices at tree distance exactly `k` from the root. -/
noncomputable def rootedVerticesAt
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) (k : ℕ) : Finset W :=
  Finset.univ.filter fun x ↦
    x ≠ root ∧ RootedTreeCode.level T hT root x = k

@[simp]
theorem rootedVerticesUpTo_zero
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) : rootedVerticesUpTo T hT root 0 = ∅ := by
  classical
  ext x
  simp only [rootedVerticesUpTo, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.notMem_empty, iff_false]
  rintro ⟨hx, hlevel⟩
  have hzero : RootedTreeCode.level T hT root x = 0 := by omega
  exact hx (RootedTreeCode.eq_root_of_level_eq_zero T hT hzero)

theorem rootedVerticesUpTo_succ
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) (k : ℕ) :
    rootedVerticesUpTo T hT root (k + 1) =
      rootedVerticesUpTo T hT root k ∪
        rootedVerticesAt T hT root (k + 1) := by
  classical
  ext x
  simp only [rootedVerticesUpTo, rootedVerticesAt, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨hx, hlevel⟩
    by_cases hle : RootedTreeCode.level T hT root x ≤ k
    · exact Or.inl ⟨hx, hle⟩
    · exact Or.inr ⟨hx, by omega⟩
  · rintro (h | h)
    · exact ⟨h.1, by omega⟩
    · exact ⟨h.1, by omega⟩

theorem rootedVerticesUpTo_disjoint_at_succ
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) (k : ℕ) :
    Disjoint (rootedVerticesUpTo T hT root k)
      (rootedVerticesAt T hT root (k + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [rootedVerticesUpTo, rootedVerticesAt, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx hxs
  omega

/-- Build the depth-first-style closed tour through the first `k` rooted
tree levels by inserting one backtrack for each newly exposed vertex. -/
theorem exists_partialTreeTour
    {W : Type*} [Fintype W] (T : SimpleGraph W) (hT : T.IsTree)
    (root : W) (k : ℕ) :
    ∃ q : T.Walk root root,
      (∀ x : W, RootedTreeCode.level T hT root x ≤ k →
        x ∈ q.support) ∧
      q.length = 2 * (rootedVerticesUpTo T hT root k).card ∧
      q.edges.toFinset =
        (rootedVerticesUpTo T hT root k).image
          (RootedTreeCode.parentEdge T hT root) := by
  classical
  induction k with
  | zero =>
      refine ⟨.nil, ?_, ?_, ?_⟩
      · intro x hx
        have hzero : RootedTreeCode.level T hT root x = 0 := by omega
        have hxr := RootedTreeCode.eq_root_of_level_eq_zero T hT hzero
        subst x
        simp
      · simp
      · simp
  | succ k ih =>
      obtain ⟨q, hcover, hlength, hedges⟩ := ih
      let S := rootedVerticesAt T hT root (k + 1)
      have hadj : ∀ x ∈ S,
          T.Adj (RootedTreeCode.parent T hT root x) x := by
        intro x hx
        have hx' := hx
        simp only [S, rootedVerticesAt, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx'
        exact (RootedTreeCode.adj_parent T hT hx'.1).symm
      have hparent : ∀ x ∈ S,
          RootedTreeCode.parent T hT root x ∈ q.support := by
        intro x hx
        have hx' := hx
        simp only [S, rootedVerticesAt, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx'
        apply hcover
        have hlt := RootedTreeCode.level_parent_lt T hT hx'.1
        omega
      obtain ⟨q', hqsub, hchildren, hlength', hedges'⟩ :=
        exists_insertBacktracks_finset
          (RootedTreeCode.parent T hT root) S q hadj hparent
      refine ⟨q', ?_, ?_, ?_⟩
      · intro x hx
        by_cases hxk : RootedTreeCode.level T hT root x ≤ k
        · exact hqsub (hcover x hxk)
        · apply hchildren x
          simp only [S, rootedVerticesAt, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨?_, by omega⟩
          intro hxr
          subst x
          simp at hxk
      · have hcard : (rootedVerticesUpTo T hT root (k + 1)).card =
            (rootedVerticesUpTo T hT root k).card + S.card := by
          rw [rootedVerticesUpTo_succ]
          exact Finset.card_union_of_disjoint
            (rootedVerticesUpTo_disjoint_at_succ T hT root k)
        rw [hlength', hlength, hcard]
        omega
      · simp only [S] at hedges'
        rw [hedges', hedges, rootedVerticesUpTo_succ,
          Finset.image_union]
        rfl

/-- Every finite tree has a closed walk from any prescribed root that
traverses each tree edge twice. -/
theorem SimpleGraph.IsTree.exists_closedWalk_length_twice_edges
    {W : Type*} [Fintype W] {T : SimpleGraph W}
    (hT : T.IsTree) (root : W) :
    ∃ q : T.Walk root root,
      q.length = 2 * T.edgeFinset.card ∧
      q.support.toFinset = Finset.univ ∧
      q.edges.toFinset = T.edgeFinset := by
  classical
  obtain ⟨q, hcover, hlength, hedges⟩ :=
    exists_partialTreeTour T hT root (Fintype.card W)
  have hlevel : ∀ x : W,
      RootedTreeCode.level T hT root x ≤ Fintype.card W := by
    intro x
    exact Nat.le_of_lt (RootedTreeCode.pathToRoot_isPath T hT root x).length_lt
  have hup : rootedVerticesUpTo T hT root (Fintype.card W) =
      Finset.univ.erase root := by
    ext x
    simp only [rootedVerticesUpTo, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hx, _⟩
      exact ⟨hx, trivial⟩
    · rintro ⟨hx, _⟩
      exact ⟨hx, hlevel x⟩
  have hsupport : q.support.toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcover x (hlevel x)
  have hparentSubset :
      (Finset.univ.erase root).image
          (RootedTreeCode.parentEdge T hT root) ⊆ T.edgeFinset := by
    intro edge hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨x, hx, rfl⟩ := hedge
    rw [SimpleGraph.mem_edgeFinset]
    have hxroot : x ≠ root := (Finset.mem_erase.mp hx).1
    exact (RootedTreeCode.adj_parent T hT hxroot).symm
  have hparentCard :
      ((Finset.univ.erase root).image
        (RootedTreeCode.parentEdge T hT root)).card =
        (Finset.univ.erase root).card := by
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    apply RootedTreeCode.parentEdge_injectiveOn_nonroot T hT root
    · exact (Finset.mem_erase.mp hx).1
    · exact (Finset.mem_erase.mp hy).1
    · exact hxy
  have hparentEdges :
      (Finset.univ.erase root).image
          (RootedTreeCode.parentEdge T hT root) = T.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le hparentSubset
    rw [hparentCard, Finset.card_erase_of_mem (Finset.mem_univ root),
      Finset.card_univ]
    have htreeCard := hT.card_edgeFinset
    omega
  refine ⟨q, ?_, hsupport, ?_⟩
  · rw [hlength, hup, Finset.card_erase_of_mem (Finset.mem_univ root),
      Finset.card_univ]
    have htreeCard := hT.card_edgeFinset
    omega
  · rw [hedges, hup, hparentEdges]

/-- Every finite connected graph has a closed walk of length twice its edge
count whose edge support is the whole graph.  This is the doubled-edge tour
used in the paper's connected-subgraph encoding. -/
theorem SimpleGraph.Connected.exists_closedWalk_length_twice_edges
    {W : Type*} [Fintype W] {H : SimpleGraph W}
    (hH : H.Connected) (root : W) :
    ∃ q : H.Walk root root,
      q.length = 2 * H.edgeFinset.card ∧
      q.support.toFinset = Finset.univ ∧
      q.edges.toFinset = H.edgeFinset := by
  classical
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  obtain ⟨qT, hlengthT, hsupportT, hedgesT⟩ :=
    LowDegree.SimpleGraph.IsTree.exists_closedWalk_length_twice_edges hT root
  let q : H.Walk root root := qT.map (SimpleGraph.Hom.ofLE hTH)
  have hlengthq : q.length = 2 * T.edgeFinset.card := by
    simpa [q] using hlengthT
  have hsupportq : q.support.toFinset = Finset.univ := by
    simpa [q] using hsupportT
  have hedgesq : q.edges.toFinset = T.edgeFinset := by
    simpa [q] using hedgesT
  let extra : Finset (Sym2 W) := H.edgeFinset \ T.edgeFinset
  have hadj : ∀ e ∈ extra, H.Adj e.out.1 e.out.2 := by
    intro e he
    have heH : e ∈ H.edgeFinset := (Finset.mem_sdiff.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at heH
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.out_eq]
    exact heH
  have hparent : ∀ e ∈ extra, e.out.1 ∈ q.support := by
    intro e _he
    have : e.out.1 ∈ q.support.toFinset := by
      rw [hsupportq]
      exact Finset.mem_univ _
    exact List.mem_toFinset.mp this
  obtain ⟨q', hqsub, hlength, hedges⟩ :=
    exists_insertBacktracks_indexed_finset
      (fun e : Sym2 W ↦ e.out.1) (fun e : Sym2 W ↦ e.out.2)
      extra q hadj hparent
  have himage : extra.image (fun e : Sym2 W ↦ s(e.out.1, e.out.2)) =
      extra := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa only [Sym2.mk, a.out_eq] using ha
    · intro he
      exact ⟨e, he, e.out_eq⟩
  have hfin : T.edgeFinset ⊆ H.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hTH he
  have hsupport : q'.support.toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    apply hqsub
    have : x ∈ q.support.toFinset := by
      rw [hsupportq]
      exact Finset.mem_univ x
    exact List.mem_toFinset.mp this
  refine ⟨q', ?_, hsupport, ?_⟩
  · rw [hlength, hlengthq]
    have hextra : extra.card = H.edgeFinset.card - T.edgeFinset.card := by
      exact Finset.card_sdiff_of_subset hfin
    rw [hextra]
    have hcard := Finset.card_le_card hfin
    omega
  · rw [hedges, hedgesq, himage]
    exact Finset.union_sdiff_of_subset hfin

/-! ## Counting fixed-length walks in a bounded-degree graph -/

/-- Record the local neighbour number taken at each step of a fixed-length
walk. -/
noncomputable def fixedLengthWalkCode
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    {root : V} (L : ℕ) (p : {q : G.Walk root root // q.length = L}) :
    Fin L → Fin D :=
  fun i ↦ boundedNeighborCode G D hD hDpos
    (p.1.getVert i.val) (p.1.getVert (i.val + 1))

theorem fixedLengthWalkCode_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    {root : V} (L : ℕ) :
    Function.Injective
      (fixedLengthWalkCode G D hD hDpos (root := root) L) := by
  intro p q hpq
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · rw [p.2, q.2]
  · intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hklt : k < L := by simpa [p.2] using hk
        have hkprev : p.1.getVert k = q.1.getVert k := ih (by omega)
        have hcode := congrFun hpq ⟨k, hklt⟩
        apply boundedNeighborCode_injective_on_neighbors G D hD hDpos
          (v := q.1.getVert k)
        · have hadj := p.1.adj_getVert_succ (by simpa [p.2] using hklt)
          rw [hkprev] at hadj
          exact hadj
        · exact q.1.adj_getVert_succ (by simpa [q.2] using hklt)
        · simpa only [fixedLengthWalkCode, hkprev] using hcode

/-- At a fixed supported root there are at most `D^L` closed walks of
length `L`. -/
theorem card_closedWalk_length_eq_le_pow
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    (root : G.support) (L : ℕ) :
    Fintype.card {q : G.Walk root.1 root.1 // q.length = L} ≤ D ^ L := by
  calc
    Fintype.card {q : G.Walk root.1 root.1 // q.length = L} ≤
        Fintype.card (Fin L → Fin D) :=
      Fintype.card_le_of_injective _
        (fixedLengthWalkCode_injective G D hD hDpos L)
    _ = D ^ L := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Summing over supported starting vertices costs only the support size. -/
theorem card_sigma_supported_closedWalk_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : ℕ) (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D)
    (L : ℕ) :
    Fintype.card
        (Σ root : G.support,
          {q : G.Walk root.1 root.1 // q.length = L}) ≤
      G.support.toFinset.card * D ^ L := by
  rw [Fintype.card_sigma]
  calc
    (∑ root : G.support,
        Fintype.card {q : G.Walk root.1 root.1 // q.length = L}) ≤
        ∑ _root : G.support, D ^ L := by
      exact Finset.sum_le_sum fun root _ ↦
        card_closedWalk_length_eq_le_pow G D hD hDpos root L
    _ = G.support.toFinset.card * D ^ L := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      exact (Set.toFinset_card G.support).symm

/-- A closed walk which visits every vertex and traverses every edge recovers
the whole ambient graph as its walk subgraph. -/
theorem closedWalk_toSubgraph_eq_top
    {W : Type*} [Fintype W] {H : SimpleGraph W} {root : W}
    (q : H.Walk root root)
    (hsupport : q.support.toFinset = Finset.univ)
    (hedges : q.edges.toFinset = H.edgeFinset) :
    q.toSubgraph = ⊤ := by
  apply SimpleGraph.Subgraph.ext
  · rw [SimpleGraph.Walk.verts_toSubgraph,
      SimpleGraph.Subgraph.verts_top]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply List.mem_toFinset.mp
    rw [hsupport]
    exact Finset.mem_univ x
  · funext x y
    apply propext
    change s(x, y) ∈ q.toSubgraph.edgeSet ↔ H.Adj x y
    rw [q.mem_edges_toSubgraph, ← List.mem_toFinset, hedges,
      SimpleGraph.mem_edgeFinset]
    exact SimpleGraph.mem_edgeSet H

/-- Transport a concrete copy to the complete graph on the canonical finite
model of its ambient vertex type.  This lets us read off its ambient-support
orbit without assuming that the original ambient graph is complete. -/
noncomputable def FiniteGraphShape.canonicalTopConcreteCopy
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    (G : SimpleGraph V) (copy : F.ConcreteCopy G) :
    F.ConcreteCopy (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
  F.mapConcreteCopy
    (SimpleGraph.Iso.completeGraph (Fintype.equivFin V))
    (F.liftConcreteCopy (by exact le_top) copy)

/-- Concrete copies belonging to two canonical shape classes cannot have the
same ambient subgraph unless the classes themselves agree. -/
theorem ambientSupportClass_eq_of_concreteCopy_subgraph_eq
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {C D : AmbientSupportClass (Fintype.card V)}
    (left : C.shape.ConcreteCopy G) (right : D.shape.ConcreteCopy G)
    (hsubgraph : left.1 = right.1) : C = D := by
  let leftLift : C.shape.ConcreteCopy (⊤ : SimpleGraph V) :=
    C.shape.liftConcreteCopy (by exact le_top) left
  let rightLift : D.shape.ConcreteCopy (⊤ : SimpleGraph V) :=
    D.shape.liftConcreteCopy (by exact le_top) right
  have hlift : leftLift.1 = rightLift.1 := by
    apply SimpleGraph.Subgraph.ext
    · simpa only [leftLift, rightLift,
        FiniteGraphShape.liftConcreteCopy_verts] using
        congrArg SimpleGraph.Subgraph.verts hsubgraph
    · funext x y
      apply propext
      simpa only [leftLift, rightLift,
        FiniteGraphShape.liftConcreteCopy_adj] using
        Iff.of_eq
          (congrArg (fun H : G.Subgraph ↦ H.Adj x y) hsubgraph)
  let ambientIso : (⊤ : SimpleGraph V) ≃g
      (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
    SimpleGraph.Iso.completeGraph (Fintype.equivFin V)
  let leftTop : C.shape.ConcreteCopy
      (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
    C.shape.mapConcreteCopy ambientIso leftLift
  let rightTop : D.shape.ConcreteCopy
      (⊤ : SimpleGraph (Fin (Fintype.card V))) :=
    D.shape.mapConcreteCopy ambientIso rightLift
  have htop : leftTop.1 = rightTop.1 := by
    rw [show leftTop.1 = leftLift.1.map ambientIso.toHom by
        exact C.shape.mapConcreteCopy_subgraph ambientIso leftLift,
      show rightTop.1 = rightLift.1.map ambientIso.toHom by
        exact D.shape.mapConcreteCopy_subgraph ambientIso rightLift,
      hlift]
  let leftFiber := C.concreteCopyToFiber leftTop
  let rightFiber := D.concreteCopyToFiber rightTop
  have hedge : C.shape.concreteCopyEdges leftTop =
      D.shape.concreteCopyEdges rightTop := by
    ext edge
    rw [C.shape.mem_concreteCopyEdges, D.shape.mem_concreteCopyEdges,
      htop]
  have hfiber : leftFiber.1 = rightFiber.1 := by
    apply Subtype.ext
    exact hedge
  calc
    C = ambientSupportClass leftFiber.1 := leftFiber.2.symm
    _ = ambientSupportClass rightFiber.1 :=
      congrArg ambientSupportClass hfiber
    _ = D := rightFiber.2

/-- The finite set of abstract nonempty graph classes with exactly `e` edges
and connected support.  The ambient order only supplies a finite universe of
representatives. -/
noncomputable def connectedShapeClasses (ambientOrder e : ℕ) :
    Finset (AmbientSupportClass ambientOrder) :=
  (Finset.univ : Finset (AmbientSupportClass ambientOrder)).filter fun C ↦
    C.shape.graph.Connected ∧ C.shape.edgeCount = e

/-- There is no zero-edge class in the nonempty-support quotient. -/
theorem connectedShapeClasses_zero (ambientOrder : ℕ) :
    connectedShapeClasses ambientOrder 0 = ∅ := by
  ext C
  simp only [connectedShapeClasses, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.not_mem_empty, iff_false]
  intro hC
  have hpos : 0 < C.shape.edgeCount := by
    rw [C.shape_edgeCount_eq_representative_card]
    exact C.representative.2.card_pos
  omega

/-- The manuscript sum `∑_F N_G(F)` over connected abstract `e`-edge
shapes, with one term for each isomorphism class. -/
noncomputable def connectedShapeCopyMass
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) : ℕ :=
  ∑ C ∈ connectedShapeClasses (Fintype.card V) e,
    C.shape.nonInducedCopyCount G

/-- One connected shape class in the `e`-edge index, together with one of
its unlabelled concrete copies. -/
abbrev ConnectedConcreteCopy
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) :=
  Σ C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e},
    C.1.shape.ConcreteCopy G

/-- The disjoint-union cardinality is exactly the manuscript sum of
unlabelled connected copies. -/
theorem card_connectedConcreteCopy
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) :
    Fintype.card (ConnectedConcreteCopy G e) =
      connectedShapeCopyMass G e := by
  rw [Fintype.card_sigma]
  unfold connectedShapeCopyMass FiniteGraphShape.nonInducedCopyCount
  exact (Finset.sum_subtype
    (connectedShapeClasses (Fintype.card V) e)
    (by intro C; simp)
    (fun C ↦ Fintype.card (C.shape.ConcreteCopy G))).symm

theorem connectedConcreteCopyIndex_connected
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    C.1.shape.graph.Connected := by
  have hC : C.1.shape.graph.Connected ∧ C.1.shape.edgeCount = e := by
    simpa only [connectedShapeClasses, Finset.mem_filter,
      Finset.mem_univ, true_and] using C.2
  exact hC.1

theorem connectedConcreteCopyIndex_edgeFinset_card
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    C.1.shape.graph.edgeFinset.card = e := by
  have hC : C.1.shape.graph.Connected ∧ C.1.shape.edgeCount = e := by
    simpa only [connectedShapeClasses, Finset.mem_filter,
      Finset.mem_univ, true_and] using C.2
  have hedgeCount : C.1.shape.edgeCount = e := hC.2
  calc
    C.1.shape.graph.edgeFinset.card = C.1.shape.edgeCount := by
      rw [FiniteGraphShape.edgeCount_eq_ncard]
      exact (Set.ncard_eq_toFinset_card'
        C.1.shape.graph.edgeSet).symm
    _ = e := hedgeCount

/-- A fixed root used to make the doubled-edge-tour encoding a function. -/
noncomputable def connectedShapeRoot
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    C.1.shape.Vertex :=
  (connectedConcreteCopyIndex_connected (G := G) C).nonempty.some

theorem exists_connectedShapeTour
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    ∃ q : C.1.shape.graph.Walk
        (connectedShapeRoot (G := G) C) (connectedShapeRoot (G := G) C),
      q.length = 2 * e ∧
      q.support.toFinset = Finset.univ ∧
      q.edges.toFinset = C.1.shape.graph.edgeFinset := by
  obtain ⟨q, hlength, hsupport, hedges⟩ :=
    LowDegree.SimpleGraph.Connected.exists_closedWalk_length_twice_edges
      (connectedConcreteCopyIndex_connected (G := G) C)
      (connectedShapeRoot (G := G) C)
  refine ⟨q, ?_, hsupport, hedges⟩
  rw [hlength, connectedConcreteCopyIndex_edgeFinset_card (G := G) C]

/-- The selected doubled-edge tour of a connected shape. -/
noncomputable def connectedShapeTour
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    C.1.shape.graph.Walk
      (connectedShapeRoot (G := G) C) (connectedShapeRoot (G := G) C) :=
  (exists_connectedShapeTour (G := G) C).choose

theorem connectedShapeTour_spec
    {V : Type*} [Fintype V] {G : SimpleGraph V} {e : ℕ}
    (C : {C : AmbientSupportClass (Fintype.card V) //
      C ∈ connectedShapeClasses (Fintype.card V) e}) :
    (connectedShapeTour (G := G) C).length = 2 * e ∧
    (connectedShapeTour (G := G) C).support.toFinset = Finset.univ ∧
    (connectedShapeTour (G := G) C).edges.toFinset =
      C.1.shape.graph.edgeFinset :=
  (exists_connectedShapeTour (G := G) C).choose_spec

/-- Encode an unlabelled connected copy by its fixed doubled-edge tour,
mapped into the ambient graph. -/
noncomputable def connectedConcreteCopyWalk
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ)
    (z : ConnectedConcreteCopy G e) :
    Σ root : G.support,
      {q : G.Walk root.1 root.1 // q.length = 2 * e} := by
  let f : SimpleGraph.Copy z.1.1.shape.graph G :=
    FiniteGraphShape.concreteCopyToAmbientCopy z.2
  let root := connectedShapeRoot (G := G) z.1
  have hrootShape : root ∈ z.1.1.shape.graph.support := by
    rw [z.1.1.shape.support_eq_univ]
    exact Set.mem_univ root
  have hrootAmbient : f root ∈ G.support := by
    rw [SimpleGraph.mem_support] at hrootShape ⊢
    obtain ⟨w, hrootw⟩ := hrootShape
    exact ⟨f w, f.toHom.map_rel hrootw⟩
  let q := connectedShapeTour (G := G) z.1
  refine ⟨⟨f root, hrootAmbient⟩, ⟨q.map f.toHom, ?_⟩⟩
  simpa only [SimpleGraph.Walk.length_map, q] using
    (connectedShapeTour_spec (G := G) z.1).1

/-- The ambient subgraph can be recovered exactly from the encoded tour. -/
theorem connectedConcreteCopyWalk_toSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ)
    (z : ConnectedConcreteCopy G e) :
    (connectedConcreteCopyWalk G e z).2.1.toSubgraph = z.2.1 := by
  change
    ((connectedShapeTour (G := G) z.1).map
      (FiniteGraphShape.concreteCopyToAmbientCopy z.2).toHom).toSubgraph =
        z.2.1
  rw [SimpleGraph.Walk.toSubgraph_map]
  have htour : (connectedShapeTour (G := G) z.1).toSubgraph = ⊤ :=
    closedWalk_toSubgraph_eq_top (connectedShapeTour (G := G) z.1)
      (connectedShapeTour_spec (G := G) z.1).2.1
      (connectedShapeTour_spec (G := G) z.1).2.2
  rw [htour]
  change
    (FiniteGraphShape.concreteCopyToAmbientCopy z.2).toSubgraph = z.2.1
  exact FiniteGraphShape.concreteCopyToAmbientCopy_toSubgraph z.2

/-- Distinct connected shape/copy pairs give distinct supported closed
walks.  Equality of walks first recovers the concrete subgraph; its ambient
support orbit then recovers the shape-class tag. -/
theorem connectedConcreteCopyWalk_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) :
    Function.Injective (connectedConcreteCopyWalk G e) := by
  intro left right hwalk
  have hwalkSubgraph :
      (connectedConcreteCopyWalk G e left).2.1.toSubgraph =
        (connectedConcreteCopyWalk G e right).2.1.toSubgraph :=
    congrArg (fun z ↦ z.2.1.toSubgraph) hwalk
  have hsubgraph : left.2.1 = right.2.1 := by
    calc
      left.2.1 = (connectedConcreteCopyWalk G e left).2.1.toSubgraph :=
        (connectedConcreteCopyWalk_toSubgraph G e left).symm
      _ = (connectedConcreteCopyWalk G e right).2.1.toSubgraph :=
        hwalkSubgraph
      _ = right.2.1 := connectedConcreteCopyWalk_toSubgraph G e right
  have hclass : left.1.1 = right.1.1 :=
    ambientSupportClass_eq_of_concreteCopy_subgraph_eq
      left.2 right.2 hsubgraph
  have hindex : left.1 = right.1 := Subtype.ext hclass
  cases left with
  | mk C leftCopy =>
      cases right with
      | mk D rightCopy =>
          dsimp only at hindex hsubgraph ⊢
          subst D
          have hcopy : leftCopy = rightCopy := Subtype.ext hsubgraph
          cases hcopy
          rfl

/-- The left side of the deterministic connected-count lemma:
`∑_F N_G(F)^2 |Aut(F)|`, over connected abstract `e`-edge shapes. -/
noncomputable def connectedShapeTripleMass
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) : ℕ :=
  ∑ C ∈ connectedShapeClasses (Fintype.card V) e,
    C.shape.nonInducedCopyCount G ^ 2 *
      Fintype.card C.shape.Automorphism

@[simp]
theorem connectedShapeTripleMass_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    connectedShapeTripleMass G 0 = 0 := by
  unfold connectedShapeTripleMass
  rw [connectedShapeClasses_zero]
  simp

/-- The same finite mass written as `∑_F N_G(F) Emb_G(F)`.  This is the
first equality in the paper proof. -/
theorem connectedShapeTripleMass_eq_sum_copy_mul_labelledCopyCount
    {V : Type*} [Fintype V] (G : SimpleGraph V) (e : ℕ) :
    connectedShapeTripleMass G e =
      ∑ C ∈ connectedShapeClasses (Fintype.card V) e,
        C.shape.nonInducedCopyCount G *
          Fintype.card (SimpleGraph.Copy C.shape.graph G) := by
  unfold connectedShapeTripleMass
  apply Finset.sum_congr rfl
  intro C _hC
  rw [C.shape.labelledCopyCount_eq_nonInducedCopyCount_mul_aut]
  ring

/-- The pointwise labelled-embedding estimate used in the manuscript proof:
`Emb_G(F) ≤ m D^e` for every connected `e`-edge shape in the finite
index. -/
def ConnectedEmbeddingCountBound
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) : Prop :=
  ∀ C ∈ connectedShapeClasses (Fintype.card V) e,
    Fintype.card (SimpleGraph.Copy C.shape.graph G) ≤ m * D ^ e

/-- The manuscript's labelled-copy estimate follows from the two structural
hypotheses, with no ambient-cardinality loss from isolated padding. -/
theorem connectedEmbeddingCountBound_of_supportCard_maxDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) (hsupport : G.HasSupportCardAtMost m)
    (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D) :
    ConnectedEmbeddingCountBound G m D e := by
  intro C hC
  simp only [connectedShapeClasses, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  have hedge : C.shape.graph.edgeFinset.card = e := by
    calc
      C.shape.graph.edgeFinset.card = C.shape.edgeCount := by
        rw [FiniteGraphShape.edgeCount_eq_ncard]
        exact (Set.ncard_eq_toFinset_card' C.shape.graph.edgeSet).symm
      _ = e := hC.2
  have hbase := card_copy_le_support_mul_pow_edgeFinset_of_connected
    C.shape.graph G hC.1 C.shape.support_eq_univ D hD hDpos
  rw [hedge] at hbase
  exact hbase.trans (Nat.mul_le_mul_right _ hsupport)

/-- The connected-subgraph enumeration estimate used in the manuscript:
the total number of unlabelled connected `e`-edge copies is at most
`m D^(2e)`. -/
def ConnectedConcreteCopySumBound
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) : Prop :=
  connectedShapeCopyMass G e ≤ m * D ^ (2 * e)

/-- The connected-copy sum bound follows unconditionally from the support
size and maximum-degree hypotheses by the doubled-edge-tour injection. -/
theorem connectedConcreteCopySumBound_of_supportCard_maxDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) (hsupport : G.HasSupportCardAtMost m)
    (hD : G.HasMaximumDegreeAtMost D) (hDpos : 0 < D) :
    ConnectedConcreteCopySumBound G m D e := by
  unfold ConnectedConcreteCopySumBound
  calc
    connectedShapeCopyMass G e =
        Fintype.card (ConnectedConcreteCopy G e) :=
      (card_connectedConcreteCopy G e).symm
    _ ≤ Fintype.card
        (Σ root : G.support,
          {q : G.Walk root.1 root.1 // q.length = 2 * e}) :=
      Fintype.card_le_of_injective _
        (connectedConcreteCopyWalk_injective G e)
    _ ≤ G.support.toFinset.card * D ^ (2 * e) :=
      card_sigma_supported_closedWalk_le G D hD hDpos (2 * e)
    _ ≤ m * D ^ (2 * e) :=
      Nat.mul_le_mul_right _ hsupport

/-- A finite certificate containing the two enumeration inputs of the
deterministic connected-count proof, together with the structural hypotheses
from which the manuscript derives them. -/
structure DeterministicConnectedCountCertificate
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) : Prop where
  supportCard : G.HasSupportCardAtMost m
  maximumDegree : G.HasMaximumDegreeAtMost D
  labelledCopies : ConnectedEmbeddingCountBound G m D e
  connectedCopies : ConnectedConcreteCopySumBound G m D e

/-- **Finite form of the deterministic connected-count lemma.**

Once the two elementary bounded-degree enumeration estimates have been
supplied, the exact shape sum satisfies the paper's bound
`∑_F N_G(F)^2 |Aut(F)| ≤ m^2 D^(3e)`.

The support-cardinality hypothesis uses only the non-isolated vertices, so
this statement applies unchanged after embedding an `m`-vertex plant in a
larger ambient graph by adding isolated vertices. -/
theorem deterministicConnectedCount_of_finiteBounds
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ)
    (h : DeterministicConnectedCountCertificate G m D e) :
    connectedShapeTripleMass G e ≤ m ^ 2 * D ^ (3 * e) := by
  rw [connectedShapeTripleMass_eq_sum_copy_mul_labelledCopyCount]
  calc
    (∑ C ∈ connectedShapeClasses (Fintype.card V) e,
        C.shape.nonInducedCopyCount G *
          Fintype.card (SimpleGraph.Copy C.shape.graph G)) ≤
        ∑ C ∈ connectedShapeClasses (Fintype.card V) e,
          C.shape.nonInducedCopyCount G * (m * D ^ e) := by
      exact Finset.sum_le_sum fun C hC ↦
        Nat.mul_le_mul_left _ (h.labelledCopies C hC)
    _ = (m * D ^ e) * connectedShapeCopyMass G e := by
      unfold connectedShapeCopyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _hC
      ring
    _ ≤ (m * D ^ e) * (m * D ^ (2 * e)) := by
      exact Nat.mul_le_mul_left _ h.connectedCopies
    _ = m ^ 2 * D ^ (3 * e) := by
      rw [show 3 * e = e + 2 * e by omega, pow_add]
      ring

/-- **Appendix deterministic connected-count lemma.**

For every positive edge count, a graph with at most `m` non-isolated
vertices and maximum degree at most `D` satisfies the paper's exact finite
shape-sum bound.  The numerical assumption `6 ≤ D` is retained verbatim
from the manuscript; only its consequence `0 < D` is needed in the counting
argument. -/
theorem deterministicConnectedCount
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m D e : ℕ) (he : 0 < e) (hD : 6 ≤ D)
    (hsupport : G.HasSupportCardAtMost m)
    (hmax : G.HasMaximumDegreeAtMost D) :
    connectedShapeTripleMass G e ≤ m ^ 2 * D ^ (3 * e) := by
  have hDpos : 0 < D := by omega
  apply deterministicConnectedCount_of_finiteBounds G m D e
  exact
    { supportCard := hsupport
      maximumDegree := hmax
      labelledCopies :=
        connectedEmbeddingCountBound_of_supportCard_maxDegree
          G m D e hsupport hmax hDpos
      connectedCopies :=
        connectedConcreteCopySumBound_of_supportCard_maxDegree
          G m D e hsupport hmax hDpos }

end LowDegree

end
