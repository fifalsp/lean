import Mathlib.Combinatorics.SimpleGraph.Metric
import LowDegree.Combinatorics.WeightedTreePartition

/-!
# Adapter from finite graph trees to intrinsic weighted trees

`WeightedTreePartition.exists_partition` is stated for an intrinsic rose-tree
representation.  This file constructs that representation from an arbitrary
finite `SimpleGraph.IsTree` whose degrees are at most three.  We root at a leaf,
orient every other vertex towards the root along its unique path, and retain the
original vertex labels in an intermediate `RTree X`.

The label-retaining intermediate tree is important: it lets us prove that every
original vertex occurs in the intrinsic tree, rather than assuming the total
weight condition needed by `exists_partition`.  The final section specializes
the construction to the owner-node weights of an `EdgeOwnedRefinementWitness`.
-/

namespace LowDegree
namespace WeightedTreePartitionAdapter

open scoped BigOperators
open WeightedTreePartition

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

variable {X : Type*} [Fintype X] {Q : SimpleGraph X}

/-- A finite tree has a vertex of degree at most one, including the singleton
case where the unique vertex has degree zero. -/
theorem exists_root_degree_le_one (hQ : Q.IsTree) :
    ∃ r : X, Q.degree r ≤ 1 := by
  classical
  by_cases hX : Nontrivial X
  · letI : Nontrivial X := hX
    obtain ⟨r, hr⟩ := hQ.exists_vert_degree_one_of_nontrivial
    exact ⟨r, hr.le⟩
  · haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    obtain ⟨r⟩ := hQ.isConnected.nonempty
    refine ⟨r, ?_⟩
    have hn : Q.neighborFinset r = ∅ := by
      ext y
      have hyr : y = r := Subsingleton.elim _ _
      subst y
      simp
    rw [SimpleGraph.degree, hn]
    simp

/-- The shortest root-to-`x` path.  In a tree this is also the unique path. -/
def rootPath (hQ : Q.IsTree) (r x : X) : Q.Walk r x :=
  Classical.choose (hQ.isConnected.exists_path_of_dist r x)

omit [Fintype X] in
theorem rootPath_isPath (hQ : Q.IsTree) (r x : X) :
    (rootPath hQ r x).IsPath :=
  (Classical.choose_spec (hQ.isConnected.exists_path_of_dist r x)).1

omit [Fintype X] in
theorem rootPath_length (hQ : Q.IsTree) (r x : X) :
    (rootPath hQ r x).length = Q.dist r x :=
  (Classical.choose_spec (hQ.isConnected.exists_path_of_dist r x)).2

/-- The distance from the chosen root, expressed as the length of the retained
canonical path. -/
def height (hQ : Q.IsTree) (r x : X) : ℕ :=
  (rootPath hQ r x).length

/-- The predecessor of a vertex on its path from the root.  Its value at the
root itself is the root and is never used as a genuine parent edge. -/
def parent (hQ : Q.IsTree) (r x : X) : X :=
  (rootPath hQ r x).penultimate

omit [Fintype X] in
private theorem dropLast_isPath (hQ : Q.IsTree) (r x : X) :
    (rootPath hQ r x).dropLast.IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.dropLast,
    SimpleGraph.Walk.take_support_eq_support_take_succ]
  exact (rootPath_isPath hQ r x).support_nodup.take

omit [Fintype X] in
/-- The canonical path to a non-root vertex is the canonical path to its
parent followed by the last edge. -/
theorem rootPath_parent (hQ : Q.IsTree) (r x : X) :
    rootPath hQ r (parent hQ r x) = (rootPath hQ r x).dropLast := by
  have hpaths := hQ.IsAcyclic.path_unique
    (⟨rootPath hQ r (parent hQ r x), rootPath_isPath hQ r _⟩ :
      Q.Path r (parent hQ r x))
    (⟨(rootPath hQ r x).dropLast, dropLast_isPath hQ r x⟩ :
      Q.Path r (parent hQ r x))
  exact congrArg Subtype.val hpaths

omit [Fintype X] in
/-- Moving from a non-root vertex to its parent decreases height by exactly
one. -/
theorem height_parent_add_one (hQ : Q.IsTree) (r x : X) (hx : x ≠ r) :
    height hQ r (parent hQ r x) + 1 = height hQ r x := by
  rw [height, rootPath_parent hQ r x, height]
  have hp : 0 < (rootPath hQ r x).length := by
    rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
    exact SimpleGraph.Walk.not_nil_of_ne (Ne.symm hx)
  simp only [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_length]
  omega

omit [Fintype X] in
/-- The parent is adjacent to every non-root vertex. -/
theorem parent_adj (hQ : Q.IsTree) (r x : X) (hx : x ≠ r) :
    Q.Adj (parent hQ r x) x := by
  exact (rootPath hQ r x).adj_penultimate
    (SimpleGraph.Walk.not_nil_of_ne (Ne.symm hx))

/-! ### Exhaustion of the original tree edges -/

/-- The unoriented edge from a non-root vertex to its parent. -/
def orientedEdge (hQ : Q.IsTree) (r x : X) : Sym2 X :=
  s(parent hQ r x, x)

omit [Fintype X] in
/-- Different non-root vertices determine different parent edges. -/
theorem orientedEdge_injOn (hQ : Q.IsTree) (r : X) :
    Set.InjOn (orientedEdge hQ r) {x | x ≠ r} := by
  intro x hx y hy hxy
  rw [orientedEdge, orientedEdge, Sym2.eq_iff] at hxy
  rcases hxy with hxy | hxy
  · exact hxy.2
  · have hxHeight := height_parent_add_one hQ r x hx
    have hyHeight := height_parent_add_one hQ r y hy
    rw [hxy.1] at hxHeight
    rw [← hxy.2] at hyHeight
    omega

/-- The parent edges of all non-root vertices are exactly the edges of the
original finite tree. -/
theorem image_orientedEdge_eq_edgeFinset (hQ : Q.IsTree) (r : X) :
    ((Finset.univ.erase r).image (orientedEdge hQ r)) = Q.edgeFinset := by
  classical
  have hsubset : ((Finset.univ.erase r).image (orientedEdge hQ r)) ⊆
      Q.edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    rw [Finset.mem_erase] at hx
    rw [SimpleGraph.mem_edgeFinset, orientedEdge,
      SimpleGraph.mem_edgeSet]
    exact parent_adj hQ r x hx.1
  have himage : ((Finset.univ.erase r).image (orientedEdge hQ r)).card =
      (Finset.univ.erase r).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    apply orientedEdge_injOn hQ r
    · simpa using (Finset.mem_erase.mp hx).1
    · simpa using (Finset.mem_erase.mp hy).1
    · exact hxy
  have hrmem : r ∈ (Finset.univ : Finset X) := Finset.mem_univ r
  have herase : (Finset.univ.erase r).card = Fintype.card X - 1 := by
    rw [Finset.card_erase_of_mem hrmem, Finset.card_univ]
  have htreeCard := hQ.card_edgeFinset
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [himage, herase]
  omega

/-- Original adjacency is exactly the parent-child relation in the rooted
orientation. -/
theorem adj_iff_parent (hQ : Q.IsTree) (r x y : X) :
    Q.Adj x y ↔
      (y ≠ r ∧ parent hQ r y = x) ∨
        (x ≠ r ∧ parent hQ r x = y) := by
  constructor
  · intro hxy
    have hedge : s(x, y) ∈ Q.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hxy
    rw [← image_orientedEdge_eq_edgeFinset hQ r,
      Finset.mem_image] at hedge
    obtain ⟨z, hz, heq⟩ := hedge
    have hzroot : z ≠ r := (Finset.mem_erase.mp hz).1
    rw [orientedEdge, Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · rcases heq with ⟨hparent, rfl⟩
      exact Or.inl ⟨hzroot, hparent⟩
    · rcases heq with ⟨hparent, rfl⟩
      exact Or.inr ⟨hzroot, hparent⟩
  · rintro (h | h)
    · simpa [h.2] using parent_adj hQ r y h.1
    · simpa [h.2] using (parent_adj hQ r x h.1).symm

/-- Children in the orientation away from the root. -/
def children (hQ : Q.IsTree) (r x : X) : Finset X :=
  Finset.univ.filter fun y ↦ y ≠ r ∧ parent hQ r y = x

@[simp]
theorem mem_children_iff (hQ : Q.IsTree) (r x y : X) :
    y ∈ children hQ r x ↔ y ≠ r ∧ parent hQ r y = x := by
  simp [children]

/-- A child is one level farther from the root. -/
theorem height_lt_of_mem_children (hQ : Q.IsTree) (r x y : X)
    (hy : y ∈ children hQ r x) :
    height hQ r x < height hQ r y := by
  rw [mem_children_iff] at hy
  have hh := height_parent_add_one hQ r y hy.1
  rw [hy.2] at hh
  omega

/-- Oriented children are actual graph neighbors. -/
theorem adj_of_mem_children (hQ : Q.IsTree) (r x y : X)
    (hy : y ∈ children hQ r x) : Q.Adj x y := by
  rw [mem_children_iff] at hy
  simpa [hy.2] using parent_adj hQ r y hy.1

theorem children_subset_neighborFinset (hQ : Q.IsTree) (r x : X) :
    children hQ r x ⊆ Q.neighborFinset x := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset]
  exact adj_of_mem_children hQ r x y hy

/-- Rooting a subcubic tree at a vertex of degree at most one leaves at most
two oriented children at every node. -/
theorem children_card_le_two (hQ : Q.IsTree) (hdeg : ∀ x, Q.degree x ≤ 3)
    {r : X} (hroot : Q.degree r ≤ 1) (x : X) :
    (children hQ r x).card ≤ 2 := by
  classical
  by_cases hx : x = r
  · subst x
    have hc := Finset.card_le_card (children_subset_neighborFinset hQ r r)
    change (children hQ r r).card ≤ Q.degree r at hc
    omega
  · have hpmem : parent hQ r x ∈ Q.neighborFinset x := by
      rw [SimpleGraph.mem_neighborFinset]
      exact (parent_adj hQ r x hx).symm
    have hpnot : parent hQ r x ∉ children hQ r x := by
      intro hp
      have hforward := height_lt_of_mem_children hQ r x (parent hQ r x) hp
      have hback := height_parent_add_one hQ r x hx
      omega
    have hsubset : children hQ r x ⊆
        (Q.neighborFinset x).erase (parent hQ r x) := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, children_subset_neighborFinset hQ r x hy⟩
      intro hypar
      subst y
      exact hpnot hy
    have hc := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hpmem] at hc
    change (children hQ r x).card ≤ Q.degree x - 1 at hc
    have hd := hdeg x
    omega

/-! ### The label-retaining intrinsic tree -/

/-- The well-founded relation used to recurse away from the root.  A recursive
call is made at a strictly greater height; this is well-founded because the
vertex type is finite. -/
def farther (hQ : Q.IsTree) (r : X) (y x : X) : Prop :=
  height hQ r x < height hQ r y

theorem farther_wellFounded (hQ : Q.IsTree) (r : X) :
    WellFounded (farther hQ r) := by
  letI : IsTrans X (farther hQ r) :=
    ⟨by
      intro a b c hab hbc
      exact lt_trans hbc hab⟩
  letI : IsIrrefl X (farther hQ r) :=
    ⟨by
      intro a ha
      exact (lt_irrefl _ ha)⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

private def labeledTreeStep (hQ : Q.IsTree) (r x : X)
    (rec : ∀ y : X, farther hQ r y x → RTree X) : RTree X :=
  .node x <| (children hQ r x).attach.toList.map fun y ↦
    rec y.val (by
      change height hQ r x < height hQ r y.val
      exact height_lt_of_mem_children hQ r x y.val y.property)

/-- The rose tree obtained by orienting `Q` away from `r`.  Its labels retain
the original graph vertices. -/
def labeledTree (hQ : Q.IsTree) (r x : X) : RTree X :=
  (farther_wellFounded hQ r).fix (labeledTreeStep hQ r) x

theorem labeledTree_eq (hQ : Q.IsTree) (r x : X) :
    labeledTree hQ r x =
      .node x ((children hQ r x).attach.toList.map fun y ↦
        labeledTree hQ r y.1) := by
  rw [labeledTree, WellFounded.fix_eq]
  rfl

/-! ### Boolean weights and subcubicity -/

/-- Convert a natural weight known to be at most one into a Boolean label. -/
def boolWeight (w : X → ℕ) (x : X) : Bool :=
  decide (w x = 1)

omit [Fintype X] in
@[simp]
theorem nodeWeight_boolWeight (w : X → ℕ) (hw : ∀ x, w x ≤ 1) (x : X) :
    nodeWeight (boolWeight w x) = w x := by
  have hbound := hw x
  have hx : w x = 0 ∨ w x = 1 := by omega
  rcases hx with hx | hx <;> simp [boolWeight, nodeWeight, hx]

/-- Replace retained vertex labels by their Boolean weights. -/
def withWeights (w : X → ℕ) : RTree X → WeightedTree
  | .node x children => .node (boolWeight w x) (children.map (withWeights w))

private theorem isSubcubic_node_of_forall {b : Bool} {ts : List WeightedTree}
    (hlen : ts.length ≤ 2) (hall : ∀ t ∈ ts, IsSubcubic t) :
    IsSubcubic (.node b ts) := by
  cases ts with
  | nil => exact .leaf b
  | cons t ts =>
      cases ts with
      | nil => exact .unary b (hall t (by simp))
      | cons u ts =>
          cases ts with
          | nil => exact .binary b (hall t (by simp)) (hall u (by simp))
          | cons v vs => simp at hlen

/-- The intrinsic tree produced from a subcubic graph tree is intrinsically
subcubic. -/
theorem withWeights_labeledTree_isSubcubic (hQ : Q.IsTree)
    (hdeg : ∀ x, Q.degree x ≤ 3) {r : X} (hroot : Q.degree r ≤ 1)
    (w : X → ℕ) (x : X) :
    IsSubcubic (withWeights w (labeledTree hQ r x)) := by
  induction x using (farther_wellFounded hQ r).induction with
  | h x ih =>
      rw [labeledTree_eq, withWeights]
      apply isSubcubic_node_of_forall
      · simpa using children_card_le_two hQ hdeg hroot x
      · intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        rw [List.mem_map] at hs
        obtain ⟨y, _hy, rfl⟩ := hs
        apply ih y.val
        change height hQ r x < height hQ r y.val
        exact height_lt_of_mem_children hQ r x y.val y.property

/-! ### Coverage of the original vertex labels -/

/-- Preorder list of the labels in a rose tree. -/
def vertices : RTree X → List X
  | .node x children => x :: (children.map vertices).flatten

/-- Root label of a nonempty rose tree. -/
def rootLabel : RTree X → X
  | .node x _ => x

/-- Structural subtree occurrence. -/
inductive IsSubtree (s : RTree X) : RTree X → Prop where
  | refl : IsSubtree s s
  | descend {a : X} {children : List (RTree X)} {t : RTree X} :
      t ∈ children → IsSubtree s t → IsSubtree s (.node a children)

namespace IsSubtree

omit [Fintype X] in
theorem trans {s t u : RTree X} (hst : IsSubtree s t) (htu : IsSubtree t u) :
    IsSubtree s u := by
  induction htu with
  | refl => exact hst
  | descend ht _ ih => exact .descend ht ih

omit [Fintype X] in
private theorem mem_flatten_of_mem_tree {x : X} {t : RTree X}
    {ts : List (RTree X)} (ht : t ∈ ts) (hx : x ∈ vertices t) :
    x ∈ (ts.map vertices).flatten := by
  rw [List.mem_flatten]
  refine ⟨vertices t, ?_, hx⟩
  exact List.mem_map.mpr ⟨t, ht, rfl⟩

omit [Fintype X] in
/-- The root label of a structural subtree occurs among the labels of the
ambient tree. -/
theorem rootLabel_mem_vertices {s t : RTree X} (h : IsSubtree s t) :
    rootLabel s ∈ vertices t := by
  induction h with
  | refl => cases s; simp [rootLabel, vertices]
  | descend ht _ ih =>
      simp only [vertices, List.mem_cons]
      exact Or.inr (mem_flatten_of_mem_tree ht ih)

end IsSubtree

/-- An oriented child gives an immediate structural subtree. -/
theorem labeledTree_child_isSubtree (hQ : Q.IsTree) (r x y : X)
    (hy : y ∈ children hQ r x) :
    IsSubtree (labeledTree hQ r y) (labeledTree hQ r x) := by
  conv_rhs => rw [labeledTree_eq]
  have hmem : labeledTree hQ r y ∈
      ((children hQ r x).attach.toList.map fun z ↦ labeledTree hQ r z.val) := by
    rw [List.mem_map]
    exact ⟨⟨y, hy⟩, by simp, rfl⟩
  exact IsSubtree.descend hmem .refl

/-- Every vertex-rooted intrinsic subtree occurs below the global root. -/
theorem labeledTree_isSubtree_root (hQ : Q.IsTree) (r y : X) :
    IsSubtree (labeledTree hQ r y) (labeledTree hQ r r) := by
  apply (measure (height hQ r)).wf.induction y
  intro y ih
  by_cases hyr : y = r
  · subst y
    exact .refl
  · have hpheight : height hQ r (parent hQ r y) < height hQ r y := by
      have hh := height_parent_add_one hQ r y hyr
      omega
    have hpSubtree :
        IsSubtree (labeledTree hQ r (parent hQ r y)) (labeledTree hQ r r) :=
      ih (parent hQ r y) hpheight
    have hyChild : y ∈ children hQ r (parent hQ r y) := by
      rw [mem_children_iff]
      exact ⟨hyr, rfl⟩
    exact (labeledTree_child_isSubtree hQ r (parent hQ r y) y hyChild).trans hpSubtree

/-- Every original graph vertex occurs in the label-retaining intrinsic tree. -/
theorem mem_vertices_labeledTree_root (hQ : Q.IsTree) (r y : X) :
    y ∈ vertices (labeledTree hQ r r) := by
  have hm := (labeledTree_isSubtree_root hQ r y).rootLabel_mem_vertices
  have hroot : rootLabel (labeledTree hQ r y) = y := by
    rw [labeledTree_eq]
    rfl
  rwa [hroot] at hm

/-! ### Uniqueness of the retained labels -/

/-- `z` is below `x` in the orientation away from `r`, expressed using the
iterated parent map.  The numerical component makes the iteration count
canonical. -/
def IsDescendant (hQ : Q.IsTree) (r x z : X) : Prop :=
  ∃ n : ℕ,
    height hQ r z = height hQ r x + n ∧
      (parent hQ r)^[n] z = x

/-- Every label occurring in the subtree rooted at `x` is an oriented
descendant of `x`. -/
theorem isDescendant_of_mem_vertices_labeledTree (hQ : Q.IsTree) (r x z : X)
    (hz : z ∈ vertices (labeledTree hQ r x)) :
    IsDescendant hQ r x z := by
  induction x using (farther_wellFounded hQ r).induction with
  | h x ih =>
      rw [labeledTree_eq, vertices] at hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨0, by simp, by simp⟩
      · rw [List.mem_flatten] at hz
        obtain ⟨labels, hlabels, hz⟩ := hz
        rw [List.mem_map] at hlabels
        obtain ⟨subtree, hsubtree, rfl⟩ := hlabels
        rw [List.mem_map] at hsubtree
        obtain ⟨y, _hy, rfl⟩ := hsubtree
        have hyFarther : farther hQ r y.val x := by
          change height hQ r x < height hQ r y.val
          exact height_lt_of_mem_children hQ r x y.val y.property
        obtain ⟨n, hheight, hiterate⟩ := ih y.val hyFarther hz
        have hyChild : y.val ≠ r ∧ parent hQ r y.val = x :=
          (mem_children_iff hQ r x y.val).mp y.property
        refine ⟨n + 1, ?_, ?_⟩
        · have hyHeight := height_parent_add_one hQ r y.val hyChild.1
          rw [hyChild.2] at hyHeight
          omega
        · rw [show n + 1 = n.succ by omega, Function.iterate_succ_apply']
          rw [hiterate, hyChild.2]

/-- The rooted encoding visits every original vertex exactly once. -/
theorem vertices_labeledTree_nodup (hQ : Q.IsTree) (r x : X) :
    (vertices (labeledTree hQ r x)).Nodup := by
  induction x using (farther_wellFounded hQ r).induction with
  | h x ih =>
      rw [labeledTree_eq, vertices, List.nodup_cons]
      constructor
      · intro hx
        rw [List.mem_flatten] at hx
        obtain ⟨labels, hlabels, hx⟩ := hx
        rw [List.mem_map] at hlabels
        obtain ⟨subtree, hsubtree, rfl⟩ := hlabels
        rw [List.mem_map] at hsubtree
        obtain ⟨y, _hy, rfl⟩ := hsubtree
        obtain ⟨n, hheight, _hiterate⟩ :=
          isDescendant_of_mem_vertices_labeledTree hQ r y.val x hx
        have hyChild : y.val ≠ r ∧ parent hQ r y.val = x :=
          (mem_children_iff hQ r x y.val).mp y.property
        have hyHeight := height_parent_add_one hQ r y.val hyChild.1
        rw [hyChild.2] at hyHeight
        omega
      · rw [List.nodup_flatten]
        constructor
        · intro labels hlabels
          rw [List.mem_map] at hlabels
          obtain ⟨subtree, hsubtree, rfl⟩ := hlabels
          rw [List.mem_map] at hsubtree
          obtain ⟨y, _hy, rfl⟩ := hsubtree
          apply ih y.val
          change height hQ r x < height hQ r y.val
          exact height_lt_of_mem_children hQ r x y.val y.property
        · rw [List.pairwise_map, List.pairwise_map]
          apply (children hQ r x).attach.nodup_toList.pairwise_of_forall_ne
          intro y _hy z _hz hyz
          rw [List.disjoint_left]
          intro a hay haz
          obtain ⟨ny, hheighty, hitery⟩ :=
            isDescendant_of_mem_vertices_labeledTree hQ r y.val a hay
          obtain ⟨nz, hheightz, hiterz⟩ :=
            isDescendant_of_mem_vertices_labeledTree hQ r z.val a haz
          have hyChild : y.val ≠ r ∧ parent hQ r y.val = x :=
            (mem_children_iff hQ r x y.val).mp y.property
          have hzChild : z.val ≠ r ∧ parent hQ r z.val = x :=
            (mem_children_iff hQ r x z.val).mp z.property
          have hyHeight := height_parent_add_one hQ r y.val hyChild.1
          have hzHeight := height_parent_add_one hQ r z.val hzChild.1
          rw [hyChild.2] at hyHeight
          rw [hzChild.2] at hzHeight
          have hn : ny = nz := by omega
          subst nz
          exact hyz (Subtype.ext (hitery.symm.trans hiterz))

/-! ### Numerical faithfulness -/

private theorem le_sum_map_of_mem {A : Type*} (f : A → ℕ) {a : A}
    {l : List A} (ha : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      simp only [List.map_cons, List.sum_cons]
      rcases ha with rfl | ha
      · omega
      · have := ih ha
        omega

omit [Fintype X] in
/-- The weight of `withWeights` is the sum of the retained natural labels. -/
theorem totalWeight_withWeights_eq_sum_vertices (w : X → ℕ)
    (hw : ∀ x, w x ≤ 1) (t : RTree X) :
    totalWeight (withWeights w t) = (vertices t |>.map w).sum := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | node x children =>
          simp only [withWeights, totalWeight, vertices, List.map_cons, List.sum_cons,
            nodeWeight_boolWeight w hw]
          congr 1
          calc
            ((children.map (withWeights w)).map totalWeight).sum =
                (children.map fun child ↦ (vertices child |>.map w).sum).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro child hchild
              have hle : RTree.card child ≤ (children.map RTree.card).sum :=
                le_sum_map_of_mem RTree.card hchild
              have hlt : RTree.card child < n := by
                simp only [RTree.card] at hcard
                omega
              exact ih (RTree.card child) hlt child rfl
            _ = (((children.map vertices).flatten).map w).sum := by
              simp only [List.map_flatten, List.sum_flatten, List.map_map]
              apply congrArg List.sum
              apply List.map_congr_left
              intro child _
              rfl

omit [Fintype X] in
private theorem sum_toFinset_le_sum (w : X → ℕ) (l : List X) :
    (∑ x ∈ l.toFinset, w x) ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases ha : a ∈ l
      · rw [Finset.insert_eq_of_mem (by simpa using ha)]
        omega
      · rw [Finset.sum_insert (by simpa using ha)]
        omega

/-- The intrinsic rooted encoding contains at least the total weight of the
original graph vertices.  The one-sided statement follows from the formally
proved coverage theorem and is the precise fact needed to discharge the
hypothesis of `exists_partition`. -/
theorem sum_weights_le_totalWeight (hQ : Q.IsTree) (r : X) (w : X → ℕ)
    (hw : ∀ x, w x ≤ 1) :
    (∑ x : X, w x) ≤ totalWeight (withWeights w (labeledTree hQ r r)) := by
  let labels := vertices (labeledTree hQ r r)
  have hlabels : labels.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    simpa [labels] using mem_vertices_labeledTree_root hQ r y
  calc
    (∑ x : X, w x) = ∑ x ∈ labels.toFinset, w x := by rw [hlabels]
    _ ≤ (labels.map w).sum := sum_toFinset_le_sum w labels
    _ = totalWeight (withWeights w (labeledTree hQ r r)) := by
      symm
      exact totalWeight_withWeights_eq_sum_vertices w hw _

/-! ### Adapter theorem -/

/-- **Finite graph-tree adapter for node-weighted Lemma 5.4.**

An arbitrary finite tree of maximum degree at most three, with natural node
weights at most one and total weight at least `ℓ`, can be rooted and passed to
the intrinsic weighted-tree partition theorem.  The existential root has
degree at most one, the displayed input to `IsPartition` is the actual rooted
encoding of `Q`, and every quotient label lies in `[ℓ, 3ℓ]`.

No partition or clustering data is assumed. -/
theorem exists_intrinsic_partition (hQ : Q.IsTree)
    (hdeg : ∀ x, Q.degree x ≤ 3) (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (htotal : ℓ ≤ ∑ x : X, w x) :
    ∃ r : X, ∃ q : QuotientTree,
      Q.degree r ≤ 1 ∧
      IsSubcubic (withWeights w (labeledTree hQ r r)) ∧
      IsPartition (withWeights w (labeledTree hQ r r)) q ∧
      LabelsIn ℓ (3 * ℓ) q := by
  obtain ⟨r, hroot⟩ := exists_root_degree_le_one hQ
  have hsubcubic := withWeights_labeledTree_isSubcubic hQ hdeg hroot w r
  have hencodedTotal : ℓ ≤ totalWeight (withWeights w (labeledTree hQ r r)) :=
    htotal.trans (sum_weights_le_totalWeight hQ r w hw)
  obtain ⟨q, hpartition, hlabels⟩ :=
    WeightedTreePartition.exists_partition hsubcubic hℓ hencodedTotal
  exact ⟨r, q, hroot, hsubcubic, hpartition, hlabels⟩

/-! ### Edge-owned refinement specialization -/

open TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The edge-owner weights of a subcubic refinement satisfy all numerical and
structural hypotheses of the intrinsic Lemma 5.4 theorem.  In particular, the
total Boolean weight is discharged from the actual edge count, not assumed on
the encoded rose tree. -/
theorem EdgeOwnedRefinementWitness.exists_intrinsic_owner_partition
    (R : EdgeOwnedRefinementWitness G X) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (htotal : ℓ ≤ G.edgeFinset.card) :
    ∃ r : X, ∃ q : QuotientTree,
      R.decomposition.tree.degree r ≤ 1 ∧
      IsSubcubic
        (withWeights (WeightedTreePartition.ownedWeight R)
          (labeledTree R.decomposition.isTree r r)) ∧
      IsPartition
        (withWeights (WeightedTreePartition.ownedWeight R)
          (labeledTree R.decomposition.isTree r r)) q ∧
      LabelsIn ℓ (3 * ℓ) q := by
  have hsum : ℓ ≤ ∑ x : X, WeightedTreePartition.ownedWeight R x := by
    rw [WeightedTreePartition.sum_ownedWeight R]
    exact htotal
  exact exists_intrinsic_partition R.decomposition.isTree R.subcubic
    (WeightedTreePartition.ownedWeight R)
    (WeightedTreePartition.ownedWeight_le_one R) hℓ hsum

/-!
The theorem above deliberately stops at an intrinsic `IsPartition`.  That
relation is indexed only by the Boolean-weighted `RTree`; its quotient stores
cluster weights and child structure, but no original `X` labels or node
addresses.  Consequently its output alone cannot define the `clusterOf : X →
Fin m` field of `ClusterQuotientWitness`, nor state that those fibers induce
connected subgraphs of the original `SimpleGraph X`.  Closing that final gap
requires a label-preserving refinement of `RootSplit`/`IsPartition` (or a
synchronized replay of the packing algorithm on `RTree X`), rather than an
additional premise on the input graph.
-/

end

end WeightedTreePartitionAdapter
end LowDegree
