import LowDegree.Combinatorics.IndexedWeightedTreePartition

/-!
# Edge-owned subcubic refinements of tree decompositions

This file formalizes Lemma 5.3 of the paper.  Starting from a finite tree
decomposition, every decomposition node is replaced by a finite binary spine.
The original child subtrees are attached along the spine, and every graph edge
hosted at that node receives its own unary spine node.  Bags are copied from
the original node to its whole spine (including its owner nodes).

The resulting occurrence graph is a tree of maximum degree three.  Distinct
graph edges have distinct owner nodes, and the copied bag at an owner node
contains both endpoints of its edge.
-/

namespace LowDegree
namespace TreeDecomposition

open WeightedTreePartition
open WeightedTreePartitionAdapter
open IndexedWeightedTreePartition

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

variable {V X Y : Type*}

/-! ### A general connected-fiber lifting lemma -/

/-- The inverse image of a connected vertex set is connected when all fibers
are connected and every edge downstairs has an edge lift upstairs. -/
theorem connected_induce_preimage_of_connected_fibers
    {Q : SimpleGraph X} {R : SimpleGraph Y} (q : Y → X)
    (hfiber : ∀ x : X, (R.induce {y : Y | q y = x}).Connected)
    (hlift : ∀ ⦃x z : X⦄, Q.Adj x z →
      ∃ y w : Y, q y = x ∧ q w = z ∧ R.Adj y w)
    {S : Set X} (hS : (Q.induce S).Connected) :
    (R.induce {y : Y | q y ∈ S}).Connected := by
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  obtain ⟨y₀, hy₀⟩ := (hfiber x₀).nonempty
  have hy₀q : q y₀ = x₀ := hy₀
  let x₀' : S := ⟨x₀, hx₀⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨y₀, by change q y₀ ∈ S; rw [hy₀q]; exact hx₀⟩, ?_⟩
  rintro ⟨y, hyS⟩
  let x : S := ⟨q y, hyS⟩
  have hdown : (Q.induce S).Reachable x₀' x := hS x₀' x
  rcases hdown with ⟨p⟩
  have liftWalk : ∀ ⦃a b : S⦄,
      (p : (Q.induce S).Walk a b) → ∀ (u v : Y)
        (hu : q u = a.1) (hv : q v = b.1)
        (huS : q u ∈ S) (hvS : q v ∈ S),
        (R.induce {w : Y | q w ∈ S}).Reachable
          ⟨u, huS⟩ ⟨v, hvS⟩ := by
    intro a b p
    induction p with
    | @nil z =>
        intro u v hu hv huS hvS
        have huv := (hfiber z.1) ⟨u, hu⟩ ⟨v, hv⟩
        simpa only using huv.map (SimpleGraph.induceHomOfLE R (by
          intro w hw
          change q w ∈ S
          rw [hw]
          exact z.2)).toHom
    | @cons a b c hab p ih =>
        intro u v hu hv huS hvS
        obtain ⟨u', v', hu', hv', huv'⟩ := hlift hab
        have huu' := (hfiber a.1) ⟨u, hu⟩ ⟨u', hu'⟩
        have huu'S : (R.induce {w : Y | q w ∈ S}).Reachable
            ⟨u, huS⟩ ⟨u', by simpa [hu'] using a.2⟩ :=
          huu'.map (SimpleGraph.induceHomOfLE R (by
            intro w hw
            change q w ∈ S
            rw [hw]
            exact a.2)).toHom
        have hu'v'S : (R.induce {w : Y | q w ∈ S}).Adj
            ⟨u', by simpa [hu'] using a.2⟩
            ⟨v', by simpa [hv'] using b.2⟩ := by
          exact huv'
        have hv'v := ih v' v hv' hv (by simpa [hv'] using b.2) hvS
        exact huu'S.trans (hu'v'S.reachable.trans hv'v)
  exact liftWalk p y₀ y hy₀q rfl
    (by change q y₀ ∈ S; rw [hy₀q]; exact hx₀) hyS

/-! ### The binary-spine construction -/

variable [Fintype V] [Fintype X] {G : SimpleGraph V}

/-- An edge of `G`, bundled with its edge-set membership proof. -/
abbrev GraphEdge (G : SimpleGraph V) := G.edgeSet

/-- A bag containing both endpoints of an edge exists in every decomposition. -/
theorem Decomposition.exists_edge_host (D : Decomposition G X)
    (e : GraphEdge G) :
    ∃ x : X, ∀ v ∈ e.1.toFinset, v ∈ D.bag x := by
  let u : V := e.1.out.1
  let v : V := e.1.out.2
  have heq : s(u, v) = e.1 := Quot.out_eq e.1
  have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp (heq ▸ e.2)
  obtain ⟨x, hu, hv⟩ := D.edge_mem huv
  refine ⟨x, ?_⟩
  intro w hw
  rw [← heq] at hw
  simp at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

/-- A fixed original decomposition node that hosts a graph edge. -/
def Decomposition.edgeHost (D : Decomposition G X) (e : GraphEdge G) : X :=
  Classical.choose (D.exists_edge_host e)

theorem Decomposition.mem_bag_edgeHost (D : Decomposition G X)
    (e : GraphEdge G) {v : V} (hv : v ∈ e.1.toFinset) :
    v ∈ D.bag (D.edgeHost e) :=
  Classical.choose_spec (D.exists_edge_host e) v hv

/-- Labels used by the intrinsic refinement.  `spine x` is a copied bag node;
`owner e` is the unique unary spine node assigned to the graph edge `e`. -/
inductive RefinementLabel (D : Decomposition G X) where
  | spine (x : X)
  | owner (e : GraphEdge G)
  deriving DecidableEq

namespace RefinementLabel

/-- Original decomposition node whose bag is copied to a refinement label. -/
def base (D : Decomposition G X) : RefinementLabel D → X
  | .spine x => x
  | .owner e => D.edgeHost e

end RefinementLabel

/-- The owner edges hosted by `x`, in an arbitrary fixed order. -/
def hostedEdges (D : Decomposition G X) (x : X) : List (GraphEdge G) :=
  ((Finset.univ.filter fun e : GraphEdge G ↦ D.edgeHost e = x).toList)

@[simp]
theorem mem_hostedEdges_iff (D : Decomposition G X) (x : X)
    (e : GraphEdge G) :
    e ∈ hostedEdges D x ↔ D.edgeHost e = x := by
  simp [hostedEdges]

/-- An item placed along the refinement spine.  A child item attaches one
refined original child subtree; an owner item makes the current spine node the
unique owner of a graph edge. -/
inductive SpineItem (D : Decomposition G X) where
  | child (t : RTree (RefinementLabel D))
  | owner (e : GraphEdge G)

/-- Attach child subtrees and edge owners along a binary spine carrying copies
of the bag at `x`.  A child node has two children (the attachment and the rest
of the spine), while an owner node has only the rest of the spine. -/
def binarySpine (D : Decomposition G X) (x : X) :
    List (SpineItem D) → RTree (RefinementLabel D)
  | [] => .node (.spine x) []
  | .child t :: ts => .node (.spine x) [t, binarySpine D x ts]
  | .owner e :: ts => .node (.owner e) [binarySpine D x ts]

/-- Replace every original node by its binary spine.  Refined child subtrees
are spine attachments, while owner nodes occur along the spine. -/
def refineTree (D : Decomposition G X) : RTree X → RTree (RefinementLabel D)
  | .node x children =>
      binarySpine D x
        (children.map (fun t ↦ SpineItem.child (refineTree D t)) ++
          (hostedEdges D x).map SpineItem.owner)

/-- A binary spine is intrinsically binary when all attached child trees are. -/
theorem binarySpine_allChildrenCardLE (D : Decomposition G X) (x : X)
    (items : List (SpineItem D))
    (hchildren : ∀ t, SpineItem.child t ∈ items →
      IndexedWeightedTreePartition.Node.AllChildrenCardLE 2 t) :
    IndexedWeightedTreePartition.Node.AllChildrenCardLE 2
      (binarySpine D x items) := by
  induction items with
  | nil => simp [binarySpine, IndexedWeightedTreePartition.Node.AllChildrenCardLE]
  | cons item items ih =>
      cases item with
      | child t =>
          rw [binarySpine, IndexedWeightedTreePartition.Node.AllChildrenCardLE]
          constructor
          · simp
          · intro s hs
            simp at hs
            rcases hs with hs | hs
            · subst s
              exact hchildren _ (by simp)
            · subst s
              exact ih (fun u hu ↦ hchildren u (by simp [hu]))
      | owner e =>
          rw [binarySpine, IndexedWeightedTreePartition.Node.AllChildrenCardLE]
          constructor
          · simp
          · intro s hs
            simp only [List.mem_singleton] at hs
            subst s
            exact ih (fun u hu ↦ hchildren u (by simp [hu]))

/-- A summand selected from a list is at most the whole sum. -/
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

/-- Every rose tree produced by the refinement is intrinsically binary. -/
theorem refineTree_allChildrenCardLE (D : Decomposition G X) (t : RTree X) :
    IndexedWeightedTreePartition.Node.AllChildrenCardLE 2 (refineTree D t) := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | node x children =>
          rw [refineTree]
          apply binarySpine_allChildrenCardLE
          intro s hs
          rw [List.mem_append] at hs
          rcases hs with hs | hs
          · rw [List.mem_map] at hs
            obtain ⟨child, hchild, hinj⟩ := hs
            cases hinj
            apply ih (RTree.card child)
            · have hle : RTree.card child ≤
                  (children.map RTree.card).sum :=
                le_sum_map_of_mem RTree.card hchild
              simp only [RTree.card] at hcard
              omega
            · rfl
          · rw [List.mem_map] at hs
            obtain ⟨e, _he, hinj⟩ := hs
            cases hinj

/-- An arbitrary fixed root of the original decomposition tree. -/
def Decomposition.root (D : Decomposition G X) : X :=
  Classical.choice D.isTree.isConnected.nonempty

/-- The original decomposition tree, rooted and represented intrinsically. -/
def Decomposition.rootedTree (D : Decomposition G X) : RTree X :=
  labeledTree D.isTree D.root D.root

/-- Intrinsic binary refinement of a tree decomposition. -/
def Decomposition.refinedTree (D : Decomposition G X) :
    RTree (RefinementLabel D) :=
  refineTree D D.rootedTree

/-- Nodes of the refined decomposition tree are occurrences in its intrinsic
binary-tree representation. -/
abbrev RefinedNode (D : Decomposition G X) :=
  IndexedWeightedTreePartition.Node D.refinedTree

/-- Projection of a refined occurrence to the original node whose bag it
copies. -/
def Decomposition.refinedBase (D : Decomposition G X) (n : RefinedNode D) : X :=
  RefinementLabel.base D (IndexedWeightedTreePartition.Node.label n)

/-- The structural tree on refined node occurrences. -/
def Decomposition.refinedGraph (D : Decomposition G X) :
    SimpleGraph (RefinedNode D) :=
  IndexedWeightedTreePartition.Node.graph D.refinedTree

theorem Decomposition.refinedGraph_isTree (D : Decomposition G X) :
    D.refinedGraph.IsTree :=
  IndexedWeightedTreePartition.Node.graph_isTree D.refinedTree

/-- The refined structural tree has maximum degree three. -/
theorem Decomposition.refinedGraph_subcubic (D : Decomposition G X)
    (n : RefinedNode D) : D.refinedGraph.degree n ≤ 3 := by
  exact IndexedWeightedTreePartition.Node.graph_degree_le_succ
    (refineTree_allChildrenCardLE D D.rootedTree) n

/-! ### Owner occurrences -/

/-- Labels in an attached child tree remain present in the surrounding binary
spine. -/
theorem mem_vertices_binarySpine_of_child (D : Decomposition G X) (x : X)
    {items : List (SpineItem D)} {t : RTree (RefinementLabel D)}
    (ht : SpineItem.child t ∈ items) {a : RefinementLabel D}
    (ha : a ∈ vertices t) : a ∈ vertices (binarySpine D x items) := by
  induction items with
  | nil => simp at ht
  | cons item items ih =>
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst item
        simp [binarySpine, vertices, ha]
      · cases item with
        | child u =>
            have htail := ih ht
            simp [binarySpine, vertices, htail]
        | owner e =>
            have htail := ih ht
            simp [binarySpine, vertices, htail]

/-- The label of an owner item occurs on its binary spine. -/
theorem owner_mem_vertices_binarySpine (D : Decomposition G X) (x : X)
    {items : List (SpineItem D)} {e : GraphEdge G}
    (he : SpineItem.owner e ∈ items) :
    RefinementLabel.owner e ∈ vertices (binarySpine D x items) := by
  induction items with
  | nil => simp at he
  | cons item items ih =>
      rw [List.mem_cons] at he
      rcases he with he | he
      · subst item
        simp [binarySpine, vertices]
      · cases item with
        | child t =>
            have htail := ih he
            simp [binarySpine, vertices, htail]
        | owner f =>
            have htail := ih he
            simp [binarySpine, vertices, htail]

/-- If the host of `e` occurs in the input rose tree, the refinement contains
the corresponding owner label. -/
theorem owner_mem_vertices_refineTree (D : Decomposition G X)
    (e : GraphEdge G) (t : RTree X)
    (he : D.edgeHost e ∈ vertices t) :
    RefinementLabel.owner e ∈ vertices (refineTree D t) := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | node x children =>
          simp only [vertices, List.mem_cons] at he
          rw [refineTree]
          rcases he with he | he
          · have hx : D.edgeHost e = x := he
            have hehosted : e ∈ hostedEdges D x :=
              (mem_hostedEdges_iff D x e).mpr hx
            apply owner_mem_vertices_binarySpine D x
            rw [List.mem_append]
            exact Or.inr (List.mem_map.mpr ⟨e, hehosted, rfl⟩)
          · rw [List.mem_flatten] at he
            obtain ⟨labels, hlabels, he⟩ := he
            rw [List.mem_map] at hlabels
            obtain ⟨child, hchild, rfl⟩ := hlabels
            have hle : RTree.card child ≤
                (children.map RTree.card).sum :=
              le_sum_map_of_mem RTree.card hchild
            have hlt : RTree.card child < n := by
              simp only [RTree.card] at hcard
              omega
            have howner := ih (RTree.card child) hlt child he rfl
            apply mem_vertices_binarySpine_of_child D x
              (t := refineTree D child)
            · rw [List.mem_append]
              exact Or.inl (List.mem_map.mpr ⟨child, hchild, rfl⟩)
            · exact howner

theorem Decomposition.ownerLabel_mem_refinedTree (D : Decomposition G X)
    (e : GraphEdge G) :
    RefinementLabel.owner e ∈ vertices D.refinedTree := by
  apply owner_mem_vertices_refineTree D e D.rootedTree
  exact mem_vertices_labeledTree_root D.isTree D.root (D.edgeHost e)

/-- Canonical occurrence of the unique owner label for `e`. -/
def Decomposition.ownerNode (D : Decomposition G X) (e : GraphEdge G) :
    RefinedNode D :=
  Classical.choose
    (IndexedWeightedTreePartition.Node.exists_node_of_mem_vertices
      (D.ownerLabel_mem_refinedTree e))

theorem Decomposition.ownerNode_label (D : Decomposition G X)
    (e : GraphEdge G) :
    IndexedWeightedTreePartition.Node.label (D.ownerNode e) =
      RefinementLabel.owner e :=
  Classical.choose_spec
    (IndexedWeightedTreePartition.Node.exists_node_of_mem_vertices
      (D.ownerLabel_mem_refinedTree e))

theorem Decomposition.ownerNode_base (D : Decomposition G X)
    (e : GraphEdge G) : D.refinedBase (D.ownerNode e) = D.edgeHost e := by
  simp [Decomposition.refinedBase, D.ownerNode_label, RefinementLabel.base]

/-- Owner map on all symmetric pairs, with an arbitrary root value off the
actual edge set. -/
def Decomposition.refinedOwner (D : Decomposition G X) (e : Sym2 V) :
    RefinedNode D :=
  if he : e ∈ G.edgeSet then D.ownerNode ⟨e, he⟩
  else IndexedWeightedTreePartition.Node.globalRoot D.refinedTree

theorem Decomposition.refinedOwner_of_mem (D : Decomposition G X)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    D.refinedOwner e = D.ownerNode ⟨e, he⟩ := by
  simp [Decomposition.refinedOwner, he]

theorem Decomposition.refinedOwner_injOn (D : Decomposition G X) :
    Set.InjOn D.refinedOwner G.edgeSet := by
  intro e he f hf hef
  rw [D.refinedOwner_of_mem he, D.refinedOwner_of_mem hf] at hef
  have hlabels := congrArg IndexedWeightedTreePartition.Node.label hef
  rw [D.ownerNode_label, D.ownerNode_label] at hlabels
  exact congrArg Subtype.val (RefinementLabel.owner.inj hlabels)

/-! ### Connected fibers -/

/-- A label fiber in a rose tree has a distinguished top occurrence, and every
other occurrence in the fiber has a parent in the same fiber. -/
def FiberRooted {A I : Type*} (f : A → I) (i : I) (t : RTree A) : Prop :=
  ∃ r : IndexedWeightedTreePartition.Node t,
    f (IndexedWeightedTreePartition.Node.label r) = i ∧
    ∀ n : IndexedWeightedTreePartition.Node t,
      f (IndexedWeightedTreePartition.Node.label n) = i → n ≠ r →
      ∃ p : IndexedWeightedTreePartition.Node t,
        IndexedWeightedTreePartition.Node.parent n = some p ∧
        f (IndexedWeightedTreePartition.Node.label p) = i

/-- A rooted label fiber induces a connected subgraph of the occurrence tree. -/
theorem FiberRooted.connected {A I : Type*} {f : A → I} {i : I}
    {t : RTree A} (h : FiberRooted f i t) :
    ((IndexedWeightedTreePartition.Node.graph t).induce
      {n : IndexedWeightedTreePartition.Node t |
        f (IndexedWeightedTreePartition.Node.label n) = i}).Connected := by
  obtain ⟨r, hr, hparent⟩ := h
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨r, hr⟩, ?_⟩
  rintro ⟨n, hn⟩
  revert hn
  apply (measure IndexedWeightedTreePartition.Node.depth).wf.induction n
  intro n ih hn
  by_cases hnr : n = r
  · subst n
    exact .rfl
  · obtain ⟨p, hp, hpbase⟩ := hparent n hn hnr
    have hreach := ih p
      (IndexedWeightedTreePartition.Node.depth_parent_lt hp) hpbase
    have hadj :
        ((IndexedWeightedTreePartition.Node.graph t).induce
          {m : IndexedWeightedTreePartition.Node t |
            f (IndexedWeightedTreePartition.Node.label m) = i}).Adj
          ⟨p, hpbase⟩ ⟨n, hn⟩ := by
      exact IndexedWeightedTreePartition.Node.graph_adj_parent hp
    exact hreach.trans hadj.reachable

/-- Every label on a well-hosted spine either is copied from `x` or comes
from an attached child; consequently any property inherited by all child
labels and by `x` is inherited by the whole spine. -/
theorem base_mem_of_mem_vertices_binarySpine (D : Decomposition G X) (x : X)
    {items : List (SpineItem D)} {S : Set X}
    (hx : x ∈ S)
    (howner : ∀ e, SpineItem.owner e ∈ items → D.edgeHost e = x)
    (hchild : ∀ t, SpineItem.child t ∈ items →
      ∀ a ∈ vertices t, RefinementLabel.base D a ∈ S)
    {a : RefinementLabel D} (ha : a ∈ vertices (binarySpine D x items)) :
    RefinementLabel.base D a ∈ S := by
  induction items with
  | nil =>
      simp [binarySpine, vertices] at ha
      subst a
      exact hx
  | cons item items ih =>
      cases item with
      | child t =>
          simp only [binarySpine, vertices, List.map_cons, List.map_nil,
            List.flatten_cons, List.flatten_nil, List.append_nil,
            List.mem_cons, List.mem_append] at ha
          rcases ha with ha | ha
          · subst a
            exact hx
          · rcases ha with ha | ha
            · exact hchild t (by simp) a ha
            · exact ih
                (fun e he ↦ howner e (by simp [he]))
                (fun u hu ↦ hchild u (by simp [hu])) ha
      | owner e =>
          simp only [binarySpine, vertices, List.map_cons, List.map_nil,
            List.flatten_cons, List.flatten_nil, List.append_nil,
            List.mem_cons, List.mem_append] at ha
          rcases ha with ha | ha
          · subst a
            rw [RefinementLabel.base, howner e (by simp)]
            exact hx
          · exact ih
              (fun f hf ↦ howner f (by simp [hf]))
              (fun u hu ↦ hchild u (by simp [hu])) ha

/-- Projection of every label in a refined rose tree is an original label of
the input tree. -/
theorem base_mem_vertices_of_mem_refineTree (D : Decomposition G X)
    (t : RTree X) {a : RefinementLabel D}
    (ha : a ∈ vertices (refineTree D t)) :
    RefinementLabel.base D a ∈ vertices t := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t a with
  | h n ih =>
      cases t with
      | node x children =>
          rw [refineTree] at ha
          apply base_mem_of_mem_vertices_binarySpine D x
            (items :=
              children.map (fun t ↦ SpineItem.child (refineTree D t)) ++
                (hostedEdges D x).map SpineItem.owner)
            (S := {y | y ∈ vertices (.node x children)})
          · simp [vertices]
          · intro e he
            have hehosted : e ∈ hostedEdges D x := by
              simpa using he
            exact (mem_hostedEdges_iff D x e).mp hehosted
          · intro u hu b hb
            have huorig : ∃ child ∈ children, refineTree D child = u := by
              simpa using hu
            obtain ⟨child, hchild, rfl⟩ := huorig
            have hle : RTree.card child ≤
                (children.map RTree.card).sum :=
              le_sum_map_of_mem RTree.card hchild
            have hlt : RTree.card child < n := by
              simp only [RTree.card] at hcard
              omega
            have hbase := ih (RTree.card child) hlt child hb rfl
            simp only [vertices, List.mem_cons]
            right
            rw [List.mem_flatten]
            exact ⟨vertices child,
              List.mem_map.mpr ⟨child, hchild, rfl⟩, hbase⟩
          · exact ha

theorem Decomposition.refinedBase_mem_rootedTree (D : Decomposition G X)
    (n : RefinedNode D) : D.refinedBase n ∈ vertices D.rootedTree := by
  apply base_mem_vertices_of_mem_refineTree D D.rootedTree
  exact IndexedWeightedTreePartition.Node.label_mem_vertices n

/-- A label fiber is absent from a rose tree. -/
def NoFiber {A I : Type*} (f : A → I) (i : I) (t : RTree A) : Prop :=
  ∀ n : IndexedWeightedTreePartition.Node t,
    f (IndexedWeightedTreePartition.Node.label n) ≠ i

/-- The fiber of the global rose-tree root is closed under taking parents. -/
def RootFiber {A I : Type*} (f : A → I) (i : I) (t : RTree A) : Prop :=
  f (IndexedWeightedTreePartition.Node.label
      (IndexedWeightedTreePartition.Node.globalRoot t)) = i ∧
  ∀ n : IndexedWeightedTreePartition.Node t,
    f (IndexedWeightedTreePartition.Node.label n) = i →
    n ≠ IndexedWeightedTreePartition.Node.globalRoot t →
    ∃ p : IndexedWeightedTreePartition.Node t,
      IndexedWeightedTreePartition.Node.parent n = some p ∧
      f (IndexedWeightedTreePartition.Node.label p) = i

theorem RootFiber.fiberRooted {A I : Type*} {f : A → I} {i : I}
    {t : RTree A} (h : RootFiber f i t) : FiberRooted f i t :=
  ⟨IndexedWeightedTreePartition.Node.globalRoot t, h.1, h.2⟩

/-- If `x` does not occur in the original input, it cannot occur as a base
label in its refinement. -/
theorem noFiber_refineTree_of_not_mem (D : Decomposition G X)
    (t : RTree X) (x : X) (hx : x ∉ vertices t) :
    NoFiber (RefinementLabel.base D) x (refineTree D t) := by
  intro n hn
  have hm := base_mem_vertices_of_mem_refineTree D t
    (IndexedWeightedTreePartition.Node.label_mem_vertices n)
  rw [hn] at hm
  exact hx hm

/-- The copied nodes along a well-hosted binary spine form its root fiber,
provided none of the attached child trees contains that base. -/
theorem binarySpine_rootFiber (D : Decomposition G X) (x : X)
    (items : List (SpineItem D))
    (howner : ∀ e, SpineItem.owner e ∈ items → D.edgeHost e = x)
    (hchild : ∀ t, SpineItem.child t ∈ items →
      NoFiber (RefinementLabel.base D) x t) :
    RootFiber (RefinementLabel.base D) x (binarySpine D x items) := by
  induction items with
  | nil =>
      constructor
      · rfl
      · intro n hn hnr
        cases n with
        | root => exact (hnr rfl).elim
        | child i n => exact Fin.elim0 i
  | cons item items ih =>
      have hi := ih
        (fun e he ↦ howner e (by simp [he]))
        (fun t ht ↦ hchild t (by simp [ht]))
      cases item with
      | child t =>
          constructor
          · rfl
          · intro n hn hnr
            cases n with
            | root => exact (hnr rfl).elim
            | child i n =>
                fin_cases i
                · exact (hchild t (by simp) n hn).elim
                · cases hp : IndexedWeightedTreePartition.Node.parent n with
                  | none =>
                      refine ⟨IndexedWeightedTreePartition.Node.globalRoot _, ?_, rfl⟩
                      simp [binarySpine,
                        IndexedWeightedTreePartition.Node.globalRoot,
                        IndexedWeightedTreePartition.Node.parent, hp]
                  | some p =>
                      have hnotroot :
                          n ≠ IndexedWeightedTreePartition.Node.globalRoot
                            (binarySpine D x items) := by
                        intro hroot
                        subst n
                        simp at hp
                      obtain ⟨q, hq, hqbase⟩ := hi.2 n hn hnotroot
                      let j : Fin [t, binarySpine D x items].length :=
                        ⟨1, by simp⟩
                      refine ⟨IndexedWeightedTreePartition.Node.child j q, ?_, hqbase⟩
                      simp [binarySpine,
                        IndexedWeightedTreePartition.Node.globalRoot,
                        IndexedWeightedTreePartition.Node.parent, hq, j]
      | owner e =>
          constructor
          · exact howner e (by simp)
          · intro n hn hnr
            cases n with
            | root => exact (hnr rfl).elim
            | child i n =>
                fin_cases i
                cases hp : IndexedWeightedTreePartition.Node.parent n with
                | none =>
                    refine ⟨IndexedWeightedTreePartition.Node.globalRoot _, ?_, ?_⟩
                    · simp [binarySpine,
                        IndexedWeightedTreePartition.Node.globalRoot,
                        IndexedWeightedTreePartition.Node.parent, hp]
                    · exact howner e (by simp)
                | some p =>
                    have hnotroot :
                        n ≠ IndexedWeightedTreePartition.Node.globalRoot
                          (binarySpine D x items) := by
                      intro hroot
                      subst n
                      simp at hp
                    obtain ⟨q, hq, hqbase⟩ := hi.2 n hn hnotroot
                    let j : Fin [binarySpine D x items].length := ⟨0, by simp⟩
                    refine ⟨IndexedWeightedTreePartition.Node.child j q, ?_, hqbase⟩
                    simp [binarySpine,
                      IndexedWeightedTreePartition.Node.globalRoot,
                      IndexedWeightedTreePartition.Node.parent, hq, j]

/-- An individual spine item has no occurrence over `x`. -/
def SpineItem.NoFiberAt (D : Decomposition G X) (x : X) :
    SpineItem D → Prop
  | .child t => NoFiber (RefinementLabel.base D) x t
  | .owner e => D.edgeHost e ≠ x

/-- If all attachments avoid `x` and the spine itself is based at a different
original node, then the entire binary spine avoids `x`. -/
theorem noFiber_binarySpine (D : Decomposition G X) (a x : X)
    (items : List (SpineItem D)) (hax : a ≠ x)
    (howner : ∀ e, SpineItem.owner e ∈ items → D.edgeHost e = a)
    (hitems : ∀ item ∈ items, item.NoFiberAt D x) :
    NoFiber (RefinementLabel.base D) x (binarySpine D a items) := by
  intro n hn
  have hnot : RefinementLabel.base D
      (IndexedWeightedTreePartition.Node.label n) ≠ x := by
    apply base_mem_of_mem_vertices_binarySpine D a
      (items := items) (S := {y | y ≠ x})
    · exact hax
    · exact howner
    · intro t ht label hlabel
      have hno : NoFiber (RefinementLabel.base D) x t :=
        hitems (SpineItem.child t) ht
      obtain ⟨m, hm⟩ :=
        IndexedWeightedTreePartition.Node.exists_node_of_mem_vertices hlabel
      rw [← hm]
      exact hno m
    · exact IndexedWeightedTreePartition.Node.label_mem_vertices n
  exact hnot hn

/-- Exactly one child attachment supplies a rooted `x`-fiber; every item
before or after it avoids `x`. -/
inductive OneChildFiber (D : Decomposition G X) (x : X) :
    List (SpineItem D) → Prop where
  | here {t : RTree (RefinementLabel D)} {tail : List (SpineItem D)} :
      FiberRooted (RefinementLabel.base D) x t →
      (∀ item ∈ tail, item.NoFiberAt D x) →
      OneChildFiber D x (SpineItem.child t :: tail)
  | skip {item : SpineItem D} {tail : List (SpineItem D)} :
      item.NoFiberAt D x → OneChildFiber D x tail →
      OneChildFiber D x (item :: tail)

/-- A unique rooted child fiber remains rooted after embedding the child at
its position on a different-base spine. -/
theorem OneChildFiber.fiberRooted_binarySpine (D : Decomposition G X)
    {a x : X} {items : List (SpineItem D)}
    (h : OneChildFiber D x items) (hax : a ≠ x)
    (howner : ∀ e, SpineItem.owner e ∈ items → D.edgeHost e = a) :
    FiberRooted (RefinementLabel.base D) x (binarySpine D a items) := by
  induction h with
  | @here t tail ht htail =>
      obtain ⟨r, hr, hrparent⟩ := ht
      let j₀ : Fin [t, binarySpine D a tail].length := ⟨0, by simp⟩
      let r' : IndexedWeightedTreePartition.Node
          (binarySpine D a (SpineItem.child t :: tail)) :=
        IndexedWeightedTreePartition.Node.child j₀ r
      refine ⟨r', hr, ?_⟩
      intro n hn hnr
      cases n with
      | root => exact (hax hn).elim
      | child i n =>
          fin_cases i
          · by_cases hnr' : n = r
            · subst n
              exfalso
              apply hnr
              simp [r', j₀]
            · obtain ⟨p, hp, hpbase⟩ := hrparent n hn hnr'
              refine ⟨IndexedWeightedTreePartition.Node.child j₀ p, ?_, hpbase⟩
              simp [binarySpine, IndexedWeightedTreePartition.Node.parent,
                hp, j₀]
          · have hno : NoFiber (RefinementLabel.base D) x
                (binarySpine D a tail) :=
              noFiber_binarySpine D a x tail hax
                (fun e he ↦ howner e (by simp [he])) htail
            exact (hno n hn).elim
  | @skip item tail hitem htail ih =>
      have hi := ih (fun e he ↦ howner e (by simp [he]))
      obtain ⟨r, hr, hrparent⟩ := hi
      cases item with
      | child t =>
          let j₁ : Fin [t, binarySpine D a tail].length := ⟨1, by simp⟩
          let r' : IndexedWeightedTreePartition.Node
              (binarySpine D a (SpineItem.child t :: tail)) :=
            IndexedWeightedTreePartition.Node.child j₁ r
          refine ⟨r', hr, ?_⟩
          intro n hn hnr
          cases n with
          | root => exact (hax hn).elim
          | child i n =>
              fin_cases i
              · exact (hitem n hn).elim
              · by_cases hnr' : n = r
                · subst n
                  exfalso
                  apply hnr
                  simp [r', j₁]
                · obtain ⟨p, hp, hpbase⟩ := hrparent n hn hnr'
                  refine ⟨IndexedWeightedTreePartition.Node.child j₁ p,
                    ?_, hpbase⟩
                  simp [binarySpine, IndexedWeightedTreePartition.Node.parent,
                    hp, j₁]
      | owner e =>
          let j₀ : Fin [binarySpine D a tail].length := ⟨0, by simp⟩
          let r' : IndexedWeightedTreePartition.Node
              (binarySpine D a (SpineItem.owner e :: tail)) :=
            IndexedWeightedTreePartition.Node.child j₀ r
          refine ⟨r', hr, ?_⟩
          intro n hn hnr
          cases n with
          | root =>
              have hebase := howner e (by simp)
              exact (hax (hebase.symm.trans hn)).elim
          | child i n =>
              fin_cases i
              by_cases hnr' : n = r
              · subst n
                exfalso
                apply hnr
                simp [r', j₀]
              · obtain ⟨p, hp, hpbase⟩ := hrparent n hn hnr'
                refine ⟨IndexedWeightedTreePartition.Node.child j₀ p,
                  ?_, hpbase⟩
                simp [binarySpine, IndexedWeightedTreePartition.Node.parent,
                  hp, j₀]

/-- Every member list of a list with nodup flatten is itself nodup. -/
private theorem nodup_of_mem_of_flatten_nodup {A : Type*}
    {lists : List (List A)} {s : List A} (hs : s ∈ lists)
    (hflat : lists.flatten.Nodup) : s.Nodup := by
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hs
  rw [hsplit, List.flatten_append, List.flatten_cons] at hflat
  exact hflat.of_append_right.of_append_left

/-- From a unique occurrence of `x` among the child traversals, build the
unique-child fiber certificate for the child and owner item list. -/
theorem oneChildFiber_of_mem_flatten (D : Decomposition G X) (a x : X)
    (children : List (RTree X)) (owners : List (GraphEdge G))
    (hax : a ≠ x)
    (howners : ∀ e ∈ owners, D.edgeHost e = a)
    (hflat : (children.map vertices).flatten.Nodup)
    (hx : x ∈ (children.map vertices).flatten)
    (hrooted : ∀ t ∈ children, x ∈ vertices t →
      FiberRooted (RefinementLabel.base D) x (refineTree D t)) :
    OneChildFiber D x
      (children.map (fun t ↦ SpineItem.child (refineTree D t)) ++
        owners.map SpineItem.owner) := by
  induction children with
  | nil => simp at hx
  | cons t children ih =>
      simp only [List.map_cons, List.flatten_cons] at hflat hx
      have hdisjoint : (vertices t).Disjoint
          (children.map vertices).flatten :=
        List.disjoint_of_nodup_append hflat
      rcases (List.mem_append.mp hx) with hxt | hxt
      · apply OneChildFiber.here (hrooted t (by simp) hxt)
        intro item hitem
        cases item with
        | child u =>
            have hu : ∃ child ∈ children, refineTree D child = u := by
              simpa using hitem
            obtain ⟨child, hchild, rfl⟩ := hu
            apply noFiber_refineTree_of_not_mem D child x
            intro hxchild
            have hxtail : x ∈ (children.map vertices).flatten := by
              rw [List.mem_flatten]
              exact ⟨vertices child,
                List.mem_map.mpr ⟨child, hchild, rfl⟩, hxchild⟩
            exact hdisjoint hxt hxtail
        | owner e =>
            have he : e ∈ owners := by simpa using hitem
            exact (howners e he).trans_ne hax
      · apply OneChildFiber.skip
        · apply noFiber_refineTree_of_not_mem D t x
          exact fun hxin ↦ hdisjoint hxin hxt
        · apply ih
          · exact hflat.of_append_right
          · exact hxt
          · intro child hchild hxchild
            exact hrooted child (by simp [hchild]) hxchild

/-- Every original label has a rooted, hence connected, fiber in the refined
occurrence tree. -/
theorem fiberRooted_refineTree (D : Decomposition G X) (t : RTree X)
    (hnodup : (vertices t).Nodup) {x : X} (hx : x ∈ vertices t) :
    FiberRooted (RefinementLabel.base D) x (refineTree D t) := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t x with
  | h n ih =>
      cases t with
      | node a children =>
          simp only [vertices, List.nodup_cons] at hnodup
          rcases hnodup with ⟨ha_not, hflat⟩
          simp only [vertices, List.mem_cons] at hx
          rw [refineTree]
          rcases hx with hx | hx
          · subst x
            apply (binarySpine_rootFiber D a
              (children.map (fun t ↦ SpineItem.child (refineTree D t)) ++
                (hostedEdges D a).map SpineItem.owner) ?_ ?_).fiberRooted
            · intro e he
              have hehosted : e ∈ hostedEdges D a := by simpa using he
              exact (mem_hostedEdges_iff D a e).mp hehosted
            · intro u hu
              have huorig : ∃ child ∈ children, refineTree D child = u := by
                simpa using hu
              obtain ⟨child, hchild, rfl⟩ := huorig
              apply noFiber_refineTree_of_not_mem D child a
              intro hamem
              apply ha_not
              rw [List.mem_flatten]
              exact ⟨vertices child,
                List.mem_map.mpr ⟨child, hchild, rfl⟩, hamem⟩
          · have hax : a ≠ x := by
              intro hax
              subst x
              exact ha_not hx
            have hone : OneChildFiber D x
                (children.map (fun t ↦ SpineItem.child (refineTree D t)) ++
                  (hostedEdges D a).map SpineItem.owner) := by
              apply oneChildFiber_of_mem_flatten D a x children
                (hostedEdges D a) hax
              · intro e he
                exact (mem_hostedEdges_iff D a e).mp he
              · exact hflat
              · exact hx
              · intro child hchild hxchild
                have hle : RTree.card child ≤
                    (children.map RTree.card).sum :=
                  le_sum_map_of_mem RTree.card hchild
                have hlt : RTree.card child < n := by
                  simp only [RTree.card] at hcard
                  omega
                have hchildNodup : (vertices child).Nodup :=
                  nodup_of_mem_of_flatten_nodup
                    (List.mem_map.mpr ⟨child, hchild, rfl⟩) hflat
                exact ih (RTree.card child) hlt child hchildNodup hxchild rfl
            apply hone.fiberRooted_binarySpine D hax
            intro e he
            have hehosted : e ∈ hostedEdges D a := by simpa using he
            exact (mem_hostedEdges_iff D a e).mp hehosted

theorem Decomposition.refinedFiber_connected (D : Decomposition G X)
    (x : X) :
    (D.refinedGraph.induce {n : RefinedNode D | D.refinedBase n = x}).Connected := by
  apply FiberRooted.connected
  apply fiberRooted_refineTree D D.rootedTree
  · exact vertices_labeledTree_nodup D.isTree D.root D.root
  · exact mem_vertices_labeledTree_root D.isTree D.root x

/-! ### Original-edge realization by the rooted encoding -/

theorem node_label_globalRoot_eq_rootLabel {A : Type*} (t : RTree A) :
    IndexedWeightedTreePartition.Node.label
      (IndexedWeightedTreePartition.Node.globalRoot t) = rootLabel t := by
  cases t
  rfl

/-- A structural parent edge in a rose tree respecting `Q` maps to an edge of
`Q` between the two occurrence labels. -/
theorem adj_labels_of_parent_of_respects {A : Type*} {Q : SimpleGraph A}
    {t : RTree A} (h : IndexedWeightedTreePartition.Respects Q t)
    {n p : IndexedWeightedTreePartition.Node t}
    (hp : IndexedWeightedTreePartition.Node.parent n = some p) :
    Q.Adj (IndexedWeightedTreePartition.Node.label p)
      (IndexedWeightedTreePartition.Node.label n) := by
  induction n with
  | root => simp [IndexedWeightedTreePartition.Node.parent] at hp
  | @child label children i n ih =>
      rw [IndexedWeightedTreePartition.Respects] at h
      simp only [IndexedWeightedTreePartition.Node.parent] at hp
      split at hp
      · rename_i hnone
        have hn : n = IndexedWeightedTreePartition.Node.globalRoot
            (children.get i) :=
          (IndexedWeightedTreePartition.Node.parent_eq_none_iff_root n).mp hnone
        subst n
        cases hp
        have hadj := h.1 (children.get i) (children.get_mem i)
        change Q.Adj label (IndexedWeightedTreePartition.Node.label
          (IndexedWeightedTreePartition.Node.globalRoot (children.get i)))
        rw [node_label_globalRoot_eq_rootLabel]
        exact hadj
      · rename_i p' hsome
        cases hp
        exact ih (h.2 (children.get i) (children.get_mem i)) hsome

/-- Every structural occurrence edge in a rose tree respecting `Q` maps to a
`Q`-edge between its labels. -/
theorem adj_labels_of_respects {A : Type*} {Q : SimpleGraph A}
    {t : RTree A} (h : IndexedWeightedTreePartition.Respects Q t)
    {a b : IndexedWeightedTreePartition.Node t}
    (hab : (IndexedWeightedTreePartition.Node.graph t).Adj a b) :
    Q.Adj (IndexedWeightedTreePartition.Node.label a)
      (IndexedWeightedTreePartition.Node.label b) := by
  rw [IndexedWeightedTreePartition.Node.graph,
    SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with hp | hp
  · exact adj_labels_of_parent_of_respects h hp
  · exact (adj_labels_of_parent_of_respects h hp).symm

/-- Occurrences of the rooted original tree are canonically equivalent to its
original vertex labels. -/
def Decomposition.rootedLabelEquiv (D : Decomposition G X) :
    IndexedWeightedTreePartition.Node D.rootedTree ≃ X :=
  Equiv.ofBijective IndexedWeightedTreePartition.Node.label ⟨
    IndexedWeightedTreePartition.Node.label_injective_of_vertices_nodup
      (vertices_labeledTree_nodup D.isTree D.root D.root),
    fun x ↦ IndexedWeightedTreePartition.Node.exists_node_of_mem_vertices
      (mem_vertices_labeledTree_root D.isTree D.root x)⟩

@[simp]
theorem Decomposition.rootedLabelEquiv_apply (D : Decomposition G X)
    (n : IndexedWeightedTreePartition.Node D.rootedTree) :
    D.rootedLabelEquiv n = IndexedWeightedTreePartition.Node.label n := rfl

/-- The occurrence graph of the rooted encoding, transported back to `X`. -/
def Decomposition.rootedEncodedGraph (D : Decomposition G X) : SimpleGraph X :=
  (IndexedWeightedTreePartition.Node.graph D.rootedTree).map
    D.rootedLabelEquiv.toEmbedding

/-- The label-preserving rooted encoding recovers exactly the original tree. -/
theorem Decomposition.rootedEncodedGraph_eq (D : Decomposition G X) :
    D.rootedEncodedGraph = D.tree := by
  have hle : D.rootedEncodedGraph ≤ D.tree := by
    rintro u v ⟨a, b, hab, ha, hb⟩
    subst u
    subst v
    simpa using adj_labels_of_respects
      (IndexedWeightedTreePartition.labeledTree_respects
        D.isTree D.root D.root) hab
  have hconn : D.rootedEncodedGraph.Connected := by
    exact ((SimpleGraph.Iso.map D.rootedLabelEquiv
      (IndexedWeightedTreePartition.Node.graph D.rootedTree)).connected_iff).mp
        (IndexedWeightedTreePartition.Node.graph_connected D.rootedTree)
  have hmin : Minimal SimpleGraph.Connected D.tree :=
    SimpleGraph.isTree_iff_minimal_connected.mp D.isTree
  exact le_antisymm hle (hmin.2 hconn hle)

/-- Every original tree edge is represented by an occurrence edge carrying
the same endpoint labels. -/
theorem Decomposition.exists_rooted_adj_of_adj (D : Decomposition G X)
    {x y : X} (hxy : D.tree.Adj x y) :
    ∃ a b : IndexedWeightedTreePartition.Node D.rootedTree,
      IndexedWeightedTreePartition.Node.label a = x ∧
      IndexedWeightedTreePartition.Node.label b = y ∧
      (IndexedWeightedTreePartition.Node.graph D.rootedTree).Adj a b := by
  have henc : D.rootedEncodedGraph.Adj x y := by
    rw [D.rootedEncodedGraph_eq]
    exact hxy
  rcases henc with ⟨a, b, hab, ha, hb⟩
  exact ⟨a, b, ha, hb, hab⟩

/-! ### Lifting structural edges through the binary-spine refinement -/

/-- The root occurrence of a well-hosted spine copies the spine's original
node, regardless of whether its first item is a child or an owner. -/
theorem base_globalRoot_binarySpine (D : Decomposition G X) (x : X)
    (items : List (SpineItem D))
    (howner : ∀ e, SpineItem.owner e ∈ items → D.edgeHost e = x) :
    RefinementLabel.base D (IndexedWeightedTreePartition.Node.label
      (IndexedWeightedTreePartition.Node.globalRoot (binarySpine D x items))) = x := by
  cases items with
  | nil => rfl
  | cons item items =>
      cases item with
      | child t => rfl
      | owner e => exact howner e (by simp)

theorem base_globalRoot_refineTree (D : Decomposition G X) (t : RTree X) :
    RefinementLabel.base D (IndexedWeightedTreePartition.Node.label
      (IndexedWeightedTreePartition.Node.globalRoot (refineTree D t))) =
      rootLabel t := by
  cases t with
  | node x children =>
      rw [refineTree]
      apply base_globalRoot_binarySpine
      intro e he
      have hehosted : e ∈ hostedEdges D x := by simpa using he
      exact (mem_hostedEdges_iff D x e).mp hehosted

/-- A child item is attached by one structural edge from an `x`-based spine
node to the root occurrence of that child. -/
theorem binarySpine_child_attached (D : Decomposition G X) (x : X)
    {items : List (SpineItem D)} {t : RTree (RefinementLabel D)}
    (ht : SpineItem.child t ∈ items) :
    ∃ p q : IndexedWeightedTreePartition.Node (binarySpine D x items),
      RefinementLabel.base D (IndexedWeightedTreePartition.Node.label p) = x ∧
      IndexedWeightedTreePartition.Node.label q = rootLabel t ∧
      (IndexedWeightedTreePartition.Node.graph (binarySpine D x items)).Adj p q := by
  induction items with
  | nil => simp at ht
  | cons item items ih =>
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · cases item with
        | child u =>
            have htu := SpineItem.child.inj ht
            subst u
            let j₀ : Fin [t, binarySpine D x items].length := ⟨0, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.globalRoot _,
              IndexedWeightedTreePartition.Node.childEmbedding j₀
                (IndexedWeightedTreePartition.Node.globalRoot t), rfl, ?_, ?_⟩
            · exact node_label_globalRoot_eq_rootLabel t
            · apply (IndexedWeightedTreePartition.Node.graph_adj_root_child_iff
                j₀ _).mpr
              rfl
        | owner e => exact SpineItem.noConfusion ht
      · obtain ⟨p, q, hp, hq, hpq⟩ := ih ht
        cases item with
        | child u =>
            let j₁ : Fin [u, binarySpine D x items].length := ⟨1, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.childEmbedding j₁ p,
              IndexedWeightedTreePartition.Node.childEmbedding j₁ q,
              hp, hq, ?_⟩
            exact (IndexedWeightedTreePartition.Node.graph_adj_childEmbedding_iff
              j₁ p q).mpr hpq
        | owner e =>
            let j₀ : Fin [binarySpine D x items].length := ⟨0, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.childEmbedding j₀ p,
              IndexedWeightedTreePartition.Node.childEmbedding j₀ q,
              hp, hq, ?_⟩
            exact (IndexedWeightedTreePartition.Node.graph_adj_childEmbedding_iff
              j₀ p q).mpr hpq

/-- Internal adjacency in an attached child tree remains adjacency in the
surrounding binary spine. -/
theorem binarySpine_embed_child_adj (D : Decomposition G X) (x : X)
    {items : List (SpineItem D)} {t : RTree (RefinementLabel D)}
    (ht : SpineItem.child t ∈ items)
    {a b : IndexedWeightedTreePartition.Node t}
    (hab : (IndexedWeightedTreePartition.Node.graph t).Adj a b) :
    ∃ a' b' : IndexedWeightedTreePartition.Node (binarySpine D x items),
      IndexedWeightedTreePartition.Node.label a' =
        IndexedWeightedTreePartition.Node.label a ∧
      IndexedWeightedTreePartition.Node.label b' =
        IndexedWeightedTreePartition.Node.label b ∧
      (IndexedWeightedTreePartition.Node.graph (binarySpine D x items)).Adj a' b' := by
  induction items with
  | nil => simp at ht
  | cons item items ih =>
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · cases item with
        | child u =>
            have htu := SpineItem.child.inj ht
            subst u
            let j₀ : Fin [t, binarySpine D x items].length := ⟨0, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.childEmbedding j₀ a,
              IndexedWeightedTreePartition.Node.childEmbedding j₀ b,
              rfl, rfl, ?_⟩
            exact (IndexedWeightedTreePartition.Node.graph_adj_childEmbedding_iff
              j₀ a b).mpr hab
        | owner e => exact SpineItem.noConfusion ht
      · obtain ⟨a', b', ha, hb, hab'⟩ := ih ht
        cases item with
        | child u =>
            let j₁ : Fin [u, binarySpine D x items].length := ⟨1, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.childEmbedding j₁ a',
              IndexedWeightedTreePartition.Node.childEmbedding j₁ b',
              ha, hb, ?_⟩
            exact (IndexedWeightedTreePartition.Node.graph_adj_childEmbedding_iff
              j₁ a' b').mpr hab'
        | owner e =>
            let j₀ : Fin [binarySpine D x items].length := ⟨0, by simp⟩
            refine ⟨IndexedWeightedTreePartition.Node.childEmbedding j₀ a',
              IndexedWeightedTreePartition.Node.childEmbedding j₀ b',
              ha, hb, ?_⟩
            exact (IndexedWeightedTreePartition.Node.graph_adj_childEmbedding_iff
              j₀ a' b').mpr hab'

/-- Every parent edge of the original rose tree has an edge lift in the
binary-spine refinement, with the same projected endpoint labels. -/
theorem refineTree_lifts_parent (D : Decomposition G X) {t : RTree X}
    {n p : IndexedWeightedTreePartition.Node t}
    (hp : IndexedWeightedTreePartition.Node.parent n = some p) :
    ∃ a b : IndexedWeightedTreePartition.Node (refineTree D t),
      RefinementLabel.base D (IndexedWeightedTreePartition.Node.label a) =
        IndexedWeightedTreePartition.Node.label p ∧
      RefinementLabel.base D (IndexedWeightedTreePartition.Node.label b) =
        IndexedWeightedTreePartition.Node.label n ∧
      (IndexedWeightedTreePartition.Node.graph (refineTree D t)).Adj a b := by
  induction n with
  | root => simp [IndexedWeightedTreePartition.Node.parent] at hp
  | @child x children i n ih =>
      let items : List (SpineItem D) :=
        children.map (fun child ↦ SpineItem.child (refineTree D child)) ++
          (hostedEdges D x).map SpineItem.owner
      have hitem : SpineItem.child (refineTree D (children.get i)) ∈ items := by
        change SpineItem.child (refineTree D (children.get i)) ∈
          children.map (fun child ↦ SpineItem.child (refineTree D child)) ++
            (hostedEdges D x).map SpineItem.owner
        rw [List.mem_append]
        exact Or.inl (List.mem_map.mpr
          ⟨children.get i, children.get_mem i, rfl⟩)
      rw [refineTree]
      change ∃ a b : IndexedWeightedTreePartition.Node (binarySpine D x items),
        RefinementLabel.base D (IndexedWeightedTreePartition.Node.label a) =
          IndexedWeightedTreePartition.Node.label p ∧
        RefinementLabel.base D (IndexedWeightedTreePartition.Node.label b) =
          IndexedWeightedTreePartition.Node.label
            (IndexedWeightedTreePartition.Node.child i n) ∧
        (IndexedWeightedTreePartition.Node.graph (binarySpine D x items)).Adj a b
      cases hnparent : IndexedWeightedTreePartition.Node.parent n with
      | none =>
          have hnroot : n = IndexedWeightedTreePartition.Node.globalRoot
              (children.get i) :=
            (IndexedWeightedTreePartition.Node.parent_eq_none_iff_root n).mp hnparent
          subst n
          have hproot : p = IndexedWeightedTreePartition.Node.globalRoot
              (.node x children) := by
            have hrootParent :
                IndexedWeightedTreePartition.Node.parent
                  (IndexedWeightedTreePartition.Node.child i
                    (IndexedWeightedTreePartition.Node.globalRoot (children.get i))) =
                  some (IndexedWeightedTreePartition.Node.globalRoot (.node x children)) :=
              (IndexedWeightedTreePartition.Node.parent_child_eq_root_iff i _).mpr rfl
            rw [hrootParent] at hp
            exact Option.some.inj hp.symm
          subst p
          obtain ⟨a, b, ha, hb, hab⟩ :=
            binarySpine_child_attached D x hitem
          refine ⟨a, b, ?_, ?_, hab⟩
          · exact ha
          · rw [hb, ← node_label_globalRoot_eq_rootLabel
              (refineTree D (children.get i))]
            simpa using (base_globalRoot_refineTree D (children.get i)).trans
              (node_label_globalRoot_eq_rootLabel (children.get i)).symm
      | some q =>
          have hpchild : p =
              (IndexedWeightedTreePartition.Node.child i q :
                IndexedWeightedTreePartition.Node (.node x children)) := by
            have hchildParent :
                IndexedWeightedTreePartition.Node.parent
                  (IndexedWeightedTreePartition.Node.child i n :
                    IndexedWeightedTreePartition.Node (.node x children)) =
                  some (IndexedWeightedTreePartition.Node.child i q :
                    IndexedWeightedTreePartition.Node (.node x children)) :=
              (IndexedWeightedTreePartition.Node.parent_child_eq_child_iff i q n).mpr
                hnparent
            rw [hchildParent] at hp
            exact Option.some.inj hp.symm
          subst p
          obtain ⟨a, b, ha, hb, hab⟩ := ih hnparent
          obtain ⟨a', b', ha', hb', hab'⟩ :=
            binarySpine_embed_child_adj D x hitem hab
          refine ⟨a', b', ?_, ?_, hab'⟩
          · rw [ha']
            exact ha
          · rw [hb']
            exact hb

/-- Every structural edge of the original rose tree has an edge lift in its
refinement. -/
theorem refineTree_lifts_adj (D : Decomposition G X) {t : RTree X}
    {u v : IndexedWeightedTreePartition.Node t}
    (huv : (IndexedWeightedTreePartition.Node.graph t).Adj u v) :
    ∃ a b : IndexedWeightedTreePartition.Node (refineTree D t),
      RefinementLabel.base D (IndexedWeightedTreePartition.Node.label a) =
        IndexedWeightedTreePartition.Node.label u ∧
      RefinementLabel.base D (IndexedWeightedTreePartition.Node.label b) =
        IndexedWeightedTreePartition.Node.label v ∧
      (IndexedWeightedTreePartition.Node.graph (refineTree D t)).Adj a b := by
  rw [IndexedWeightedTreePartition.Node.graph,
    SimpleGraph.fromRel_adj] at huv
  rcases huv.2 with hp | hp
  · exact refineTree_lifts_parent D hp
  · obtain ⟨b, a, hb, ha, hba⟩ := refineTree_lifts_parent D hp
    exact ⟨a, b, ha, hb, hba.symm⟩

/-- Every original decomposition-tree edge has an edge lift between the two
corresponding refined fibers. -/
theorem Decomposition.refined_lifts_adj (D : Decomposition G X)
    {x y : X} (hxy : D.tree.Adj x y) :
    ∃ a b : RefinedNode D,
      D.refinedBase a = x ∧ D.refinedBase b = y ∧
      D.refinedGraph.Adj a b := by
  obtain ⟨u, v, hu, hv, huv⟩ := D.exists_rooted_adj_of_adj hxy
  obtain ⟨a, b, ha, hb, hab⟩ := refineTree_lifts_adj D huv
  exact ⟨a, b, ha.trans hu, hb.trans hv, hab⟩

/-- Copying original bags along the connected fibers preserves the running
intersection property. -/
theorem Decomposition.refined_running_intersection (D : Decomposition G X)
    (v : V) :
    (D.refinedGraph.induce
      {n : RefinedNode D | v ∈ D.bag (D.refinedBase n)}).Connected := by
  simpa using connected_induce_preimage_of_connected_fibers D.refinedBase
    D.refinedFiber_connected
    (fun _ _ hxy ↦ D.refined_lifts_adj hxy)
    (D.running_intersection v)

/-- The concrete refined tree decomposition, obtained by copying the bag of
the projected original node. -/
def Decomposition.edgeOwnedDecomposition (D : Decomposition G X) :
    Decomposition G (RefinedNode D) where
  tree := D.refinedGraph
  bag n := D.bag (D.refinedBase n)
  isTree := D.refinedGraph_isTree
  vertex_mem v := by
    obtain ⟨x, hx⟩ := D.vertex_mem v
    obtain ⟨⟨n, hn⟩⟩ := (D.refinedFiber_connected x).nonempty
    refine ⟨n, ?_⟩
    change D.refinedBase n = x at hn
    rw [hn]
    exact hx
  edge_mem := by
    intro u v huv
    obtain ⟨x, hu, hv⟩ := D.edge_mem huv
    obtain ⟨⟨n, hn⟩⟩ := (D.refinedFiber_connected x).nonempty
    change D.refinedBase n = x at hn
    refine ⟨n, ?_, ?_⟩ <;> rw [hn]
    · exact hu
    · exact hv
  running_intersection := D.refined_running_intersection

theorem Decomposition.edgeOwnedDecomposition_widthAtMost
    (D : Decomposition G X) {k : ℕ} (hD : D.WidthAtMost k) :
    D.edgeOwnedDecomposition.WidthAtMost k := by
  intro n
  exact hD (D.refinedBase n)

theorem Decomposition.refinedOwner_hosts (D : Decomposition G X)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (v : V) (hv : v ∈ e.toFinset) :
    v ∈ D.edgeOwnedDecomposition.bag (D.refinedOwner e) := by
  rw [D.refinedOwner_of_mem he]
  change v ∈ D.bag (D.refinedBase (D.ownerNode ⟨e, he⟩))
  rw [D.ownerNode_base]
  exact D.mem_bag_edgeHost ⟨e, he⟩ hv

/-- Concrete witness for paper Lemma 5.3 attached to any finite tree
decomposition. -/
def Decomposition.edgeOwnedRefinementWitness (D : Decomposition G X) :
    EdgeOwnedRefinementWitness G (RefinedNode D) where
  decomposition := D.edgeOwnedDecomposition
  owner := D.refinedOwner
  owner_inj := D.refinedOwner_injOn
  owner_hosts := by
    intro e he v hv
    exact D.refinedOwner_hosts he v hv
  subcubic := D.refinedGraph_subcubic

/-- **Paper Lemma 5.3, explicit-decomposition form.**  Every width-`k` tree
decomposition has a finite, edge-owned, subcubic refinement of the same
width. -/
theorem exists_edgeOwnedRefinement_of_decomposition
    (D : Decomposition G X) {k : ℕ} (hD : D.WidthAtMost k) :
    ∃ (Y : Type (max u_1 u_2)) (_inst : Fintype Y)
      (R : EdgeOwnedRefinementWitness G Y),
      R.decomposition.WidthAtMost k := by
  exact ⟨RefinedNode D, inferInstance, D.edgeOwnedRefinementWitness,
    D.edgeOwnedDecomposition_widthAtMost hD⟩

/-- **Paper Lemma 5.3, treewidth form.**  If `G` has treewidth at most `k`,
then it has a width-`k` tree decomposition on a finite subcubic tree together
with an injective assignment of graph edges to bags containing their
endpoints.  The paper assumes `G` connected, but the refinement argument does
not need that hypothesis. -/
theorem exists_edgeOwnedRefinement_of_hasTreewidthAtMost {k : ℕ}
    (hG : HasTreewidthAtMost G k) :
    ∃ (Y : Type u_1) (_inst : Fintype Y)
      (R : EdgeOwnedRefinementWitness G Y),
      R.decomposition.WidthAtMost k := by
  obtain ⟨t, D, hD⟩ := hG
  exact exists_edgeOwnedRefinement_of_decomposition D hD

/-- Numerical-treewidth formulation of paper Lemma 5.3. -/
theorem exists_edgeOwnedRefinement_of_treewidth_le {k : ℕ}
    (hG : treewidth G ≤ k) :
    ∃ (Y : Type u_1) (_inst : Fintype Y)
      (R : EdgeOwnedRefinementWitness G Y),
      R.decomposition.WidthAtMost k :=
  exists_edgeOwnedRefinement_of_hasTreewidthAtMost
    (treewidth_le_iff.mp hG)

end
end TreeDecomposition
end LowDegree
