import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Tree decompositions and low-overlap edge divisions

This file formalizes the finite combinatorial vocabulary used in Section 5 of
the paper.  In particular, an edge piece is an arbitrary (possibly
disconnected) simple graph.  Its vertices are its incident vertices, represented
by `SimpleGraph.support`; ambient isolated vertices are never counted.

The paper constructs an edge-owned subcubic refinement and then partitions its
decomposition tree into connected clusters.  We record both constructions as
honest witness structures.  The unconditional results below are the exact
edge-partition and overlap-counting facts, together with the general interface
charging argument.  No existence theorem for the refinement or clustering is
asserted in this file.
-/

namespace LowDegree

open scoped BigOperators

namespace TreeDecomposition

variable {V X : Type*}

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

/-- A finite tree decomposition in the sense used by the paper.  The nodes
whose bags contain a fixed graph vertex induce a connected subtree. -/
structure Decomposition (G : SimpleGraph V) (X : Type*) [Fintype X] where
  tree : SimpleGraph X
  bag : X → Finset V
  isTree : tree.IsTree
  vertex_mem : ∀ v : V, ∃ x : X, v ∈ bag x
  edge_mem : ∀ ⦃u v : V⦄, G.Adj u v → ∃ x : X, u ∈ bag x ∧ v ∈ bag x
  running_intersection :
    ∀ v : V, (tree.induce {x : X | v ∈ bag x}).Connected

namespace Decomposition

variable {G : SimpleGraph V} [Fintype X] (D : Decomposition G X)

/-- Width of a particular decomposition: the largest bag cardinality minus
one, exactly as in paper Definition 5.2.  `Finset.sup` returns zero on an
empty node type, although `D.isTree` in fact guarantees a nonempty tree. -/
noncomputable def width : ℕ :=
  (Finset.univ.sup fun x : X ↦ (D.bag x).card) - 1

/-- The decomposition has width at most `k`, expressed without a subtraction:
every bag has at most `k+1` vertices. -/
def WidthAtMost (k : ℕ) : Prop := ∀ x : X, (D.bag x).card ≤ k + 1

/-- The subtraction-free predicate agrees with the paper's numerical width. -/
theorem width_le_iff {k : ℕ} : D.width ≤ k ↔ D.WidthAtMost k := by
  classical
  let M : ℕ := Finset.univ.sup fun x : X ↦ (D.bag x).card
  have hbag_le (x : X) : (D.bag x).card ≤ M := by
    exact Finset.le_sup (s := Finset.univ) (f := fun y : X ↦ (D.bag y).card)
      (Finset.mem_univ x)
  constructor
  · intro h x
    change M - 1 ≤ k at h
    have hx := hbag_le x
    omega
  · intro h
    change M - 1 ≤ k
    have hM : M ≤ k + 1 := by
      apply Finset.sup_le
      intro x hx
      exact h x
    omega

end Decomposition

/-- The graph has treewidth at most `k` when it admits a finite tree
decomposition all of whose bags have size at most `k+1`.  Using `Fin t` as the
node type loses no finite decompositions and keeps the existential first-order. -/
def HasTreewidthAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ t : ℕ, ∃ D : Decomposition G (Fin t), D.WidthAtMost k

/-- Treewidth-at-most is monotone under taking spanning subgraphs.  This is
the graph-theoretic reduction used before Proposition 5.1 in the paper: every
Fourier support occurring inside a width-`k` plant also has treewidth at most
`k`. -/
theorem treewidth_mono_subgraph {G H : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (hG : HasTreewidthAtMost G k) :
    HasTreewidthAtMost H k := by
  rcases hG with ⟨t, D, hwidth⟩
  let D' : Decomposition H (Fin t) :=
    { tree := D.tree
      bag := D.bag
      isTree := D.isTree
      vertex_mem := D.vertex_mem
      edge_mem := fun {_ _} huv ↦ D.edge_mem (hHG huv)
      running_intersection := D.running_intersection }
  exact ⟨t, D', hwidth⟩

/-- Increasing the numerical width bound preserves a tree decomposition. -/
theorem hasTreewidthAtMost_mono {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hG : HasTreewidthAtMost G k) :
    HasTreewidthAtMost G l := by
  rcases hG with ⟨t, D, hwidth⟩
  exact ⟨t, D, fun x ↦ le_trans (hwidth x) (Nat.add_le_add_right hkl 1)⟩

/-- A graph of treewidth at most zero has no edges.  This isolates the only
case in which the revised product scale `tw(G) log n = o(Dₙ)` does not itself
imply the old `(tw(G)+1) log n = o(Dₙ)` scale. -/
theorem eq_bot_of_hasTreewidthAtMost_zero {G : SimpleGraph V}
    (hG : HasTreewidthAtMost G 0) : G = ⊥ := by
  classical
  rcases hG with ⟨t, D, hwidth⟩
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro huv
  rcases D.edge_mem huv with ⟨x, hux, hvx⟩
  have hsubset : ({u, v} : Finset V) ⊆ D.bag x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hux
    · exact hvx
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_pair (G.ne_of_adj huv)] at hcard
  have hx := hwidth x
  omega

/-- Every finite graph has a one-bag tree decomposition.  The deliberately
loose bound `|V|` is enough to make the minimum defining `treewidth` total,
including for empty vertex types. -/
theorem hasTreewidthAtMost_card [Fintype V] (G : SimpleGraph V) :
    HasTreewidthAtMost G (Fintype.card V) := by
  classical
  let D : Decomposition G (Fin 1) :=
    { tree := ⊥
      bag := fun _ ↦ Finset.univ
      isTree := by
        constructor
        · rw [SimpleGraph.connected_bot_iff]
          exact ⟨inferInstance, inferInstance⟩
        · exact SimpleGraph.isAcyclic_bot
      vertex_mem := fun v ↦ ⟨0, by simp⟩
      edge_mem := fun {_ _} _ ↦ ⟨0, by simp⟩
      running_intersection := by
        intro v
        have hset : {x : Fin 1 | v ∈ (Finset.univ : Finset V)} = Set.univ := by
          ext x
          simp
        rw [hset]
        apply (SimpleGraph.induceUnivIso (⊥ : SimpleGraph (Fin 1))).connected_iff.mpr
        rw [SimpleGraph.connected_bot_iff]
        exact ⟨inferInstance, inferInstance⟩ }
  refine ⟨1, D, ?_⟩
  intro x
  simp [D]

/-- **Paper Definition 5.2.**  The treewidth of a finite simple graph is the
least `k` for which it has a tree decomposition with bags of size at most
`k+1`.  The same definition works for connected and disconnected graphs. -/
noncomputable def treewidth [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find ⟨Fintype.card V, hasTreewidthAtMost_card G⟩

/-- A graph admits a decomposition at its treewidth. -/
theorem hasTreewidthAtMost_treewidth [Fintype V] (G : SimpleGraph V) :
    HasTreewidthAtMost G (treewidth G) :=
  Nat.find_spec ⟨Fintype.card V, hasTreewidthAtMost_card G⟩

/-- Minimality of `treewidth`. -/
theorem treewidth_le_of_hasTreewidthAtMost [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hG : HasTreewidthAtMost G k) :
    treewidth G ≤ k :=
  Nat.find_min' ⟨Fintype.card V, hasTreewidthAtMost_card G⟩ hG

/-- Characterization of the numerical treewidth by an explicit width bound. -/
theorem treewidth_le_iff [Fintype V] {G : SimpleGraph V} {k : ℕ} :
    treewidth G ≤ k ↔ HasTreewidthAtMost G k := by
  constructor
  · intro h
    exact hasTreewidthAtMost_mono h (hasTreewidthAtMost_treewidth G)
  · exact treewidth_le_of_hasTreewidthAtMost

/-- Numerical treewidth is monotone under spanning subgraphs. -/
theorem treewidth_mono [Fintype V] {G H : SimpleGraph V} (hHG : H ≤ G) :
    treewidth H ≤ treewidth G :=
  treewidth_le_of_hasTreewidthAtMost
    (treewidth_mono_subgraph hHG (hasTreewidthAtMost_treewidth G))

/-- A faithful ordered edge decomposition.  The pieces need not be connected.
They are nonempty, lie below `G`, are pairwise edge-disjoint, and cover every
edge of `G`. -/
structure OrderedEdgeDecomposition (G : SimpleGraph V) (m : ℕ) where
  piece : Fin m → SimpleGraph V
  piece_nonempty : ∀ i, piece i ≠ ⊥
  piece_le : ∀ i, piece i ≤ G
  edge_disjoint : Set.Pairwise (Set.univ : Set (Fin m)) fun i j ↦
    Disjoint (piece i) (piece j)
  cover : (⨆ i, piece i) = G

namespace OrderedEdgeDecomposition

variable {G : SimpleGraph V} {m : ℕ} (P : OrderedEdgeDecomposition G m)

/-- The incident vertices of a piece. -/
noncomputable def vertexFinset [Fintype V] (i : Fin m) : Finset V :=
  (P.piece i).support.toFinset

/-- The incident vertices of the graph being decomposed. -/
noncomputable def graphVertexFinset [Fintype V]
    (_P : OrderedEdgeDecomposition G m) : Finset V :=
  G.support.toFinset

/-- Number of pieces incident to `v`. -/
noncomputable def vertexMultiplicity [Fintype V] (v : V) : ℕ :=
  (Finset.univ.filter fun i ↦ v ∈ P.vertexFinset i).card

/-- The paper's vertex-overlap count
`sum_i v(T_i) - v(G)`. -/
noncomputable def overlap [Fintype V] : ℕ :=
  (∑ i, (P.vertexFinset i).card) - P.graphVertexFinset.card

/-- Membership in a piece's incident-vertex set is ordinary graph support
membership. -/
theorem mem_vertexFinset [Fintype V] (i : Fin m) (v : V) :
    v ∈ P.vertexFinset i ↔ v ∈ (P.piece i).support := by
  classical
  simp [vertexFinset]

/-- Edge membership is recovered from membership in one of the pieces. -/
theorem mem_edgeSet_iff (e : Sym2 V) :
    e ∈ G.edgeSet ↔ ∃ i : Fin m, e ∈ (P.piece i).edgeSet := by
  have hcover : (⨆ i, P.piece i).edgeSet = G.edgeSet :=
    congrArg SimpleGraph.edgeSet P.cover
  rw [← hcover]
  induction e using Sym2.inductionOn with
  | _ u v => exact SimpleGraph.iSup_adj

/-- An edge has a unique piece index. -/
theorem edge_index_unique {e : Sym2 V} {i j : Fin m}
    (hi : e ∈ (P.piece i).edgeSet) (hj : e ∈ (P.piece j).edgeSet) : i = j := by
  by_contra hij
  have hd : Disjoint (P.piece i).edgeSet (P.piece j).edgeSet :=
    SimpleGraph.disjoint_edgeSet.mpr
      (P.edge_disjoint (Set.mem_univ i) (Set.mem_univ j) hij)
  exact Set.disjoint_left.1 hd hi hj

/-- The finite edge set of `G` is the disjoint union of the piece edge sets. -/
theorem edgeFinset_eq_biUnion [Fintype V] :
    G.edgeFinset = Finset.univ.biUnion fun i ↦ (P.piece i).edgeFinset := by
  classical
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact P.mem_edgeSet_iff e

/-- Cardinality of an ordered edge partition. -/
theorem card_edges_eq_sum [Fintype V] :
    G.edgeFinset.card = ∑ i, (P.piece i).edgeFinset.card := by
  classical
  rw [P.edgeFinset_eq_biUnion]
  apply Finset.card_biUnion
  intro i _ j _ hij
  simpa [SimpleGraph.disjoint_edgeFinset] using
    P.edge_disjoint (Set.mem_univ i) (Set.mem_univ j) hij

/-- Every incident vertex of a piece is incident to an edge of `G`. -/
theorem vertexFinset_subset_graphVertexFinset [Fintype V] (i : Fin m) :
    P.vertexFinset i ⊆ P.graphVertexFinset := by
  classical
  intro v hv
  rw [P.mem_vertexFinset] at hv
  change v ∈ G.support.toFinset
  simp only [Set.mem_toFinset]
  exact SimpleGraph.support_mono (P.piece_le i) hv

/-- The incident vertices of `G` are exactly the union of the incident
vertices of the pieces. -/
theorem mem_graphVertexFinset_iff [Fintype V] (v : V) :
    v ∈ P.graphVertexFinset ↔ ∃ i : Fin m, v ∈ P.vertexFinset i := by
  classical
  simp only [graphVertexFinset, Set.mem_toFinset, SimpleGraph.mem_support,
    P.mem_vertexFinset]
  constructor
  · rintro ⟨w, hvw⟩
    rw [← P.cover, SimpleGraph.iSup_adj] at hvw
    obtain ⟨i, hi⟩ := hvw
    exact ⟨i, w, hi⟩
  · rintro ⟨i, w, hi⟩
    exact ⟨w, P.piece_le i hi⟩

/-- A graph-support vertex occurs in at least one piece. -/
theorem one_le_vertexMultiplicity [Fintype V] {v : V}
    (hv : v ∈ P.graphVertexFinset) : 1 ≤ P.vertexMultiplicity v := by
  classical
  obtain ⟨i, hi⟩ := (P.mem_graphVertexFinset_iff v).mp hv
  simp only [vertexMultiplicity]
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

/-- Double-counting incidences `(piece, incident vertex)`. -/
theorem sum_vertex_card_eq_sum_multiplicity [Fintype V] :
    (∑ i, (P.vertexFinset i).card) =
      ∑ v ∈ P.graphVertexFinset, P.vertexMultiplicity v := by
  classical
  calc
    (∑ i, (P.vertexFinset i).card) =
        ∑ i, ∑ v ∈ P.graphVertexFinset,
          if v ∈ P.vertexFinset i then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            let S := P.graphVertexFinset
            let T := P.vertexFinset i
            have hTS : T ⊆ S := P.vertexFinset_subset_graphVertexFinset i
            have hfilter : S.filter (fun v ↦ v ∈ T) = T := by
              ext v
              simp only [Finset.mem_filter]
              constructor
              · exact fun hv ↦ hv.2
              · exact fun hv ↦ ⟨hTS hv, hv⟩
            have hcard := Finset.card_filter (fun v ↦ v ∈ T) S
            rw [hfilter] at hcard
            simpa only [S, T] using hcard
    _ = ∑ v ∈ P.graphVertexFinset, ∑ i,
          if v ∈ P.vertexFinset i then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ v ∈ P.graphVertexFinset, P.vertexMultiplicity v := by
            apply Finset.sum_congr rfl
            intro v _
            have hcard := Finset.card_filter
              (fun i ↦ v ∈ P.vertexFinset i) (Finset.univ : Finset (Fin m))
            simpa only [vertexMultiplicity] using hcard.symm

/-- Covering all graph edges guarantees that the paper's natural-number
subtraction in `overlap` does not truncate. -/
theorem graphVertex_card_le_sum_vertex_card [Fintype V] :
    P.graphVertexFinset.card ≤ ∑ i, (P.vertexFinset i).card := by
  classical
  rw [P.sum_vertex_card_eq_sum_multiplicity, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv ↦ P.one_le_vertexMultiplicity hv

theorem overlap_add_graphVertex_card [Fintype V] :
    P.overlap + P.graphVertexFinset.card = ∑ i, (P.vertexFinset i).card := by
  classical
  exact Nat.sub_add_cancel P.graphVertex_card_le_sum_vertex_card

private theorem sum_sub_one_eq_sum_sub_card {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, 1 ≤ f x) :
    (∑ x ∈ s, (f x - 1)) = (∑ x ∈ s, f x) - s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : 1 ≤ f a := hf a (by simp)
      have hfs : ∀ x ∈ s, 1 ≤ f x := fun x hx ↦ hf x (by simp [hx])
      have hsum : s.card ≤ ∑ x ∈ s, f x := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun x hx ↦ hfs x hx
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
        ih hfs]
      omega

/-- The paper's overlap is the sum, over graph vertices, of the number of
extra piece incidences. -/
theorem overlap_eq_sum_multiplicity_sub_one [Fintype V] :
    P.overlap = ∑ v ∈ P.graphVertexFinset, (P.vertexMultiplicity v - 1) := by
  classical
  rw [overlap, P.sum_vertex_card_eq_sum_multiplicity]
  exact (sum_sub_one_eq_sum_sub_card P.graphVertexFinset P.vertexMultiplicity
    (fun v hv ↦ P.one_le_vertexMultiplicity hv)).symm

end OrderedEdgeDecomposition

/-- The data used by the paper's final overlap-charging argument.  For each
graph vertex, `charge v` is a set of quotient-tree interfaces.  It must pay for
all repeated piece incidences of `v`, while each interface may be charged by at
most `k+1` vertices. -/
structure InterfaceChargingWitness [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (P : OrderedEdgeDecomposition G m) (k : ℕ) where
  quotient : SimpleGraph (Fin m)
  quotient_isTree : quotient.IsTree
  charge : V → Finset quotient.edgeSet
  multiplicity_le_charge : ∀ v ∈ P.graphVertexFinset,
    P.vertexMultiplicity v - 1 ≤ (charge v).card
  interface_bound : ∀ e : quotient.edgeSet,
    (P.graphVertexFinset.filter fun v ↦ e ∈ charge v).card ≤ k + 1

namespace InterfaceChargingWitness

variable [Fintype V] {G : SimpleGraph V} {m k : ℕ}
    {P : OrderedEdgeDecomposition G m} (W : InterfaceChargingWitness P k)

/-- Double-counting the incidence relation “vertex `v` charges quotient edge
`e`”. -/
theorem sum_charge_card_eq_sum_interface_card :
    (∑ v ∈ P.graphVertexFinset, (W.charge v).card) =
      ∑ e : W.quotient.edgeSet,
        (P.graphVertexFinset.filter fun v ↦ e ∈ W.charge v).card := by
  classical
  calc
    (∑ v ∈ P.graphVertexFinset, (W.charge v).card) =
        ∑ v ∈ P.graphVertexFinset, ∑ e : W.quotient.edgeSet,
          if e ∈ W.charge v then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            have hcard := Finset.card_filter
              (fun e ↦ e ∈ W.charge v) (Finset.univ : Finset W.quotient.edgeSet)
            have hfilter :
                (Finset.univ.filter fun e ↦ e ∈ W.charge v) = W.charge v := by
              ext e
              simp
            rw [hfilter] at hcard
            exact hcard
    _ = ∑ e : W.quotient.edgeSet, ∑ v ∈ P.graphVertexFinset,
          if e ∈ W.charge v then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ e : W.quotient.edgeSet,
          (P.graphVertexFinset.filter fun v ↦ e ∈ W.charge v).card := by
            apply Finset.sum_congr rfl
            intro e _
            exact (Finset.card_filter
              (fun v ↦ e ∈ W.charge v) P.graphVertexFinset).symm

/-- A tree on `m` cluster vertices has exactly `m-1` interfaces. -/
theorem card_quotient_edges : Fintype.card W.quotient.edgeSet = m - 1 := by
  classical
  have htree := W.quotient_isTree.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card] at htree
  simp only [Fintype.card_fin] at htree
  omega

/-- General overlap charging theorem.  This is the exact final inequality in
the proof of Proposition 5.1 once its cluster quotient and bag-interface
charges have been constructed. -/
theorem overlap_le (W : InterfaceChargingWitness P k) :
    P.overlap ≤ (k + 1) * (m - 1) := by
  classical
  rw [P.overlap_eq_sum_multiplicity_sub_one]
  calc
    (∑ v ∈ P.graphVertexFinset, (P.vertexMultiplicity v - 1)) ≤
        ∑ v ∈ P.graphVertexFinset, (W.charge v).card := by
          exact Finset.sum_le_sum fun v hv ↦ W.multiplicity_le_charge v hv
    _ = ∑ e : W.quotient.edgeSet,
        (P.graphVertexFinset.filter fun v ↦ e ∈ W.charge v).card :=
          W.sum_charge_card_eq_sum_interface_card
    _ ≤ ∑ _e : W.quotient.edgeSet, (k + 1) := by
          exact Finset.sum_le_sum fun e _ ↦ W.interface_bound e
    _ = (k + 1) * (m - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            W.card_quotient_edges]
          exact Nat.mul_comm _ _

end InterfaceChargingWitness

/-- A conclusion-witness for the paper's subcubic edge-owned refinement.
`owner` is defined on all symmetric pairs only to make later filtering simple;
its injectivity requirement is restricted to actual edges of `G`. -/
structure EdgeOwnedRefinementWitness (G : SimpleGraph V) (X : Type*)
    [Fintype V] [Fintype X] where
  decomposition : Decomposition G X
  owner : Sym2 V → X
  owner_inj : Set.InjOn owner G.edgeSet
  owner_hosts : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet →
    ∀ v ∈ e.toFinset, v ∈ decomposition.bag (owner e)
  subcubic : ∀ x : X, decomposition.tree.degree x ≤ 3

/-- A witness for partitioning an edge-owned decomposition tree into connected
clusters.  The quotient is recorded extensionally: two distinct clusters are
adjacent exactly when an original tree edge crosses between them. -/
structure ClusterQuotientWitness {G : SimpleGraph V} {X : Type*}
    [Fintype V] [Fintype X] (R : EdgeOwnedRefinementWitness G X)
    (m lower upper : ℕ) where
  clusterOf : X → Fin m
  cluster_surjective : Function.Surjective clusterOf
  cluster_connected : ∀ i : Fin m,
    (R.decomposition.tree.induce {x : X | clusterOf x = i}).Connected
  quotient : SimpleGraph (Fin m)
  quotient_adj : ∀ ⦃i j : Fin m⦄, quotient.Adj i j ↔
    i ≠ j ∧ ∃ x y : X,
      R.decomposition.tree.Adj x y ∧ clusterOf x = i ∧ clusterOf y = j
  quotient_isTree : quotient.IsTree
  cluster_lower : ∀ i : Fin m,
    lower ≤ (G.edgeFinset.filter fun e ↦ clusterOf (R.owner e) = i).card
  cluster_upper : ∀ i : Fin m,
    (G.edgeFinset.filter fun e ↦ clusterOf (R.owner e) = i).card ≤ upper

namespace ClusterQuotientWitness

variable [Fintype V] [Fintype X] {G : SimpleGraph V}
    {m lower upper : ℕ} {R : EdgeOwnedRefinementWitness G X}
    (C : ClusterQuotientWitness R m lower upper)

/-- The graph piece consisting of the edges whose owner lies in cluster `i`.
The construction does not impose connectedness. -/
noncomputable def piece (i : Fin m) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e : Sym2 V |
    e ∈ G.edgeSet ∧ C.clusterOf (R.owner e) = i}

theorem piece_edgeSet (i : Fin m) :
    (C.piece i).edgeSet = {e : Sym2 V |
      e ∈ G.edgeSet ∧ C.clusterOf (R.owner e) = i} := by
  classical
  rw [piece, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · exact fun h ↦ h.1
  · rintro h
    exact ⟨h, G.not_isDiag_of_mem_edgeSet h.1⟩

theorem piece_le (i : Fin m) : C.piece i ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet, C.piece_edgeSet]
  exact fun _e he ↦ he.1

theorem piece_edgeFinset (i : Fin m) :
    (C.piece i).edgeFinset =
      G.edgeFinset.filter fun e ↦ C.clusterOf (R.owner e) = i := by
  classical
  ext e
  simp only [SimpleGraph.mem_edgeFinset, C.piece_edgeSet, Set.mem_setOf_eq,
    Finset.mem_filter]

/-- Owner clusters give an ordered edge decomposition whenever every cluster
owns at least one edge. -/
noncomputable def edgeDecomposition (hlower : 0 < lower) :
    OrderedEdgeDecomposition G m where
  piece := C.piece
  piece_nonempty := by
    intro i hbot
    have hpos : 0 <
        (G.edgeFinset.filter fun e ↦ C.clusterOf (R.owner e) = i).card :=
      lt_of_lt_of_le hlower (C.cluster_lower i)
    have hpiecepos : 0 < (C.piece i).edgeFinset.card := by
      simpa [C.piece_edgeFinset i] using hpos
    simp [hbot] at hpiecepos
  piece_le := C.piece_le
  edge_disjoint := by
    intro i _ j _ hij
    apply SimpleGraph.disjoint_edgeSet.mp
    rw [C.piece_edgeSet, C.piece_edgeSet]
    refine Set.disjoint_left.mpr ?_
    rintro e ⟨_he, hi⟩ ⟨_he', hj⟩
    exact hij (hi.symm.trans hj)
  cover := by
    apply le_antisymm
    · exact iSup_le fun i ↦ C.piece_le i
    · intro u v huv
      rw [SimpleGraph.iSup_adj]
      let i : Fin m := C.clusterOf (R.owner s(u, v))
      refine ⟨i, ?_⟩
      rw [← SimpleGraph.mem_edgeSet, C.piece_edgeSet]
      exact ⟨huv, rfl⟩

theorem edgeDecomposition_piece (hlower : 0 < lower) (i : Fin m) :
    (C.edgeDecomposition hlower).piece i = C.piece i := rfl

theorem edgeDecomposition_piece_card_lower (hlower : 0 < lower) (i : Fin m) :
    lower ≤ ((C.edgeDecomposition hlower).piece i).edgeFinset.card := by
  simpa [C.edgeDecomposition_piece hlower i, C.piece_edgeFinset i] using
    C.cluster_lower i

theorem edgeDecomposition_piece_card_upper (hlower : 0 < lower) (i : Fin m) :
    ((C.edgeDecomposition hlower).piece i).edgeFinset.card ≤ upper := by
  simpa [C.edgeDecomposition_piece hlower i, C.piece_edgeFinset i] using
    C.cluster_upper i

end ClusterQuotientWitness

/-- Complete explicit data needed to obtain the paper's small-overlap edge
division from an edge-owned refinement.  The separate `charging` field is the
interface argument: constructing it from bag subtrees is precisely the part of
Proposition 5.1 not claimed as an existence theorem in this module. -/
structure SmallOverlapDivisionWitness (G : SimpleGraph V) (k l m : ℕ)
    [Fintype V] where
  nodeCount : ℕ
  refinement : EdgeOwnedRefinementWitness G (Fin nodeCount)
  widthAtMost : refinement.decomposition.WidthAtMost k
  l_pos : 0 < l
  clustering : ClusterQuotientWitness refinement m l (3 * l)
  charging : InterfaceChargingWitness (clustering.edgeDecomposition l_pos) k
  charging_quotient : charging.quotient = clustering.quotient

namespace SmallOverlapDivisionWitness

variable [Fintype V] {G : SimpleGraph V} {k l m : ℕ}
    (W : SmallOverlapDivisionWitness G k l m)

/-- Conditional, witness-level form of Proposition 5.1.  This theorem is
faithful about its status: it extracts the advertised edge decomposition from
the explicit refinement, clustering, and interface-charging witnesses; it does
not assert that ordinary treewidth alone already supplies those witnesses. -/
theorem exists_orderedEdgeDecomposition (W : SmallOverlapDivisionWitness G k l m) :
    ∃ P : OrderedEdgeDecomposition G m,
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ (k + 1) * (m - 1) := by
  let P := W.clustering.edgeDecomposition W.l_pos
  refine ⟨P, ?_, ?_⟩
  · intro i
    exact ⟨W.clustering.edgeDecomposition_piece_card_lower W.l_pos i,
      W.clustering.edgeDecomposition_piece_card_upper W.l_pos i⟩
  · exact W.charging.overlap_le

end SmallOverlapDivisionWitness

end

end TreeDecomposition

end LowDegree
