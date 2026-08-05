import LowDegree.Combinatorics.IndexedWeightedTreePartition

/-!
# Interface charging for connected tree clusters

This module supplies the interface-charging argument left abstract in
`TreeDecomposition.InterfaceChargingWitness`.  A connected clustering of the
nodes of an edge-owned tree decomposition determines one original tree edge
above every quotient-tree edge.  A graph vertex charges precisely those
interfaces whose two endpoint bags contain it.
-/

namespace LowDegree

open scoped BigOperators

open IndexedWeightedTreePartition
open IndexedWeightedTreePartition.TreeConnectedQuotient

namespace TreeDecomposition

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

variable {V X : Type*} [Fintype V] [Fintype X]
variable {G : SimpleGraph V} {m lower upper k : ℕ}
variable {R : EdgeOwnedRefinementWitness G X}

/-- A walk can be mapped through a vertex map that sends each edge either to
an equality or to a target edge.  Equal consecutive images are simply
contracted at the reachability level. -/
private theorem reachable_map_eq_or_adj {A B : Type*}
    {Q : SimpleGraph A} {H : SimpleGraph B} (f : A → B)
    (hmap : ∀ {a b : A}, Q.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    {a b : A} (h : Q.Reachable a b) : H.Reachable (f a) (f b) := by
  apply h.elim
  intro p
  clear h
  induction p with
  | nil => exact .rfl
  | @cons a b c hab p ih =>
      rcases hmap hab with heq | hadj
      · simpa [heq] using ih
      · exact hadj.reachable.trans ih

namespace ClusterQuotientWitness

variable (C : ClusterQuotientWitness R m lower upper)

/-- Forward realization of quotient adjacency by an original decomposition-tree
edge, packaged in the form used by `TreeConnectedQuotient.liftedEdge`. -/
theorem quotientForward {i j : Fin m} (h : C.quotient.Adj i j) :
    ∃ x y : X, R.decomposition.tree.Adj x y ∧
      C.clusterOf x = i ∧ C.clusterOf y = j := by
  exact (C.quotient_adj.mp h).2

/-- The unique original decomposition-tree edge lying above a quotient
interface. -/
noncomputable def interfaceTreeEdge (e : C.quotient.edgeSet) :
    R.decomposition.tree.edgeSet :=
  liftedEdge (Q := R.decomposition.tree) (H := C.quotient)
    C.clusterOf (fun {_ _} h ↦ C.quotientForward h) e

theorem interfaceTreeEdge_map (e : C.quotient.edgeSet) :
    (C.interfaceTreeEdge e).val.map C.clusterOf = e.val :=
  liftedEdge_map (Q := R.decomposition.tree) (H := C.quotient)
    C.clusterOf (fun {_ _} h ↦ C.quotientForward h) e

theorem interfaceTreeEdge_mem_crossEdges (e : C.quotient.edgeSet) :
    (C.interfaceTreeEdge e).val ∈
      crossEdges R.decomposition.tree C.clusterOf :=
  liftedEdge_mem_crossEdges (Q := R.decomposition.tree) (H := C.quotient)
    C.clusterOf (fun {_ _} h ↦ C.quotientForward h) e

/-- The cluster indices whose pieces contain an edge incident to `v`. -/
noncomputable def pieceClusters (hlower : 0 < lower) (v : V) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦
    v ∈ (C.edgeDecomposition hlower).vertexFinset i

/-- The cluster indices containing at least one decomposition bag containing
`v`. -/
noncomputable def bagClusters (v : V) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦
    ∃ x : X, C.clusterOf x = i ∧ v ∈ R.decomposition.bag x

/-- Every cluster whose owner-piece is incident to `v` contains a bag node
whose bag contains `v`. -/
theorem pieceClusters_subset_bagClusters (hlower : 0 < lower) (v : V) :
    C.pieceClusters hlower v ⊆ C.bagClusters v := by
  classical
  intro i hi
  simp only [pieceClusters, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [(C.edgeDecomposition hlower).mem_vertexFinset] at hi
  change v ∈ (C.piece i).support at hi
  obtain ⟨w, hvw⟩ := hi
  have hePiece : s(v, w) ∈ (C.piece i).edgeSet := by
    rwa [SimpleGraph.mem_edgeSet]
  rw [C.piece_edgeSet] at hePiece
  have hvPair : v ∈ s(v, w).toFinset := by simp
  have hvBag := R.owner_hosts hePiece.1 v hvPair
  simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨R.owner s(v, w), hePiece.2, hvBag⟩

/-- The quotient clusters met by the bag-subtree of `v` induce a connected
subgraph of the quotient tree. -/
theorem bagClusters_connected (v : V) (hne : (C.bagClusters v).Nonempty) :
    (C.quotient.induce {i : Fin m | i ∈ C.bagClusters v}).Connected := by
  classical
  obtain ⟨i, hi⟩ := hne
  simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨x, hxi, hxv⟩ := hi
  let φ : {x : X // v ∈ R.decomposition.bag x} →
      {i : Fin m // i ∈ C.bagClusters v} :=
    fun z ↦ ⟨C.clusterOf z, by
      simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, rfl, z.property⟩⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨i, by
    simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxi, hxv⟩⟩, ?_⟩
  rintro ⟨j, hj⟩
  simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨y, hyj, hyv⟩ := hj
  have hsource :
      (R.decomposition.tree.induce
        {z : X | v ∈ R.decomposition.bag z}).Reachable
          ⟨x, hxv⟩ ⟨y, hyv⟩ :=
    R.decomposition.running_intersection v |>.preconnected _ _
  have himage := reachable_map_eq_or_adj φ (Q :=
      R.decomposition.tree.induce {z : X | v ∈ R.decomposition.bag z})
      (H := C.quotient.induce {i : Fin m | i ∈ C.bagClusters v})
      (fun {a b} hab ↦ by
        by_cases heq : C.clusterOf a = C.clusterOf b
        · left
          exact Subtype.ext heq
        · right
          change C.quotient.Adj (C.clusterOf a) (C.clusterOf b)
          exact C.quotient_adj.mpr
            ⟨heq, a, b, hab, rfl, rfl⟩)
      hsource
  simpa [φ, hxi, hyj] using himage

/-- A vertex charges an interface when it belongs to both endpoint bags of
the lifted tree edge. -/
def Charges (e : C.quotient.edgeSet) (v : V) : Prop :=
  ∀ x ∈ (C.interfaceTreeEdge e).val, v ∈ R.decomposition.bag x

/-- If both endpoint clusters of a quotient edge meet the bag-subtree of `v`,
then the unique lifted interface edge has `v` in both endpoint bags.  The key
point is that every edge of a tree is a bridge: splice paths inside the two
cluster fibers onto a path in the bag-subtree, and the bridge must occur in
the middle path. -/
theorem charges_of_endpoints_mem_bagClusters (v : V)
    (e : C.quotient.edgeSet)
    (he : ∀ i ∈ e.val, i ∈ C.bagClusters v) : C.Charges e v := by
  classical
  let qe : R.decomposition.tree.edgeSet := C.interfaceTreeEdge e
  let a : X := qe.val.out.1
  let b : X := qe.val.out.2
  have habPair : s(a, b) = qe.val := by
    exact qe.val.out_eq
  have hab : R.decomposition.tree.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, habPair]
    exact qe.property
  have hcross : qe.val ∈ crossEdges R.decomposition.tree C.clusterOf := by
    simpa [qe] using C.interfaceTreeEdge_mem_crossEdges e
  have hcluster_ne : C.clusterOf a ≠ C.clusterOf b := by
    intro hEq
    have hdiag : (qe.val.map C.clusterOf).IsDiag := by
      rw [← habPair]
      simp [hEq]
    exact ((mem_crossEdges_iff R.decomposition.tree C.clusterOf qe.val).mp
      hcross).2 hdiag
  have hca_mem : C.clusterOf a ∈ e.val := by
    rw [← C.interfaceTreeEdge_map e]
    refine Sym2.mem_map.mpr ⟨a, ?_, rfl⟩
    simpa [qe, a] using Sym2.out_fst_mem qe.val
  have hcb_mem : C.clusterOf b ∈ e.val := by
    rw [← C.interfaceTreeEdge_map e]
    refine Sym2.mem_map.mpr ⟨b, ?_, rfl⟩
    simpa [qe, b] using Sym2.out_snd_mem qe.val
  have hca := he (C.clusterOf a) hca_mem
  have hcb := he (C.clusterOf b) hcb_mem
  simp only [bagClusters, Finset.mem_filter, Finset.mem_univ, true_and] at hca hcb
  obtain ⟨x, hxa, hxv⟩ := hca
  obtain ⟨y, hyb, hyv⟩ := hcb
  have hax :
      (R.decomposition.tree.induce
        (fiber C.clusterOf (C.clusterOf a))).Reachable
          ⟨a, rfl⟩ ⟨x, hxa⟩ := by
    exact C.cluster_connected (C.clusterOf a) |>.preconnected _ _
  have hxy :
      (R.decomposition.tree.induce
        {z : X | v ∈ R.decomposition.bag z}).Reachable
          ⟨x, hxv⟩ ⟨y, hyv⟩ := by
    exact R.decomposition.running_intersection v |>.preconnected _ _
  have hybPath :
      (R.decomposition.tree.induce
        (fiber C.clusterOf (C.clusterOf b))).Reachable
          ⟨y, hyb⟩ ⟨b, rfl⟩ := by
    exact C.cluster_connected (C.clusterOf b) |>.preconnected _ _
  apply hax.elim
  intro pax
  apply hxy.elim
  intro pxy
  apply hybPath.elim
  intro pyb
  let pax' : R.decomposition.tree.Walk a x :=
    pax.map (SimpleGraph.Embedding.induce _).toHom
  let pxy' : R.decomposition.tree.Walk x y :=
    pxy.map (SimpleGraph.Embedding.induce _).toHom
  let pyb' : R.decomposition.tree.Walk y b :=
    pyb.map (SimpleGraph.Embedding.induce _).toHom
  have hbridge : R.decomposition.tree.IsBridge s(a, b) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      R.decomposition.isTree.IsAcyclic) hab
  have hedge : s(a, b) ∈ (pax'.append (pxy'.append pyb')).edges :=
    (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge).2 _
  have hnotax : s(a, b) ∉ pax'.edges := by
    intro hedgeAx
    have hbSupport := pax'.snd_mem_support_of_mem_edges hedgeAx
    simp only [pax', SimpleGraph.Walk.support_map, List.mem_map] at hbSupport
    obtain ⟨z, _hz, hzb⟩ := hbSupport
    change (z : X) = b at hzb
    apply hcluster_ne
    have hzprop : C.clusterOf (z : X) = C.clusterOf a := z.property
    rw [hzb] at hzprop
    exact hzprop.symm
  have hnotyb : s(a, b) ∉ pyb'.edges := by
    intro hedgeYb
    have haSupport := pyb'.fst_mem_support_of_mem_edges hedgeYb
    simp only [pyb', SimpleGraph.Walk.support_map, List.mem_map] at haSupport
    obtain ⟨z, _hz, hza⟩ := haSupport
    change (z : X) = a at hza
    apply hcluster_ne
    have hzprop : C.clusterOf (z : X) = C.clusterOf b := z.property
    rw [hza] at hzprop
    exact hzprop
  simp only [SimpleGraph.Walk.edges_append, List.mem_append] at hedge
  have hedgeXY : s(a, b) ∈ pxy'.edges := by
    rcases hedge with hedgeAx | hedgeXY | hedgeYb
    · exact (hnotax hedgeAx).elim
    · exact hedgeXY
    · exact (hnotyb hedgeYb).elim
  have haSupport := pxy'.fst_mem_support_of_mem_edges hedgeXY
  have hbSupport := pxy'.snd_mem_support_of_mem_edges hedgeXY
  simp only [pxy', SimpleGraph.Walk.support_map, List.mem_map] at haSupport hbSupport
  obtain ⟨za, _hza, hzaa⟩ := haSupport
  obtain ⟨zb, _hzb, hzbb⟩ := hbSupport
  change (za : X) = a at hzaa
  change (zb : X) = b at hzbb
  have hav : v ∈ R.decomposition.bag a := by
    have hzprop : v ∈ R.decomposition.bag (za : X) := za.property
    rw [hzaa] at hzprop
    exact hzprop
  have hbv : v ∈ R.decomposition.bag b := by
    have hzprop : v ∈ R.decomposition.bag (zb : X) := zb.property
    rw [hzbb] at hzprop
    exact hzprop
  intro z hz
  rw [← habPair] at hz
  simp only [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hav
  · exact hbv

/-- The finite set of interfaces charged by `v`. -/
noncomputable def charge (v : V) : Finset C.quotient.edgeSet :=
  Finset.univ.filter fun e ↦ C.Charges e v

@[simp]
theorem mem_charge (e : C.quotient.edgeSet) (v : V) :
    e ∈ C.charge v ↔ C.Charges e v := by
  simp [charge]

/-- Quotient edges whose two endpoints both occur among `v`'s bag clusters. -/
noncomputable def bagClusterEdges (v : V) : Finset (Sym2 (Fin m)) :=
  C.quotient.edgeFinset ∩ (C.bagClusters v).sym2

/-- `bagClusterEdges` is the edge set of the induced quotient graph on the
clusters met by `v`'s bag-subtree. -/
theorem bagClusterEdges_card_eq_induce (v : V) :
    (C.bagClusterEdges v).card =
      Nat.card (C.quotient.induce
        {i : Fin m | i ∈ C.bagClusters v}).edgeSet := by
  classical
  let S : Set (Fin m) := {i : Fin m | i ∈ C.bagClusters v}
  letI : Fintype S := Subtype.fintype (Membership.mem S)
  change (C.bagClusterEdges v).card =
    Nat.card (C.quotient.induce S).edgeSet
  have hmap := C.quotient.map_edgeFinset_induce (s := S)
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hcard
  simpa [bagClusterEdges, S] using hcard.symm

/-- When nonempty, the connected cluster set met by a bag-subtree contains
exactly one fewer induced quotient edges than vertices. -/
theorem bagClusterEdges_card_eq_sub_one (v : V)
    (hne : (C.bagClusters v).Nonempty) :
    (C.bagClusterEdges v).card = (C.bagClusters v).card - 1 := by
  classical
  let S : Set (Fin m) := {i : Fin m | i ∈ C.bagClusters v}
  have htree : (C.quotient.induce S).IsTree :=
    { isConnected := by
        simpa [S] using C.bagClusters_connected v hne
      IsAcyclic := C.quotient_isTree.IsAcyclic.induce S }
  have hedge := htree.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hedge
  have hvertex : Fintype.card S = (C.bagClusters v).card := by
    apply Fintype.card_of_subtype (C.bagClusters v)
    intro i
    rfl
  rw [hvertex] at hedge
  rw [C.bagClusterEdges_card_eq_induce v]
  simpa [S] using (show
    Nat.card (C.quotient.induce S).edgeSet =
      (C.bagClusters v).card - 1 by omega)

/-- Every induced edge on the cluster set met by `v` contributes a distinct
charge of `v`. -/
theorem bagClusterEdges_card_le_charge (v : V) :
    (C.bagClusterEdges v).card ≤ (C.charge v).card := by
  classical
  let liftCharged :
      {e : Sym2 (Fin m) // e ∈ C.bagClusterEdges v} →
        {e : C.quotient.edgeSet // e ∈ C.charge v} :=
    fun e ↦
      let heEdge : e.val ∈ C.quotient.edgeSet := by
        rw [← SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_inter.mp e.property).1
      let qe : C.quotient.edgeSet := ⟨e.val, heEdge⟩
      ⟨qe, C.mem_charge qe v |>.mpr <|
        C.charges_of_endpoints_mem_bagClusters v qe <| by
          intro i hi
          exact Finset.mem_sym2_iff.mp
            (Finset.mem_inter.mp e.property).2 i hi⟩
  have hinj : Function.Injective liftCharged := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval := congrArg (fun z ↦ z.val.val) h
    exact hval
  have hcard := Fintype.card_le_of_injective liftCharged hinj
  have hsource :
      Fintype.card {e : Sym2 (Fin m) // e ∈ C.bagClusterEdges v} =
        (C.bagClusterEdges v).card := by
    apply Fintype.card_of_subtype (C.bagClusterEdges v)
    intro e
    rfl
  have htarget :
      Fintype.card {e : C.quotient.edgeSet // e ∈ C.charge v} =
        (C.charge v).card := by
    apply Fintype.card_of_subtype (C.charge v)
    intro e
    rfl
  rwa [hsource, htarget] at hcard

/-- Piece multiplicity is exactly the cardinality of `pieceClusters`. -/
theorem vertexMultiplicity_eq_card_pieceClusters (hlower : 0 < lower) (v : V) :
    (C.edgeDecomposition hlower).vertexMultiplicity v =
      (C.pieceClusters hlower v).card := by
  rfl

/-- The connected bag-subtree supplies at least one distinct charged
interface for every repeated piece incidence. -/
theorem multiplicity_sub_one_le_charge (hlower : 0 < lower) (v : V)
    (hv : v ∈ (C.edgeDecomposition hlower).graphVertexFinset) :
    (C.edgeDecomposition hlower).vertexMultiplicity v - 1 ≤
      (C.charge v).card := by
  classical
  let P := C.edgeDecomposition hlower
  obtain ⟨i, hi⟩ := (P.mem_graphVertexFinset_iff v).mp hv
  have hiPiece : i ∈ C.pieceClusters hlower v := by
    simp [pieceClusters, P, hi]
  have hiBag : i ∈ C.bagClusters v :=
    C.pieceClusters_subset_bagClusters hlower v hiPiece
  have hbagNonempty : (C.bagClusters v).Nonempty := ⟨i, hiBag⟩
  rw [C.vertexMultiplicity_eq_card_pieceClusters hlower v]
  calc
    (C.pieceClusters hlower v).card - 1 ≤
        (C.bagClusters v).card - 1 :=
      Nat.sub_le_sub_right
        (Finset.card_le_card (C.pieceClusters_subset_bagClusters hlower v)) 1
    _ = (C.bagClusterEdges v).card :=
      (C.bagClusterEdges_card_eq_sub_one v hbagNonempty).symm
    _ ≤ (C.charge v).card := C.bagClusterEdges_card_le_charge v

/-- At most one bag's worth of vertices can charge a fixed interface. -/
theorem charge_interface_bound
    (hlower : 0 < lower) (hwidth : R.decomposition.WidthAtMost k)
    (e : C.quotient.edgeSet) :
    ((C.edgeDecomposition hlower).graphVertexFinset.filter
      fun v ↦ e ∈ C.charge v).card ≤ k + 1 := by
  classical
  let x : X := (C.interfaceTreeEdge e).val.out.1
  have hsubset :
      (C.edgeDecomposition hlower).graphVertexFinset.filter
          (fun v ↦ e ∈ C.charge v) ⊆
        R.decomposition.bag x := by
    intro v hv
    have hcharge : C.Charges e v :=
      (C.mem_charge e v).mp (Finset.mem_filter.mp hv).2
    exact hcharge x (by
      dsimp [x]
      exact Sym2.out_fst_mem _)
  exact (Finset.card_le_card hsubset).trans (hwidth x)

/-- Canonical interface-charging witness supplied by any connected quotient of
an edge-owned width-`k` tree decomposition. -/
noncomputable def interfaceChargingWitness (hlower : 0 < lower)
    (hwidth : R.decomposition.WidthAtMost k) :
    InterfaceChargingWitness (C.edgeDecomposition hlower) k where
  quotient := C.quotient
  quotient_isTree := C.quotient_isTree
  charge := C.charge
  multiplicity_le_charge := C.multiplicity_sub_one_le_charge hlower
  interface_bound := C.charge_interface_bound hlower hwidth

@[simp]
theorem interfaceChargingWitness_quotient (hlower : 0 < lower)
    (hwidth : R.decomposition.WidthAtMost k) :
    (C.interfaceChargingWitness hlower hwidth).quotient = C.quotient := rfl

/-- Existence form of `interfaceChargingWitness`, convenient for downstream
witness assembly. -/
theorem exists_interfaceChargingWitness (hlower : 0 < lower)
    (hwidth : R.decomposition.WidthAtMost k) :
    Nonempty (InterfaceChargingWitness (C.edgeDecomposition hlower) k) :=
  ⟨C.interfaceChargingWitness hlower hwidth⟩

end ClusterQuotientWitness

namespace SmallOverlapDivisionWitness

/-- Assemble the paper's full division witness from a finite-indexed
edge-owned refinement and its connected weighted clustering.  The charging
field is now canonical rather than an additional hypothesis. -/
noncomputable def ofClustering {n l : ℕ}
    (R : EdgeOwnedRefinementWitness G (Fin n))
    (hwidth : R.decomposition.WidthAtMost k) (hl : 0 < l)
    (C : ClusterQuotientWitness R m l (3 * l)) :
    SmallOverlapDivisionWitness G k l m where
  nodeCount := n
  refinement := R
  widthAtMost := hwidth
  l_pos := hl
  clustering := C
  charging := C.interfaceChargingWitness hl hwidth
  charging_quotient := rfl

end SmallOverlapDivisionWitness

end

end TreeDecomposition
end LowDegree
