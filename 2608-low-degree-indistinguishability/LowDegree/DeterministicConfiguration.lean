import LowDegree.DeterministicConfigurationBase
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite configuration-model objects

This module contains the exact, non-asymptotic part of the Appendix
construction.  A configuration is a fixed-point-free involution of the
`m * D` labelled half-edges.  Projecting paired half-edges to their incident
vertices and then forgetting loops and parallel multiplicities gives a
finite simple graph.

The probabilistic estimates used to select a good configuration live in
downstream modules.  Keeping the finite construction separate makes clear
which losses come from loops/parallel pairs and which come from deleting
short cycles.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Edge-count transport into an ambient vertex set -/

/-- Injective padding preserves the exact number of edges induced by an
ambient set after pulling the set back to the source.  The proof passes
through `Set.ncard`, avoiding any dependence on a chosen decidable-adjacency
instance. -/
theorem deterministicInducedEdgeCount_map
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) (U : Finset W) :
    deterministicInducedEdgeCount (G.map f) U =
      deterministicInducedEdgeCount G (embeddingPreimageFinset f U) := by
  classical
  unfold deterministicInducedEdgeCount
  rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
  rw [induce_map_eq_map_induce_preimage,
    SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _
    (embeddingPreimageSubtype f U).sym2Map.injective

/-! ## Girth transport through isolated-vertex padding -/

/-- A graph mapped along an injection retracts to the source graph.  Values
outside the injection range are irrelevant because they are isolated. -/
noncomputable def mapRetractHom
    {V W : Type*} [Nonempty V] (f : V ↪ W) (G : SimpleGraph V) :
    G.map f →g G where
  toFun := Function.invFun f
  map_rel' := by
    intro a b hab
    rcases (SimpleGraph.map_adj f G a b).mp hab with ⟨u, v, huv, hu, hv⟩
    subst a
    subst b
    simpa only [Function.leftInverse_invFun f.injective u,
      Function.leftInverse_invFun f.injective v] using huv

/-- Mapping a nonempty walk to the source by `mapRetractHom` and then back
along `f` recovers the original walk, provided its initial vertex is in the
range. -/
theorem walk_mapRetract_roundTrip
    {V W : Type*} [Nonempty V] (f : V ↪ W) (G : SimpleGraph V)
    {w : W} (p : (G.map f).Walk w w) (hp : ¬p.Nil)
    (hw : w ∈ Set.range f) :
    (((p.map (mapRetractHom f G)).map
      (SimpleGraph.Embedding.map f G).toHom).copy
        (Function.invFun_eq hw) (Function.invFun_eq hw)) = p := by
  apply SimpleGraph.Walk.ext_support
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
    List.map_map]
  have hmap :
      List.map ((SimpleGraph.Embedding.map f G).toHom ∘ mapRetractHom f G)
          p.support =
        List.map id p.support := by
    apply List.map_congr_left
    intro x hx
    apply Function.invFun_eq
    have hxSupport : x ∈ (G.map f).support :=
      SimpleGraph.mem_support_of_mem_walk_support p hp hx
    rw [SimpleGraph.support_map] at hxSupport
    exact ⟨Classical.choose hxSupport, (Classical.choose_spec hxSupport).2⟩
  simpa using hmap

/-- Adding isolated vertices along an injective vertex map preserves every
real girth lower bound. -/
theorem HasRealGirthAtLeast.map
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {g : ℝ} (hG : HasRealGirthAtLeast G g)
    (f : V ↪ W) :
    HasRealGirthAtLeast (G.map f) g := by
  intro w p hp
  have hwSupport : w ∈ (G.map f).support :=
    SimpleGraph.mem_support_of_mem_walk_support p hp.not_nil p.start_mem_support
  rw [SimpleGraph.support_map] at hwSupport
  rcases hwSupport with ⟨v, hv, hvw⟩
  haveI : Nonempty V := ⟨v⟩
  have hwRange : w ∈ Set.range f := ⟨v, hvw⟩
  let q : G.Walk (Function.invFun f w) (Function.invFun f w) :=
    p.map (mapRetractHom f G)
  have hround := walk_mapRetract_roundTrip f G p hp.not_nil hwRange
  have hcopyCycle :
      (((q.map (SimpleGraph.Embedding.map f G).toHom).copy
        (Function.invFun_eq hwRange) (Function.invFun_eq hwRange))).IsCycle := by
    rw [hround]
    exact hp
  have hforwardCycle :
      (q.map (SimpleGraph.Embedding.map f G).toHom).IsCycle :=
    (SimpleGraph.Walk.isCycle_copy _ _).mp hcopyCycle
  have hqCycle : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.map f G).toHom)
      (p := q)
      (SimpleGraph.Embedding.map f G).injective).mp hforwardCycle
  simpa [q] using hG (Function.invFun f w) q hqCycle

/-- The `D` labelled half-edges incident to each of `m` vertices. -/
abbrev ConfigurationHalfEdge (m D : ℕ) := Fin m × Fin D

/-- A perfect pairing of the labelled half-edges, represented by its partner
map.  Fixed-point freeness excludes singleton blocks and involutivity says
that every block has exactly two elements. -/
structure Configuration (m D : ℕ) where
  partner : Equiv.Perm (ConfigurationHalfEdge m D)
  partner_involutive : Function.Involutive partner
  partner_ne : ∀ h, partner h ≠ h

namespace Configuration

variable {m D : ℕ}

/-- The vertex incident to a half-edge. -/
@[simp] def vertex (h : ConfigurationHalfEdge m D) : Fin m := h.1

/-- The vertex reached by following one paired half-edge. -/
def socketNeighbor (C : Configuration m D) (u : Fin m) (i : Fin D) : Fin m :=
  (C.partner (u, i)).1

/-- Collapse loops and parallel configuration edges to obtain a simple
graph.  Parallel pairs have the same adjacency witness and are therefore
automatically deduplicated by the relation. -/
def projectedGraph (C : Configuration m D) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ ∃ i : Fin D, C.socketNeighbor u i = v
  symm := by
    intro u v huv
    refine ⟨huv.1.symm, ?_⟩
    rcases huv.2 with ⟨i, hi⟩
    let p := C.partner (u, i)
    have hp : p = (v, p.2) := by
      apply Prod.ext
      · exact hi
      · rfl
    refine ⟨p.2, ?_⟩
    change (C.partner (v, p.2)).1 = u
    rw [← hp, C.partner_involutive]
  loopless := by
    intro u huu
    exact huu.1 rfl

@[simp] theorem projectedGraph_adj (C : Configuration m D) (u v : Fin m) :
    C.projectedGraph.Adj u v ↔
      u ≠ v ∧ ∃ i : Fin D, C.socketNeighbor u i = v :=
  Iff.rfl

/-- Every neighbor of `u` is reached through one of its `D` sockets. -/
theorem neighborSet_subset_socketNeighbor_range (C : Configuration m D) (u : Fin m) :
    C.projectedGraph.neighborSet u ⊆ Set.range (C.socketNeighbor u) := by
  intro v huv
  exact ⟨(Classical.choose huv.2), Classical.choose_spec huv.2⟩

/-- The collapsed simple graph has maximum degree at most the number of
half-edges per vertex. -/
theorem projectedGraph_degree_le (C : Configuration m D) (u : Fin m) :
    C.projectedGraph.degree u ≤ D := by
  rw [degree_eq_ncard_neighborSet]
  calc
    (C.projectedGraph.neighborSet u).ncard ≤
        (Set.range (C.socketNeighbor u)).ncard :=
      Set.ncard_le_ncard (C.neighborSet_subset_socketNeighbor_range u)
    _ ≤ Nat.card (Fin D) := by
      simpa only [Nat.card_coe_set_eq] using
        (Finite.card_range_le (C.socketNeighbor u))
    _ = D := by simp

/-- The handshaking bound: collapsing a configuration creates at most
`mD/2` distinct non-loop edges. -/
theorem two_mul_projectedGraph_edgeFinset_card_le (C : Configuration m D) :
    2 * C.projectedGraph.edgeFinset.card ≤ m * D := by
  rw [← C.projectedGraph.sum_degrees_eq_twice_card_edges]
  calc
    ∑ u : Fin m, C.projectedGraph.degree u ≤ ∑ _u : Fin m, D := by
      exact Finset.sum_le_sum fun u _ ↦ C.projectedGraph_degree_le u
    _ = m * D := by simp

theorem projectedGraph_edgeFinset_card_le (C : Configuration m D) :
    C.projectedGraph.edgeFinset.card ≤ m * D / 2 := by
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
  simpa [Nat.mul_comm] using C.two_mul_projectedGraph_edgeFinset_card_le

/-- Number of configuration pairs lost when loops are deleted and parallel
pairs are collapsed.  This packages both defects without importing a
separate multigraph library. -/
def projectionDefect (C : Configuration m D) : ℕ :=
  m * D / 2 - C.projectedGraph.edgeFinset.card

/-- Exact bookkeeping identity for the loop/parallel-collapse defect. -/
theorem projectedGraph_card_add_projectionDefect (C : Configuration m D) :
    C.projectedGraph.edgeFinset.card + C.projectionDefect = m * D / 2 := by
  exact Nat.add_sub_of_le C.projectedGraph_edgeFinset_card_le

/-! ## A canonical pairing and permutation realization -/

/-- Swap the two blocks in `Fin (d+d)`.  For equal block sizes this is the
standard fixed-point-free pairing of socket labels. -/
def halfSwap (d : ℕ) : Equiv.Perm (Fin (d + d)) :=
  finAddFlip

theorem halfSwap_involutive (d : ℕ) : Function.Involutive (halfSwap d) := by
  rintro ⟨k, hk⟩
  by_cases hkd : k < d
  · rw [halfSwap, finAddFlip_apply_mk_left hkd,
      finAddFlip_apply_mk_right (by omega)]
    apply Fin.ext
    simp
  · have hdk : d ≤ k := Nat.le_of_not_gt hkd
    rw [halfSwap, finAddFlip_apply_mk_right hdk,
      finAddFlip_apply_mk_left (by omega)]
    apply Fin.ext
    simp
    omega

theorem halfSwap_ne (d : ℕ) (i : Fin (d + d)) : halfSwap d i ≠ i := by
  rcases i with ⟨k, hk⟩
  by_cases hkd : k < d
  · rw [halfSwap, finAddFlip_apply_mk_left hkd]
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  · have hdk : d ≤ k := Nat.le_of_not_gt hkd
    rw [halfSwap, finAddFlip_apply_mk_right hdk]
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega

/-- Pair corresponding sockets in the two size-`d` blocks at every vertex.
This canonical configuration consists only of loops; it is used as a base
pairing which a permutation conjugates into an arbitrary configuration. -/
def standardConfiguration (m d : ℕ) : Configuration m (d + d) where
  partner := Equiv.prodCongr (Equiv.refl (Fin m)) (halfSwap d)
  partner_involutive := by
    intro h
    apply Prod.ext
    · rfl
    · exact halfSwap_involutive d h.2
  partner_ne := by
    intro h heq
    exact halfSwap_ne d h.2 (congrArg Prod.snd heq)

/-- Conjugate a configuration pairing by a relabelling of the half-edges. -/
def relabel (C : Configuration m D)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) : Configuration m D where
  partner := (sigma.symm.trans C.partner).trans sigma
  partner_involutive := by
    intro h
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [C.partner_involutive]
    exact sigma.apply_symm_apply h
  partner_ne := by
    intro h heq
    apply C.partner_ne (sigma.symm h)
    apply sigma.injective
    rw [sigma.apply_symm_apply]
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using heq

/-- The permutation presentation of the configuration model: uniformly
relabel the canonical perfect pairing. -/
def ofPermutation (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    Configuration m (d + d) :=
  (standardConfiguration m d).relabel sigma

end Configuration

/-! ## Deterministic short-cycle pruning -/

/-- Edges which occur in a cycle of length strictly below `L`. -/
noncomputable def shortCycleEdges
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length < L ∧ e ∈ w.edgeSet

theorem mem_shortCycleEdges
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) (e : Sym2 V) :
    e ∈ shortCycleEdges G L ↔
      e ∈ G.edgeSet ∧
        ∃ (v : V) (w : G.Walk v v),
          w.IsCycle ∧ w.length < L ∧ e ∈ w.edgeSet := by
  classical
  simp [shortCycleEdges]

/-- Delete every edge which lies in at least one cycle shorter than `L`. -/
noncomputable def shortCyclePrunedGraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) : SimpleGraph V :=
  G.deleteEdges (shortCycleEdges G L : Set (Sym2 V))

theorem shortCyclePrunedGraph_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    shortCyclePrunedGraph G L ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- The pruning operation removes precisely the selected finite edge set. -/
theorem shortCyclePrunedGraph_edgeFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    (shortCyclePrunedGraph G L).edgeFinset =
      G.edgeFinset \ shortCycleEdges G L := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  unfold shortCyclePrunedGraph
  rw [SimpleGraph.edgeSet_deleteEdges]
  rfl

theorem shortCycleEdges_subset_edgeFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    shortCycleEdges G L ⊆ G.edgeFinset := by
  intro e he
  change e ∈ G.edgeFinset.filter (fun e ↦
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length < L ∧ e ∈ w.edgeSet) at he
  exact (Finset.mem_filter.mp he).1

/-- Exact edge-count loss under short-cycle pruning. -/
theorem shortCyclePrunedGraph_edgeFinset_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    (shortCyclePrunedGraph G L).edgeFinset.card =
      G.edgeFinset.card - (shortCycleEdges G L).card := by
  rw [shortCyclePrunedGraph_edgeFinset,
    Finset.card_sdiff_of_subset (shortCycleEdges_subset_edgeFinset G L)]

/-- Every cycle remaining after pruning has length at least `L`. -/
theorem shortCyclePrunedGraph_cycle_length
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ)
    {v : V} (p : (shortCyclePrunedGraph G L).Walk v v)
    (hp : p.IsCycle) :
    L ≤ p.length := by
  classical
  by_contra hnot
  have hlt : p.length < L := Nat.lt_of_not_ge hnot
  have hpos : 0 < p.edges.length := by
    rw [p.length_edges]
    exact (SimpleGraph.Walk.not_nil_iff_lt_length.mp hp.not_nil)
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges (List.ne_nil_of_length_pos hpos)
  let q : G.Walk v v := p.mapLe (shortCyclePrunedGraph_le G L)
  have hqcycle : q.IsCycle := hp.mapLe (shortCyclePrunedGraph_le G L)
  have heq : e ∈ q.edgeSet := by
    change e ∈ q.edges
    simpa [q] using he
  have hbad : e ∈ shortCycleEdges G L := by
    rw [mem_shortCycleEdges]
    refine ⟨q.edges_subset_edgeSet (SimpleGraph.Walk.mem_edgeSet.mp heq),
      v, q, hqcycle, ?_, heq⟩
    simpa [q] using hlt
  have hpruned : e ∈ (shortCyclePrunedGraph G L).edgeSet :=
    p.edges_subset_edgeSet he
  unfold shortCyclePrunedGraph at hpruned
  rw [SimpleGraph.edgeSet_deleteEdges] at hpruned
  exact hpruned.2 hbad

/-- Real-valued girth certificate furnished by the integer cutoff. -/
theorem shortCyclePrunedGraph_hasRealGirthAtLeast
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    HasRealGirthAtLeast (shortCyclePrunedGraph G L) (L : ℝ) := by
  intro v p hp
  exact_mod_cast shortCyclePrunedGraph_cycle_length G L p hp

/-- Induced edge counts are monotone under passage to a subgraph. -/
theorem deterministicInducedEdgeCount_mono
    {V : Type*} [Fintype V] {G H : SimpleGraph V} (hHG : H ≤ G)
    (U : Finset V) :
    deterministicInducedEdgeCount H U ≤ deterministicInducedEdgeCount G U := by
  classical
  unfold deterministicInducedEdgeCount
  apply Finset.card_le_card
  apply SimpleGraph.edgeFinset_mono
  exact SimpleGraph.comap_monotone (Function.Embedding.subtype (U : Set V)) hHG

/-- Consequently short-cycle deletion preserves every local-sparsity upper
bound already known for the unpruned graph. -/
theorem shortCyclePrunedGraph_inducedEdgeCount_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) (U : Finset V) :
    deterministicInducedEdgeCount (shortCyclePrunedGraph G L) U ≤
      deterministicInducedEdgeCount G U :=
  deterministicInducedEdgeCount_mono (shortCyclePrunedGraph_le G L) U

/-- Short-cycle deletion also preserves a maximum-degree bound. -/
theorem shortCyclePrunedGraph_degree_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) (v : V) :
    (shortCyclePrunedGraph G L).degree v ≤ G.degree v :=
  SimpleGraph.degree_le_of_le (shortCyclePrunedGraph_le G L)

namespace DeterministicPlantWitness

/-- Logarithmic girth is unchanged when the plant is padded by isolated
ambient vertices. -/
theorem ambientGraph_girth
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    HasRealGirthAtLeast (W.ambientGraph hr n)
      (W.kappa * Real.log (n : ℝ)) := by
  unfold ambientGraph
  exact (W.girth n).map (ambientEmbedding hr n)

/-- The local-sparsity certificate transports to every ambient vertex set,
including sets containing isolated padding vertices. -/
theorem ambientGraph_localSparsity
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (n : ℕ) (hn : 2 ≤ n)
    (U : Finset (Fin n)) (hUtwo : 2 ≤ U.card)
    (hUsize : (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma) :
    (deterministicInducedEdgeCount (W.ambientGraph hr n) U : ℝ) ≤
      (1 + W.A / Real.log (n : ℝ)) * (U.card : ℝ) := by
  classical
  let f := ambientEmbedding hr n
  let P := embeddingPreimageFinset f U
  have hPcard : P.card ≤ U.card := card_embeddingPreimageFinset_le f U
  have hPcardReal : (P.card : ℝ) ≤ (U.card : ℝ) := by
    exact_mod_cast hPcard
  have hnReal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnReal
  have hcoefficient : 0 ≤ 1 + W.A / Real.log (n : ℝ) := by
    have : 0 ≤ W.A / Real.log (n : ℝ) :=
      div_nonneg W.A_pos.le hlog.le
    linarith
  rw [ambientGraph, deterministicInducedEdgeCount_map]
  change (deterministicInducedEdgeCount (W.graph n) P : ℝ) ≤ _
  by_cases hPtwo : 2 ≤ P.card
  · have hPsize : (P.card : ℝ) ≤
        (appendixPlantSize r n : ℝ) ^ gamma :=
      hPcardReal.trans hUsize
    calc
      (deterministicInducedEdgeCount (W.graph n) P : ℝ) ≤
          (1 + W.A / Real.log (n : ℝ)) * (P.card : ℝ) :=
        W.localSparsity n hn P hPtwo hPsize
      _ ≤ (1 + W.A / Real.log (n : ℝ)) * (U.card : ℝ) :=
        mul_le_mul_of_nonneg_left hPcardReal hcoefficient
  · have hPsmall : P.card < 2 := Nat.lt_of_not_ge hPtwo
    have hedgeBound :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := (W.graph n).induce (P : Set (Fin (appendixPlantSize r n))))
    have hzero : deterministicInducedEdgeCount (W.graph n) P = 0 := by
      unfold deterministicInducedEdgeCount
      have hsubtype : Fintype.card {v // v ∈ (P : Set (Fin (appendixPlantSize r n)))} =
          P.card := Fintype.card_coe P
      have hsubsmall :
          Fintype.card {v // v ∈ (P : Set (Fin (appendixPlantSize r n)))} < 2 := by
        rw [hsubtype]
        exact hPsmall
      have hchoose :
          (Fintype.card {v // v ∈ (P : Set (Fin (appendixPlantSize r n)))}).choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt hsubsmall
      rw [hchoose] at hedgeBound
      exact Nat.eq_zero_of_le_zero hedgeBound
    rw [hzero, Nat.cast_zero]
    exact mul_nonneg hcoefficient (Nat.cast_nonneg U.card)

end DeterministicPlantWitness

end

end LowDegree
