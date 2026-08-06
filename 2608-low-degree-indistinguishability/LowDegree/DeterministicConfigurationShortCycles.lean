import LowDegree.DeterministicConfigurationLocalSparsity
import LowDegree.Asymptotics.PercolatedAcyclic
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Short cycles in the finite configuration model

This module formalizes the labelled-cycle first-moment argument in Appendix
Lemma A.5.  A cycle presentation consists of an injective cyclic list of
vertices and an ordered pair of distinct sockets at every vertex.  The
normalization by `2 * ell` removes the choice of root and orientation.

The only pairing input used below is the probability of a prescribed family
of disjoint pairs.  It is stated as an explicit hypothesis in the generic
first-moment lemmas, so that the finite pairing-count theorem can remain in
the configuration-probability module where it is also used by Appendix A.4.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- An ordered pair of distinct sockets at one vertex. -/
abbrev DistinctSocketPair (D : ℕ) :=
  {p : Fin D × Fin D // p ∈ (Finset.univ : Finset (Fin D)).offDiag}

/-- A rooted, oriented, labelled presentation of a length-`ell` cycle. -/
abbrev ConfigurationCyclePresentation (m D ell : ℕ) :=
  (Fin ell ↪ Fin m) × (Fin ell → DistinctSocketPair D)

namespace ConfigurationCyclePresentation

variable {m D ell : ℕ}

/-- The outgoing half-edge at the current vertex. -/
def leftEndpoint (w : ConfigurationCyclePresentation m D ell) (i : Fin ell) :
    ConfigurationHalfEdge m D :=
  (w.1 i, (w.2 i).1.2)

/-- The incoming half-edge at the next vertex in the cyclic order. -/
def rightEndpoint (w : ConfigurationCyclePresentation m D ell) (i : Fin ell) :
    ConfigurationHalfEdge m D :=
  (w.1 (finRotate ell i), (w.2 (finRotate ell i)).1.1)

/-- Package the `2 * ell` endpoints into one map. -/
def endpoint (w : ConfigurationCyclePresentation m D ell) :
    (Fin ell ⊕ Fin ell) → ConfigurationHalfEdge m D
  | Sum.inl i => w.leftEndpoint i
  | Sum.inr i => w.rightEndpoint i

theorem socket_ne (w : ConfigurationCyclePresentation m D ell) (i : Fin ell) :
    (w.2 i).1.1 ≠ (w.2 i).1.2 := by
  exact (Finset.mem_offDiag.mp (w.2 i).2).2.2

/-- Distinct vertices and distinct incoming/outgoing sockets imply that all
half-edges used by a cycle presentation are distinct. -/
theorem endpoint_injective (w : ConfigurationCyclePresentation m D ell) :
    Function.Injective w.endpoint := by
  intro a b hab
  rcases a with i | i <;> rcases b with j | j
  · congr 1
    exact w.1.injective (congrArg Prod.fst hab)
  · exfalso
    have hv : i = finRotate ell j :=
      w.1.injective (congrArg Prod.fst hab)
    have hs : (w.2 i).1.2 =
        (w.2 (finRotate ell j)).1.1 := congrArg Prod.snd hab
    rw [hv] at hs
    exact (w.socket_ne (finRotate ell j)) hs.symm
  · exfalso
    have hv : finRotate ell i = j :=
      w.1.injective (congrArg Prod.fst hab)
    have hs : (w.2 (finRotate ell i)).1.1 =
        (w.2 j).1.2 := congrArg Prod.snd hab
    rw [← hv] at hs
    exact (w.socket_ne (finRotate ell i)) hs
  · congr 1
    exact (finRotate ell).injective
      (w.1.injective (congrArg Prod.fst hab))

/-- Ordered pairs of half-edges prescribed by the cycle presentation. -/
def pairs (w : ConfigurationCyclePresentation m D ell) :
    List (ConfigurationHalfEdge m D × ConfigurationHalfEdge m D) :=
  List.ofFn fun i ↦ (w.leftEndpoint i, w.rightEndpoint i)

@[simp] theorem length_pairs (w : ConfigurationCyclePresentation m D ell) :
    w.pairs.length = ell := by
  simp [pairs]

/-- All endpoints in the prescribed cycle pairs are distinct. -/
theorem prescribedPairEndpoints_pairs_nodup
    (w : ConfigurationCyclePresentation m D ell) :
    (prescribedPairEndpoints w.pairs).Nodup := by
  rw [prescribedPairEndpoints, List.nodup_flatMap]
  constructor
  · intro p hp
    rw [pairs, List.mem_ofFn'] at hp
    rcases hp with ⟨i, rfl⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, List.nodup_nil, and_true]
    constructor
    · intro heq
      exact Sum.noConfusion
        (w.endpoint_injective (show w.endpoint (Sum.inl i) =
          w.endpoint (Sum.inr i) by exact heq))
    · simp
  · rw [pairs, List.pairwise_ofFn]
    intro i j hij
    unfold Function.onFun
    rw [List.disjoint_left]
    intro x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with hxi | hxi <;> rcases hy with hxj | hxj
    · have hs : Sum.inl i = Sum.inl j := w.endpoint_injective
        (show w.endpoint (Sum.inl i) = w.endpoint (Sum.inl j) by
          exact hxi.symm.trans hxj)
      have : i = j := Sum.inl_injective hs
      exact hij.ne this
    · have hcontra := w.endpoint_injective
        (show w.endpoint (Sum.inl i) = w.endpoint (Sum.inr j) by
          exact hxi.symm.trans hxj)
      exact Sum.noConfusion hcontra
    · have hcontra := w.endpoint_injective
        (show w.endpoint (Sum.inr i) = w.endpoint (Sum.inl j) by
          exact hxi.symm.trans hxj)
      exact Sum.noConfusion hcontra
    · have hs : Sum.inr i = Sum.inr j := w.endpoint_injective
        (show w.endpoint (Sum.inr i) = w.endpoint (Sum.inr j) by
          exact hxi.symm.trans hxj)
      have : i = j := Sum.inr_injective hs
      exact hij.ne this

/-- The event that all prescribed pairs of a cycle presentation occur in a
permutation-conjugated configuration. -/
noncomputable def event
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    (w : ConfigurationCyclePresentation m D ell) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m D)) :=
  FiniteLaw.event fun sigma ↦
    ∀ i, conjugatedPartner pairing sigma (w.leftEndpoint i) =
      w.rightEndpoint i

/-- The cycle event is exactly the simultaneous prescribed-pair event used
by the general configuration counting theorem. -/
theorem event_eq_conjugatePairsEvent
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    (w : ConfigurationCyclePresentation m D ell) :
    w.event pairing = conjugatePairsEvent pairing w.pairs := by
  ext sigma
  rw [event, FiniteLaw.mem_event, mem_conjugatePairsEvent]
  constructor
  · intro hsigma p hp
    rw [pairs, List.mem_ofFn'] at hp
    rcases hp with ⟨i, rfl⟩
    exact hsigma i
  · intro hsigma i
    exact hsigma (w.leftEndpoint i, w.rightEndpoint i) (by
      rw [pairs, List.mem_ofFn']
      exact ⟨i, rfl⟩)

@[simp] theorem mem_event
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    (w : ConfigurationCyclePresentation m D ell)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    sigma ∈ w.event pairing ↔
      ∀ i, conjugatedPartner pairing sigma (w.leftEndpoint i) =
        w.rightEndpoint i := by
  simp [event]

end ConfigurationCyclePresentation

/-! ## From projected simple cycles to pairing presentations -/

theorem cycleGraph_adj_finRotate {ell : ℕ} (hell : 3 ≤ ell) (i : Fin ell) :
    (SimpleGraph.cycleGraph ell).Adj i (finRotate ell i) := by
  obtain ⟨k, rfl⟩ : ∃ k, ell = k + 3 := ⟨ell - 3, by omega⟩
  rw [finRotate_succ_apply, SimpleGraph.cycleGraph_adj']
  right
  simp

theorem finRotate_ne_finRotate_symm {ell : ℕ} (hell : 3 ≤ ell) (i : Fin ell) :
    finRotate ell i ≠ (finRotate ell).symm i := by
  obtain ⟨k, rfl⟩ : ∃ k, ell = k + 3 := ⟨ell - 3, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_symm_apply]
  intro heq
  have hcard :
      ({i - 1, i + 1} : Finset (Fin (k + 3))).card = 2 := by
    rw [← SimpleGraph.cycleGraph_degree_two_le]
    exact SimpleGraph.cycleGraph_degree_three_le
  rw [heq] at hcard
  simp at hcard

namespace Configuration

variable {m D ell : ℕ}

/-- Outgoing socket chosen from the projected adjacency supplied by a copy
of a cycle. -/
noncomputable def cycleCopyOutgoingSocket
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph)
    (i : Fin ell) : Fin D :=
  Classical.choose ((C.projectedGraph_adj (f i) (f (finRotate ell i))).mp
    (f.toHom.map_rel (cycleGraph_adj_finRotate hell i))).2

theorem cycleCopyOutgoingSocket_neighbor
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph)
    (i : Fin ell) :
    C.socketNeighbor (f i) (C.cycleCopyOutgoingSocket hell f i) =
      f (finRotate ell i) :=
  Classical.choose_spec ((C.projectedGraph_adj (f i) (f (finRotate ell i))).mp
    (f.toHom.map_rel (cycleGraph_adj_finRotate hell i))).2

/-- Incoming socket at `i`, read from the configuration pair exposed by the
outgoing socket at the preceding cyclic vertex. -/
noncomputable def cycleCopyIncomingSocket
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph)
    (i : Fin ell) : Fin D :=
  (C.partner
    (f ((finRotate ell).symm i),
      C.cycleCopyOutgoingSocket hell f ((finRotate ell).symm i))).2

theorem cycleCopyIncomingSocket_ne_outgoingSocket
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph)
    (i : Fin ell) :
    C.cycleCopyIncomingSocket hell f i ≠ C.cycleCopyOutgoingSocket hell f i := by
  intro heq
  let pred := (finRotate ell).symm i
  let hout := C.cycleCopyOutgoingSocket hell f pred
  have hpairPredFirst :
      (C.partner (f pred, hout)).1 = f i := by
    change C.socketNeighbor (f pred) hout = f i
    simpa [pred, hout] using C.cycleCopyOutgoingSocket_neighbor hell f pred
  have hpairPred :
      C.partner (f pred, hout) =
        (f i, C.cycleCopyIncomingSocket hell f i) := by
    apply Prod.ext
    · exact hpairPredFirst
    · rfl
  have hreverse :
      C.partner (f i, C.cycleCopyOutgoingSocket hell f i) =
        (f pred, hout) := by
    rw [← heq, ← hpairPred, C.partner_involutive]
  have hsuccessor :
      (C.partner (f i, C.cycleCopyOutgoingSocket hell f i)).1 =
        f (finRotate ell i) :=
    C.cycleCopyOutgoingSocket_neighbor hell f i
  have hv : f (finRotate ell i) = f pred := by
    rw [← hsuccessor, hreverse]
  have hi : finRotate ell i = pred := f.injective hv
  exact finRotate_ne_finRotate_symm hell i (by simpa [pred] using hi)

/-- A projected simple cycle determines a pairing presentation realized by
the underlying configuration. -/
noncomputable def cyclePresentationOfCopy
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph) :
    ConfigurationCyclePresentation m D ell :=
  ⟨f.toEmbedding, fun i ↦
    ⟨(C.cycleCopyIncomingSocket hell f i,
        C.cycleCopyOutgoingSocket hell f i), by
      rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_univ _, Finset.mem_univ _,
        C.cycleCopyIncomingSocket_ne_outgoingSocket hell f i⟩⟩⟩

/-- The presentation extracted from a cycle copy is realized by `C`. -/
theorem cyclePresentationOfCopy_realized
    (C : Configuration m D) (hell : 3 ≤ ell)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph ell) C.projectedGraph) :
    ∀ i,
      C.partner ((C.cyclePresentationOfCopy hell f).leftEndpoint i) =
        (C.cyclePresentationOfCopy hell f).rightEndpoint i := by
  intro i
  apply Prod.ext
  · change C.socketNeighbor (f i) (C.cycleCopyOutgoingSocket hell f i) =
      f (finRotate ell i)
    exact C.cycleCopyOutgoingSocket_neighbor hell f i
  · change
      (C.partner (f i, C.cycleCopyOutgoingSocket hell f i)).2 =
        (C.partner
          (f ((finRotate ell).symm (finRotate ell i)),
            C.cycleCopyOutgoingSocket hell f
              ((finRotate ell).symm (finRotate ell i)))).2
    simp

end Configuration

/-- Every edge in a walk occurs between two consecutive indexed vertices. -/
theorem SimpleGraph.Walk.exists_eq_getVert_edge
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ i, i < p.length ∧ e = s(p.getVert i, p.getVert (i + 1)) := by
  induction p with
  | nil => simp at he
  | @cons u v w huv p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨0, by simp, by simp⟩
      · rcases ih he with ⟨i, hi, hei⟩
        refine ⟨i + 1, by simp; omega, ?_⟩
        simpa [SimpleGraph.Walk.getVert] using hei

/-- Moving one step with `finRotate` reads the next vertex of a closed walk,
including the wrap from the last position back to the start. -/
theorem coe_finRotate_eq_if_of_pos
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [coe_finRotate]
      by_cases hi : i = Fin.last k
      · simp [hi]
      · have hiv : i.val + 1 ≠ k + 1 := by
          intro h
          apply hi
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        have hnotLastVal : i.val ≠ k := by
          intro h
          apply hi
          apply Fin.ext
          simpa only [Fin.val_last]
        simp [hi, hnotLastVal]

theorem SimpleGraph.Walk.getVert_finRotate
    {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (i : Fin p.length) :
    p.getVert (finRotate p.length i).val = p.getVert (i.val + 1) := by
  have hlen : 0 < p.length := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [coe_finRotate_eq_if_of_pos hlen]
  split_ifs with hi
  · rw [hi, p.getVert_length, p.getVert_zero]
  · rfl

/-- The simple edges traversed by a rooted oriented presentation. -/
noncomputable def cyclePresentationEdges
    (w : ConfigurationCyclePresentation m D ell) : Finset (Sym2 (Fin m)) :=
  Finset.univ.image fun i ↦ s(w.1 i, w.1 (finRotate ell i))

theorem card_cyclePresentationEdges_le
    (w : ConfigurationCyclePresentation m D ell) :
    (cyclePresentationEdges w).card ≤ ell := by
  exact (Finset.card_image_le.trans_eq (by simp))

/-- Edges covered by all realized length-`ell` presentations. -/
noncomputable def realizedCyclePresentationEdges
    (C : Configuration m D) (ell : ℕ) : Finset (Sym2 (Fin m)) :=
  Finset.univ.biUnion fun w : ConfigurationCyclePresentation m D ell ↦
    if (∀ i, C.partner (w.leftEndpoint i) = w.rightEndpoint i) then
      cyclePresentationEdges w
    else ∅

/-- Union of all realized presentation edges at lengths `3 ≤ ell < L`. -/
noncomputable def realizedShortCyclePresentationEdges
    (C : Configuration m D) (L : ℕ) : Finset (Sym2 (Fin m)) :=
  (Finset.Ico 3 L).biUnion fun ell ↦ realizedCyclePresentationEdges C ell

/-- Every edge selected by deterministic short-cycle pruning is covered by a
realized configuration presentation of the same cycle. -/
theorem shortCycleEdges_subset_realizedShortCyclePresentationEdges
    (C : Configuration m D) (L : ℕ) :
    shortCycleEdges C.projectedGraph L ⊆
      realizedShortCyclePresentationEdges C L := by
  intro e he
  rw [mem_shortCycleEdges] at he
  rcases he.2 with ⟨v, p, hp, hlen, hep⟩
  have hell3 : 3 ≤ p.length := hp.three_le_length
  let f : SimpleGraph.Copy (SimpleGraph.cycleGraph p.length) C.projectedGraph :=
    PercolatedAcyclic.cycleCopyOfIsCycle hp
  let w : ConfigurationCyclePresentation m D p.length :=
    C.cyclePresentationOfCopy hell3 f
  have hwrealized : ∀ i, C.partner (w.leftEndpoint i) = w.rightEndpoint i :=
    C.cyclePresentationOfCopy_realized hell3 f
  rcases SimpleGraph.Walk.exists_eq_getVert_edge p hep with ⟨i, hi, hei⟩
  let ii : Fin p.length := ⟨i, hi⟩
  have hedge : e = s(w.1 ii, w.1 (finRotate p.length ii)) := by
    rw [hei]
    change s(p.getVert i, p.getVert (i + 1)) =
      s(p.getVert ii.val, p.getVert (finRotate p.length ii).val)
    rw [SimpleGraph.Walk.getVert_finRotate p ii]
  unfold realizedShortCyclePresentationEdges
  rw [Finset.mem_biUnion]
  refine ⟨p.length, Finset.mem_Ico.mpr ⟨hell3, hlen⟩, ?_⟩
  unfold realizedCyclePresentationEdges
  rw [Finset.mem_biUnion]
  refine ⟨w, Finset.mem_univ _, ?_⟩
  rw [if_pos hwrealized]
  unfold cyclePresentationEdges
  rw [Finset.mem_image]
  exact ⟨ii, Finset.mem_univ _, hedge.symm⟩

/-- Number of rooted, oriented length-`ell` cycle presentations realized by
one relabelled configuration, represented as a real number. -/
noncomputable def configurationCyclePresentationCountReal
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) : ℝ :=
  ∑ w : ConfigurationCyclePresentation m D ell,
    if sigma ∈ w.event pairing then 1 else 0

/-- The distinct-vertex cycle count, with the standard `2 ell` quotient for
choice of root and orientation.  For `ell = 0` the value is defined as zero;
the Appendix only sums lengths at least three. -/
noncomputable def configurationDistinctVertexCycleCountReal
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) : ℝ :=
  configurationCyclePresentationCountReal pairing ell sigma / (2 * ell : ℕ)

/-- Total number of distinct-vertex cycles whose lengths lie between three
and the cutoff `h`. -/
noncomputable def configurationShortCycleCountReal
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (h : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) : ℝ :=
  ∑ ell ∈ Finset.Icc 3 h,
    configurationDistinctVertexCycleCountReal pairing ell sigma

/-- Evaluating the presentation count of a sampled configuration at the
identity relabelling is the same as evaluating the canonical pairing at the
sampling permutation. -/
theorem configurationCyclePresentationCountReal_randomConfiguration_refl
    (m d ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    configurationCyclePresentationCountReal
        (randomConfiguration m d sigma).partner ell (Equiv.refl _) =
      configurationCyclePresentationCountReal
        (Configuration.standardConfiguration m d).partner ell sigma := by
  unfold configurationCyclePresentationCountReal
  apply Finset.sum_congr rfl
  intro w _hw
  congr 1
  rw [w.mem_event, w.mem_event]
  simp [randomConfiguration, Configuration.ofPermutation,
    Configuration.relabel, conjugatedPartner]

/-- The corresponding identification for the normalized short-cycle count. -/
theorem configurationShortCycleCountReal_randomConfiguration_refl
    (m d h : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    configurationShortCycleCountReal
        (randomConfiguration m d sigma).partner h (Equiv.refl _) =
      configurationShortCycleCountReal
        (Configuration.standardConfiguration m d).partner h sigma := by
  unfold configurationShortCycleCountReal
  apply Finset.sum_congr rfl
  intro ell _hell
  unfold configurationDistinctVertexCycleCountReal
  rw [configurationCyclePresentationCountReal_randomConfiguration_refl]

theorem configurationCyclePresentationCountReal_nonneg
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    0 ≤ configurationCyclePresentationCountReal pairing ell sigma := by
  unfold configurationCyclePresentationCountReal
  positivity

theorem configurationDistinctVertexCycleCountReal_nonneg
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    0 ≤ configurationDistinctVertexCycleCountReal pairing ell sigma := by
  unfold configurationDistinctVertexCycleCountReal
  exact div_nonneg
    (configurationCyclePresentationCountReal_nonneg pairing ell sigma)
    (Nat.cast_nonneg _)

theorem configurationShortCycleCountReal_nonneg
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (h : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    0 ≤ configurationShortCycleCountReal pairing h sigma := by
  unfold configurationShortCycleCountReal
  exact Finset.sum_nonneg fun ell _ ↦
    configurationDistinctVertexCycleCountReal_nonneg pairing ell sigma

/-! ## Deterministic edge-count bridge -/

/-- The union of edges in realized presentations is bounded by the number
of presentations times their common length. -/
theorem card_realizedCyclePresentationEdges_cast_le
    (C : Configuration m D) (ell : ℕ) :
    ((realizedCyclePresentationEdges C ell).card : ℝ) ≤
      (ell : ℝ) *
        configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) := by
  let pieces : ConfigurationCyclePresentation m D ell → Finset (Sym2 (Fin m)) :=
    fun w ↦
      if (∀ i, C.partner (w.leftEndpoint i) = w.rightEndpoint i) then
        cyclePresentationEdges w
      else ∅
  have hcard :
      (realizedCyclePresentationEdges C ell).card ≤
        ∑ w : ConfigurationCyclePresentation m D ell, (pieces w).card := by
    simpa only [realizedCyclePresentationEdges, pieces] using
      (Finset.card_biUnion_le (s :=
        (Finset.univ : Finset (ConfigurationCyclePresentation m D ell)))
        (t := pieces))
  calc
    ((realizedCyclePresentationEdges C ell).card : ℝ) ≤
        ((∑ w : ConfigurationCyclePresentation m D ell,
          (pieces w).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ∑ w : ConfigurationCyclePresentation m D ell,
          ((pieces w).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ w : ConfigurationCyclePresentation m D ell,
          (ell : ℝ) *
            if (Equiv.refl _ : Equiv.Perm (ConfigurationHalfEdge m D)) ∈
                w.event C.partner then 1 else 0 := by
      apply Finset.sum_le_sum
      intro w _hw
      by_cases hw : ∀ i, C.partner (w.leftEndpoint i) = w.rightEndpoint i
      · have hmem :
            (Equiv.refl _ : Equiv.Perm (ConfigurationHalfEdge m D)) ∈
              w.event C.partner := by
          rw [w.mem_event]
          simpa [conjugatedPartner] using hw
        simp only [pieces, if_pos hw, if_pos hmem, mul_one]
        exact_mod_cast card_cyclePresentationEdges_le w
      · have hnotmem :
            (Equiv.refl _ : Equiv.Perm (ConfigurationHalfEdge m D)) ∉
              w.event C.partner := by
          rw [w.mem_event]
          simpa [conjugatedPartner] using hw
        simp [pieces, hw, hnotmem]
    _ = (ell : ℝ) *
        configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) := by
      unfold configurationCyclePresentationCountReal
      rw [Finset.mul_sum]

/-- Sum the preceding presentation bound over all short lengths. -/
theorem card_realizedShortCyclePresentationEdges_cast_le
    (C : Configuration m D) (L : ℕ) :
    ((realizedShortCyclePresentationEdges C L).card : ℝ) ≤
      ∑ ell ∈ Finset.Ico 3 L,
        (ell : ℝ) *
          configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) := by
  have hcard :
      (realizedShortCyclePresentationEdges C L).card ≤
        ∑ ell ∈ Finset.Ico 3 L,
          (realizedCyclePresentationEdges C ell).card := by
    simpa only [realizedShortCyclePresentationEdges] using
      (Finset.card_biUnion_le
        (s := Finset.Ico 3 L)
        (t := fun ell ↦ realizedCyclePresentationEdges C ell))
  calc
    ((realizedShortCyclePresentationEdges C L).card : ℝ) ≤
        ((∑ ell ∈ Finset.Ico 3 L,
          (realizedCyclePresentationEdges C ell).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ ell ∈ Finset.Ico 3 L,
          ((realizedCyclePresentationEdges C ell).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ ell ∈ Finset.Ico 3 L,
        (ell : ℝ) *
          configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) := by
      exact Finset.sum_le_sum fun ell _hell ↦
        card_realizedCyclePresentationEdges_cast_le C ell

/-- Undo the standard `2 ell` quotient at positive cycle lengths. -/
theorem configurationCyclePresentationCountReal_eq_two_mul_length_mul
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) (hell : 0 < ell) :
    configurationCyclePresentationCountReal pairing ell sigma =
      2 * (ell : ℝ) *
        configurationDistinctVertexCycleCountReal pairing ell sigma := by
  unfold configurationDistinctVertexCycleCountReal
  have hden : ((2 * ell : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_eq_mul_inv]
  push_cast
  field_simp

/-- Deterministic bridge used by Appendix A.1: pruning all projected simple
cycles of length at most `h` removes no more than `2 h²` times the normalized
distinct-vertex cycle count.  This deliberately coarse polynomial factor is
harmless at the logarithmic cutoff. -/
theorem shortCycleEdges_card_cast_le_two_mul_sq_mul_shortCycleCountReal
    (C : Configuration m D) (h : ℕ) :
    ((shortCycleEdges C.projectedGraph (h + 1)).card : ℝ) ≤
      2 * (h : ℝ) ^ 2 *
        configurationShortCycleCountReal C.partner h (Equiv.refl _) := by
  have hsubset :=
    shortCycleEdges_subset_realizedShortCyclePresentationEdges C (h + 1)
  have hcard :
      (shortCycleEdges C.projectedGraph (h + 1)).card ≤
        (realizedShortCyclePresentationEdges C (h + 1)).card :=
    Finset.card_le_card hsubset
  have hinterval : Finset.Ico 3 (h + 1) = Finset.Icc 3 h := by
    ext ell
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  calc
    ((shortCycleEdges C.projectedGraph (h + 1)).card : ℝ) ≤
        ((realizedShortCyclePresentationEdges C (h + 1)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ ell ∈ Finset.Ico 3 (h + 1),
        (ell : ℝ) *
          configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) :=
      card_realizedShortCyclePresentationEdges_cast_le C (h + 1)
    _ = ∑ ell ∈ Finset.Icc 3 h,
        (ell : ℝ) *
          configurationCyclePresentationCountReal C.partner ell (Equiv.refl _) := by
      rw [hinterval]
    _ ≤ ∑ ell ∈ Finset.Icc 3 h,
        2 * (h : ℝ) ^ 2 *
          configurationDistinctVertexCycleCountReal C.partner ell (Equiv.refl _) := by
      apply Finset.sum_le_sum
      intro ell hell
      have hellPos : 0 < ell := by
        rw [Finset.mem_Icc] at hell
        omega
      have hellLeNat : ell ≤ h := (Finset.mem_Icc.mp hell).2
      have hellLe : (ell : ℝ) ≤ h := by exact_mod_cast hellLeNat
      have hellNonneg : (0 : ℝ) ≤ ell := by positivity
      have hNonneg : (0 : ℝ) ≤ h := by positivity
      have hsquare : (ell : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 := by nlinarith
      rw [configurationCyclePresentationCountReal_eq_two_mul_length_mul
        C.partner ell (Equiv.refl _) hellPos]
      have hcount := configurationDistinctVertexCycleCountReal_nonneg
        C.partner ell (Equiv.refl _)
      calc
        (ell : ℝ) *
            (2 * (ell : ℝ) *
              configurationDistinctVertexCycleCountReal C.partner ell
                (Equiv.refl _)) =
            (2 * (ell : ℝ) ^ 2) *
              configurationDistinctVertexCycleCountReal C.partner ell
                (Equiv.refl _) := by ring
        _ ≤ (2 * (h : ℝ) ^ 2) *
              configurationDistinctVertexCycleCountReal C.partner ell
                (Equiv.refl _) :=
          mul_le_mul_of_nonneg_right (by linarith) hcount
    _ = 2 * (h : ℝ) ^ 2 *
        configurationShortCycleCountReal C.partner h (Equiv.refl _) := by
      unfold configurationShortCycleCountReal
      rw [Finset.mul_sum]

/-- Exact cardinality of the ordered distinct socket-pair type. -/
theorem card_distinctSocketPair (D : ℕ) :
    Fintype.card (DistinctSocketPair D) = D * (D - 1) := by
  rw [Fintype.card_coe, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.mul_sub_left_distrib]
  simp

/-- Exact number of rooted, oriented cycle presentations. -/
theorem card_configurationCyclePresentation (m D ell : ℕ) :
    Fintype.card (ConfigurationCyclePresentation m D ell) =
      m.descFactorial ell * (D * (D - 1)) ^ ell := by
  rw [Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_pi_const, card_distinctSocketPair]
  simp only [Fintype.card_fin]

/-- Crude presentation count used in the first-moment bound. -/
theorem card_configurationCyclePresentation_le (m D ell : ℕ) :
    Fintype.card (ConfigurationCyclePresentation m D ell) ≤
      m ^ ell * (D * (D - 1)) ^ ell := by
  rw [card_configurationCyclePresentation]
  exact Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow m ell)

/-! ## Exact cycle-presentation probability -/

/-- Exact odd-denominator product for one rooted, oriented cycle
presentation in the even-degree configuration model. -/
theorem configurationPermutationLaw_prob_cyclePresentation_event
    (m d ell : ℕ)
    (w : ConfigurationCyclePresentation m (d + d) ell) :
    (configurationPermutationLaw m d).prob
        (w.event (Configuration.standardConfiguration m d).partner) =
      ((prescribedPairDenominator (m * (d + d)) ell : ℕ) : ℝ)⁻¹ := by
  rw [w.event_eq_conjugatePairsEvent]
  change (configurationPermutationLaw m d).prob
      (configurationPairsEvent m d w.pairs) = _
  simpa only [w.length_pairs] using
    (configurationPermutationLaw_prob_configurationPairsEvent m d w.pairs
      w.prescribedPairEndpoints_pairs_nodup)

/-- Under `4 ell ≤ mD`, the exact product probability is at most
`(2/(mD))^ell`. -/
theorem configurationPermutationLaw_prob_cyclePresentation_event_le
    (m d ell : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hguard : 4 * ell ≤ m * (d + d))
    (w : ConfigurationCyclePresentation m (d + d) ell) :
    (configurationPermutationLaw m d).prob
        (w.event (Configuration.standardConfiguration m d).partner) ≤
      (2 / (m * (d + d) : ℕ) : ℝ) ^ ell := by
  rw [configurationPermutationLaw_prob_cyclePresentation_event]
  let N : ℕ := m * (d + d)
  have hN : 0 < N := by dsimp [N]; positivity
  have hdenNat : 0 < prescribedPairDenominator N ell := by
    have hcard : Fintype.card (ConfigurationHalfEdge m (d + d)) = N := by
      simp [N]
    rw [← hcard]
    simpa only [w.length_pairs] using
      (prescribedPairDenominator_pos w.pairs
        w.prescribedPairEndpoints_pairs_nodup)
  have hden : (0 : ℝ) < prescribedPairDenominator N ell := by
    exact_mod_cast hdenNat
  have hhalf : (0 : ℝ) < ((N : ℝ) / 2) ^ ell := by positivity
  have hinv :
      ((prescribedPairDenominator N ell : ℕ) : ℝ)⁻¹ ≤
        (((N : ℝ) / 2) ^ ell)⁻¹ :=
    (inv_le_inv₀ hden hhalf).2
      (half_card_pow_le_prescribedPairDenominator_cast N ell hguard)
  calc
    ((prescribedPairDenominator (m * (d + d)) ell : ℕ) : ℝ)⁻¹ =
        ((prescribedPairDenominator N ell : ℕ) : ℝ)⁻¹ := by rfl
    _ ≤ (((N : ℝ) / 2) ^ ell)⁻¹ := hinv
    _ = (2 / (m * (d + d) : ℕ) : ℝ) ^ ell := by
      rw [← inv_pow]
      congr 1
      dsimp [N]
      field_simp

/-- Expectation of the presentation count is the sum of the realization
probabilities of the individual presentations. -/
theorem expect_configurationCyclePresentationCountReal
    (q : FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m D)))
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ) :
    q.expect (configurationCyclePresentationCountReal pairing ell) =
      ∑ w : ConfigurationCyclePresentation m D ell, q.prob (w.event pairing) := by
  classical
  unfold configurationCyclePresentationCountReal FiniteLaw.expect FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext sigma
  simp

/-- Generic first-moment bound from a uniform bound on each prescribed
disjoint-pair event. -/
theorem expect_configurationCyclePresentationCountReal_le
    (q : FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m D)))
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (ell : ℕ)
    (pairBound : ℝ)
    (hpair : ∀ w : ConfigurationCyclePresentation m D ell,
      q.prob (w.event pairing) ≤ pairBound) :
    q.expect (configurationCyclePresentationCountReal pairing ell) ≤
      (Fintype.card (ConfigurationCyclePresentation m D ell) : ℝ) * pairBound := by
  rw [expect_configurationCyclePresentationCountReal]
  calc
    (∑ w : ConfigurationCyclePresentation m D ell,
        q.prob (w.event pairing)) ≤ ∑ _w, pairBound :=
      Finset.sum_le_sum fun w _hw ↦ hpair w
    _ = _ := by simp

/-- Divide the presentation first moment by the root/orientation factor. -/
theorem expect_configurationDistinctVertexCycleCountReal_le
    (q : FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m D)))
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    {ell : ℕ} (hell : 0 < ell) (pairBound : ℝ)
    (hpair : ∀ w : ConfigurationCyclePresentation m D ell,
      q.prob (w.event pairing) ≤ pairBound) :
    q.expect (configurationDistinctVertexCycleCountReal pairing ell) ≤
      ((Fintype.card (ConfigurationCyclePresentation m D ell) : ℝ) * pairBound) /
        (2 * ell : ℕ) := by
  have hden : (0 : ℝ) < (2 * ell : ℕ) := by positivity
  have heq :
      q.expect (configurationDistinctVertexCycleCountReal pairing ell) =
        q.expect (configurationCyclePresentationCountReal pairing ell) /
          (2 * ell : ℕ) := by
    unfold configurationDistinctVertexCycleCountReal FiniteLaw.expect
    calc
      (∑ sigma, q.mass sigma *
          (configurationCyclePresentationCountReal pairing ell sigma /
            (2 * ell : ℕ))) =
          ∑ sigma, (q.mass sigma *
            configurationCyclePresentationCountReal pairing ell sigma) /
              (2 * ell : ℕ) := by
        apply Finset.sum_congr rfl
        intro sigma _hsigma
        ring
      _ = (∑ sigma, q.mass sigma *
          configurationCyclePresentationCountReal pairing ell sigma) /
            (2 * ell : ℕ) := by
        simpa only [Finset.sum_const_zero] using
          (Finset.sum_div
            (s := (Finset.univ : Finset
              (Equiv.Perm (ConfigurationHalfEdge m D))))
            (f := fun sigma ↦ q.mass sigma *
              configurationCyclePresentationCountReal pairing ell sigma)
            (a := ((2 * ell : ℕ) : ℝ))).symm
  rw [heq]
  exact div_le_div_of_nonneg_right
    (expect_configurationCyclePresentationCountReal_le
      q pairing ell pairBound hpair) hden.le

/-- Sum the fixed-length first-moment estimates over all short lengths. -/
theorem expect_configurationShortCycleCountReal_le
    (q : FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m D)))
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (h : ℕ)
    (pairBound : ℕ → ℝ)
    (hpair : ∀ ell, ell ∈ Finset.Icc 3 h →
      ∀ w : ConfigurationCyclePresentation m D ell,
        q.prob (w.event pairing) ≤ pairBound ell) :
    q.expect (configurationShortCycleCountReal pairing h) ≤
      ∑ ell ∈ Finset.Icc 3 h,
        ((Fintype.card (ConfigurationCyclePresentation m D ell) : ℝ) *
          pairBound ell) / (2 * ell : ℕ) := by
  unfold configurationShortCycleCountReal FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ell hell
  have hellpos : 0 < ell := (Finset.mem_Icc.mp hell).1.trans' (by norm_num)
  simpa only [FiniteLaw.expect] using
    expect_configurationDistinctVertexCycleCountReal_le
      q pairing hellpos (pairBound ell) (hpair ell hell)

/-! ## The Appendix A.5 first-moment envelope -/

/-- Cardinality and prescribed-pair probability combine to give the paper's
geometric factor `K_D = 2(D-1)`. -/
theorem cyclePresentation_firstMomentTerm_le
    (m d ell : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (Fintype.card (ConfigurationCyclePresentation m (d + d) ell) : ℝ) *
        (2 / (m * (d + d) : ℕ) : ℝ) ^ ell ≤
      ((2 * ((d + d) - 1) : ℕ) : ℝ) ^ ell := by
  let D : ℕ := d + d
  have hD : 0 < D := by dsimp [D]; omega
  have hcard :
      (Fintype.card (ConfigurationCyclePresentation m D ell) : ℝ) ≤
        ((m ^ ell * (D * (D - 1)) ^ ell : ℕ) : ℝ) := by
    exact_mod_cast card_configurationCyclePresentation_le m D ell
  calc
    (Fintype.card (ConfigurationCyclePresentation m (d + d) ell) : ℝ) *
          (2 / (m * (d + d) : ℕ) : ℝ) ^ ell ≤
        ((m ^ ell * (D * (D - 1)) ^ ell : ℕ) : ℝ) *
          (2 / (m * D : ℕ) : ℝ) ^ ell := by
      dsimp [D] at hcard ⊢
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((2 * (D - 1) : ℕ) : ℝ) ^ ell := by
      push_cast
      rw [Nat.cast_sub hD]
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp
    _ = ((2 * ((d + d) - 1) : ℕ) : ℝ) ^ ell := by rfl

/-- Fixed-length expected cycle count in the form displayed in Appendix
A.5.  The theorem is valid also for lengths one and two; A.5 itself uses
only lengths at least three. -/
theorem configurationPermutationLaw_expect_distinctVertexCycleCount_le
    (m d ell : ℕ) (hm : 0 < m) (hd : 0 < d) (hell : 0 < ell)
    (hguard : 4 * ell ≤ m * (d + d)) :
    (configurationPermutationLaw m d).expect
        (configurationDistinctVertexCycleCountReal
          (Configuration.standardConfiguration m d).partner ell) ≤
      ((2 * ((d + d) - 1) : ℕ) : ℝ) ^ ell / (2 * ell : ℕ) := by
  have hraw := expect_configurationDistinctVertexCycleCountReal_le
    (configurationPermutationLaw m d)
    (Configuration.standardConfiguration m d).partner hell
    ((2 / (m * (d + d) : ℕ) : ℝ) ^ ell)
    (fun w ↦ configurationPermutationLaw_prob_cyclePresentation_event_le
      m d ell hm hd hguard w)
  exact hraw.trans (div_le_div_of_nonneg_right
    (cyclePresentation_firstMomentTerm_le m d ell hm hd)
    (Nat.cast_nonneg _))

/-- Sum the fixed-length estimates over all lengths from three through `h`.
-/
theorem configurationPermutationLaw_expect_shortCycleCount_le_powerSum
    (m d h : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hguard : 4 * h ≤ m * (d + d)) :
    (configurationPermutationLaw m d).expect
        (configurationShortCycleCountReal
          (Configuration.standardConfiguration m d).partner h) ≤
      ∑ ell ∈ Finset.Icc 3 h,
        ((2 * ((d + d) - 1) : ℕ) : ℝ) ^ ell / (2 * ell : ℕ) := by
  let K : ℕ := 2 * ((d + d) - 1)
  have hfirst := expect_configurationShortCycleCountReal_le
    (configurationPermutationLaw m d)
    (Configuration.standardConfiguration m d).partner h
    (fun ell ↦ (2 / (m * (d + d) : ℕ) : ℝ) ^ ell)
    (fun ell hell w ↦
      configurationPermutationLaw_prob_cyclePresentation_event_le
        m d ell hm hd (by
          have hellh := (Finset.mem_Icc.mp hell).2
          omega) w)
  refine hfirst.trans (Finset.sum_le_sum fun ell hell ↦ ?_)
  exact div_le_div_of_nonneg_right
    (cyclePresentation_firstMomentTerm_le m d ell hm hd)
    (Nat.cast_nonneg _)

/-- A simple envelope for the geometric cycle-length sum. -/
theorem cyclePowerDivSum_le_envelope (K h : ℕ) (hK : 1 ≤ K) :
    (∑ ell ∈ Finset.Icc 3 h,
        (K : ℝ) ^ ell / (2 * ell : ℕ)) ≤
      (h + 1 : ℕ) * (K : ℝ) ^ h := by
  have hterm : ∀ ell ∈ Finset.Icc 3 h,
      (K : ℝ) ^ ell / (2 * ell : ℕ) ≤ (K : ℝ) ^ h := by
    intro ell hell
    have hell3 : 3 ≤ ell := (Finset.mem_Icc.mp hell).1
    have hdenNat : 1 ≤ 2 * ell := by omega
    have hden : (1 : ℝ) ≤ (2 * ell : ℕ) := by
      exact_mod_cast hdenNat
    have hKReal : (1 : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hK
    calc
      (K : ℝ) ^ ell / (2 * ell : ℕ) ≤ (K : ℝ) ^ ell :=
        div_le_self (pow_nonneg (Nat.cast_nonneg K) ell) hden
      _ ≤ (K : ℝ) ^ h :=
        pow_le_pow_right₀ hKReal (Finset.mem_Icc.mp hell).2
  calc
    (∑ ell ∈ Finset.Icc 3 h,
        (K : ℝ) ^ ell / (2 * ell : ℕ)) ≤
        ∑ _ell ∈ Finset.Icc 3 h, (K : ℝ) ^ h :=
      Finset.sum_le_sum hterm
    _ = ((Finset.Icc 3 h).card : ℝ) * (K : ℝ) ^ h := by simp
    _ ≤ (h + 1 : ℕ) * (K : ℝ) ^ h := by
      gcongr
      exact_mod_cast (show (Finset.Icc 3 h).card ≤ h + 1 by simp; omega)

/-- Fixed-size expectation estimate used by Markov's inequality in A.5. -/
theorem configurationPermutationLaw_expect_shortCycleCount_le_envelope
    (m d h : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hguard : 4 * h ≤ m * (d + d)) :
    (configurationPermutationLaw m d).expect
        (configurationShortCycleCountReal
          (Configuration.standardConfiguration m d).partner h) ≤
      (h + 1 : ℕ) *
        ((2 * ((d + d) - 1) : ℕ) : ℝ) ^ h := by
  exact (configurationPermutationLaw_expect_shortCycleCount_le_powerSum
    m d h hm hd hguard).trans
      (cyclePowerDivSum_le_envelope (2 * ((d + d) - 1)) h (by omega))

/-- Markov's inequality converts a first-moment estimate into the probability
bound used by Appendix A.5. -/
theorem configurationShortCycleCount_probability_gt_le
    (q : FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m D)))
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D)) (h : ℕ)
    {threshold expectationBound : ℝ} (hthreshold : 0 < threshold)
    (hexpect : q.expect (configurationShortCycleCountReal pairing h) ≤
      expectationBound) :
    q.prob (FiniteLaw.event fun sigma ↦
        threshold ≤ configurationShortCycleCountReal pairing h sigma) ≤
      expectationBound / threshold := by
  exact (q.markov (configurationShortCycleCountReal pairing h)
    (configurationShortCycleCountReal_nonneg pairing h) hthreshold).trans
      (div_le_div_of_nonneg_right hexpect hthreshold.le)

/-! ## The logarithmic cutoff in Appendix A.5 -/

/-- The geometric factor `K_D=2(D-1)` for the even degree `D=2d`. -/
def deterministicConfigurationCycleFactor (d : ℕ) : ℕ :=
  2 * ((d + d) - 1)

/-- The paper's cutoff `floor(log m / (2 log K_D))`. -/
noncomputable def deterministicConfigurationCycleCutoff (d m : ℕ) : ℕ :=
  ⌊Real.log (m : ℝ) /
    (2 * Real.log (deterministicConfigurationCycleFactor d : ℝ))⌋₊

theorem deterministicConfigurationCycleFactor_one_lt
    {d : ℕ} (hd : 1 ≤ d) :
    1 < deterministicConfigurationCycleFactor d := by
  unfold deterministicConfigurationCycleFactor
  omega

/-- The natural floor is below its defining logarithmic ratio. -/
theorem deterministicConfigurationCycleCutoff_le_logRatio
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (deterministicConfigurationCycleCutoff d m : ℝ) ≤
      Real.log (m : ℝ) /
        (2 * Real.log (deterministicConfigurationCycleFactor d : ℝ)) := by
  apply Nat.floor_le
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm))
    (mul_nonneg (by norm_num)
      (Real.log_nonneg (by
        exact_mod_cast (deterministicConfigurationCycleFactor_one_lt hd).le)))

/-- At the paper cutoff, the geometric factor is at most `sqrt m`. -/
theorem deterministicConfigurationCycleFactor_pow_cutoff_le_sqrt
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (deterministicConfigurationCycleFactor d : ℝ) ^
        deterministicConfigurationCycleCutoff d m ≤
      (m : ℝ) ^ (1 / 2 : ℝ) := by
  let K : ℝ := deterministicConfigurationCycleFactor d
  have hKone : 1 < K := by
    dsimp [K]
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt hd
  have hKpos : 0 < K := zero_lt_one.trans hKone
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hexp :
      (deterministicConfigurationCycleCutoff d m : ℝ) ≤
        Real.log (m : ℝ) / (2 * Real.log K) := by
    simpa only [K] using deterministicConfigurationCycleCutoff_le_logRatio hd hm
  have hpow := Real.rpow_le_rpow_of_exponent_le hKone.le hexp
  rw [Real.rpow_natCast] at hpow
  refine hpow.trans_eq ?_
  rw [Real.rpow_def_of_pos hKpos, Real.rpow_def_of_pos hmpos]
  congr 1
  have hlogK : Real.log K ≠ 0 := (Real.log_pos hKone).ne'
  field_simp

/-- The Markov step in A.5, abstracted over a size sequence and cutoff.
The displayed growth hypothesis is discharged for the paper's logarithmic
cutoff below. -/
theorem configurationShortCycleCount_badProbability_vanishes_of_envelope
    (d : ℕ) (hd : 0 < d) (m h : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hguard : ∀ᶠ n in atTop, 4 * h n ≤ m n * (d + d))
    (hgrowth : Vanishes fun n ↦
      (((h n + 1 : ℕ) : ℝ) *
          (deterministicConfigurationCycleFactor d : ℝ) ^ h n) /
        (m n : ℝ) ^ (3 / 4 : ℝ)) :
    Vanishes fun n ↦
      (configurationPermutationLaw (m n) d).prob
        (FiniteLaw.event fun sigma ↦
          (m n : ℝ) ^ (3 / 4 : ℝ) ≤
            configurationShortCycleCountReal
              (Configuration.standardConfiguration (m n) d).partner (h n) sigma) := by
  have hmpos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      (configurationPermutationLaw (m n) d).prob_nonneg _
  · filter_upwards [hmpos, hguard] with n hmn hgn
    apply configurationShortCycleCount_probability_gt_le
      (configurationPermutationLaw (m n) d)
      (Configuration.standardConfiguration (m n) d).partner (h n)
      (Real.rpow_pos_of_pos (by exact_mod_cast hmn) _)
    simpa only [deterministicConfigurationCycleFactor] using
      configurationPermutationLaw_expect_shortCycleCount_le_envelope
        (m n) d (h n) hmn hd hgn
  · exact hgrowth

/-- The explicit A.5 envelope at the logarithmic cutoff vanishes relative
to `m^(3/4)` for every size sequence tending to infinity. -/
theorem deterministicConfigurationCycleCutoff_envelope_vanishes
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (((deterministicConfigurationCycleCutoff d (m n) + 1 : ℕ) : ℝ) *
          (deterministicConfigurationCycleFactor d : ℝ) ^
            deterministicConfigurationCycleCutoff d (m n)) /
        (m n : ℝ) ^ (3 / 4 : ℝ) := by
  let K : ℝ := deterministicConfigurationCycleFactor d
  have hKone : 1 < K := by
    dsimp [K]
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt hd
  have hlogK : 0 < Real.log K := Real.log_pos hKone
  have hmReal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hlogBase : Vanishes fun n ↦
      Real.log (m n : ℝ) / (m n : ℝ) ^ (1 / 4 : ℝ) :=
    (isLittleO_log_rpow_atTop hquarter).tendsto_div_nhds_zero.comp hmReal
  have hlogScaled : Vanishes fun n ↦
      (Real.log (m n : ℝ) /
          (2 * Real.log K)) / (m n : ℝ) ^ (1 / 4 : ℝ) := by
    have hs := hlogBase.const_mul (1 / (2 * Real.log K))
    apply hs.congr'
    filter_upwards with n
    ring
  have honeBase : Vanishes fun n ↦
      (m n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    (tendsto_rpow_neg_atTop hquarter).comp hmReal
  have hone : Vanishes fun n ↦
      1 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
    apply honeBase.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hmn
    rw [Real.rpow_neg (by positivity)]
    simp only [one_div]
  have htarget : Vanishes fun n ↦
      (Real.log (m n : ℝ) / (2 * Real.log K)) /
          (m n : ℝ) ^ (1 / 4 : ℝ) +
        1 / (m n : ℝ) ^ (1 / 4 : ℝ) :=
    hlogScaled.add hone
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hmn
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast (Nat.zero_lt_of_lt hmn)
    have hcut := deterministicConfigurationCycleCutoff_le_logRatio hd hmn
    have hpow := deterministicConfigurationCycleFactor_pow_cutoff_le_sqrt hd hmn
    have hcoeff :
        ((deterministicConfigurationCycleCutoff d (m n) + 1 : ℕ) : ℝ) ≤
          Real.log (m n : ℝ) / (2 * Real.log K) + 1 := by
      push_cast
      simpa only [K] using add_le_add_right hcut 1
    have hnum :
        ((deterministicConfigurationCycleCutoff d (m n) + 1 : ℕ) : ℝ) *
            (deterministicConfigurationCycleFactor d : ℝ) ^
              deterministicConfigurationCycleCutoff d (m n) ≤
          (Real.log (m n : ℝ) / (2 * Real.log K) + 1) *
            (m n : ℝ) ^ (1 / 2 : ℝ) := by
      exact mul_le_mul hcoeff hpow (by positivity)
        (add_nonneg
          (div_nonneg (Real.log_nonneg (by exact_mod_cast hmn))
            (mul_nonneg (by norm_num) hlogK.le))
          zero_le_one)
    calc
      (((deterministicConfigurationCycleCutoff d (m n) + 1 : ℕ) : ℝ) *
            (deterministicConfigurationCycleFactor d : ℝ) ^
              deterministicConfigurationCycleCutoff d (m n)) /
          (m n : ℝ) ^ (3 / 4 : ℝ) ≤
        ((Real.log (m n : ℝ) / (2 * Real.log K) + 1) *
            (m n : ℝ) ^ (1 / 2 : ℝ)) /
          (m n : ℝ) ^ (3 / 4 : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hmpos.le _)
      _ = (Real.log (m n : ℝ) / (2 * Real.log K)) /
            (m n : ℝ) ^ (1 / 4 : ℝ) +
          1 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
        have hratio :
            (m n : ℝ) ^ (1 / 2 : ℝ) /
                (m n : ℝ) ^ (3 / 4 : ℝ) =
              1 / (m n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_sub hmpos, show (1 / 2 : ℝ) - 3 / 4 =
            -(1 / 4) by norm_num, Real.rpow_neg hmpos.le]
          simp only [one_div]
        rw [mul_div_assoc, hratio]
        ring
  · exact htarget

/-- The logarithmic cutoff satisfies the exposure guard `4h ≤ mD`
eventually. -/
theorem eventually_deterministicConfigurationCycleCutoff_guard
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop,
      4 * deterministicConfigurationCycleCutoff d (m n) ≤
        m n * (d + d) := by
  let K : ℝ := deterministicConfigurationCycleFactor d
  let D : ℝ := d + d
  have hKone : 1 < K := by
    dsimp [K]
    exact_mod_cast deterministicConfigurationCycleFactor_one_lt hd
  have hlogK : 0 < Real.log K := Real.log_pos hKone
  have hD : 0 < D := by dsimp [D]; positivity
  have hmReal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hratio : Vanishes fun n ↦
      Real.log (m n : ℝ) / (m n : ℝ) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hmReal
  have hscaled : Vanishes fun n ↦
      (4 * (Real.log (m n : ℝ) / (2 * Real.log K))) /
        ((m n : ℝ) * D) := by
    have hs := hratio.const_mul (2 / (Real.log K * D))
    apply hs.congr'
    filter_upwards with n
    field_simp [hlogK.ne', hD.ne']
    ring
  have hlt : ∀ᶠ n in atTop,
      (4 * (Real.log (m n : ℝ) / (2 * Real.log K))) /
          ((m n : ℝ) * D) < 1 :=
    hscaled.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hm.eventually (eventually_ge_atTop 1), hlt] with n hmn hnlt
  have hmpos : (0 : ℝ) < m n := by exact_mod_cast (Nat.zero_lt_of_lt hmn)
  have hden : 0 < (m n : ℝ) * D := mul_pos hmpos hD
  have hcut := deterministicConfigurationCycleCutoff_le_logRatio hd hmn
  have hreal :
      (4 : ℝ) * deterministicConfigurationCycleCutoff d (m n) ≤
        (m n : ℝ) * D := by
    calc
      (4 : ℝ) * deterministicConfigurationCycleCutoff d (m n) ≤
          4 * (Real.log (m n : ℝ) / (2 * Real.log K)) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [K] using hcut) (by norm_num)
      _ ≤ (m n : ℝ) * D :=
        (div_lt_one hden).mp hnlt |>.le
  dsimp [D] at hreal
  exact_mod_cast hreal

/-- **Appendix Lemma A.5 (bad-event form).**  At the paper's logarithmic
cutoff, the probability that the number of distinct-vertex cycles reaches
`m^(3/4)` vanishes. -/
theorem deterministicConfiguration_fewShortCycles_failure_vanishes
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (configurationPermutationLaw (m n) d).prob
        (FiniteLaw.event fun sigma ↦
          (m n : ℝ) ^ (3 / 4 : ℝ) ≤
            configurationShortCycleCountReal
              (Configuration.standardConfiguration (m n) d).partner
              (deterministicConfigurationCycleCutoff d (m n)) sigma) := by
  exact configurationShortCycleCount_badProbability_vanishes_of_envelope
    d (Nat.zero_lt_of_lt hd) m
    (fun n ↦ deterministicConfigurationCycleCutoff d (m n)) hm
    (eventually_deterministicConfigurationCycleCutoff_guard d hd m hm)
    (deterministicConfigurationCycleCutoff_envelope_vanishes d hd m hm)

/-- Appendix A.5 in the manuscript's displayed `1-o(1)` form. -/
theorem deterministicConfiguration_fewShortCycles_probability_tendsto_one
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto
      (fun n ↦
        (configurationPermutationLaw (m n) d).prob
          (FiniteLaw.event fun sigma ↦
            configurationShortCycleCountReal
                (Configuration.standardConfiguration (m n) d).partner
                (deterministicConfigurationCycleCutoff d (m n)) sigma ≤
              (m n : ℝ) ^ (3 / 4 : ℝ)))
      atTop (nhds 1) := by
  let q : (n : ℕ) →
      FiniteLaw (Equiv.Perm (ConfigurationHalfEdge (m n) (d + d))) :=
    fun n ↦ configurationPermutationLaw (m n) d
  let bad : (n : ℕ) →
      Finset (Equiv.Perm (ConfigurationHalfEdge (m n) (d + d))) :=
    fun n ↦ FiniteLaw.event fun sigma ↦
      (m n : ℝ) ^ (3 / 4 : ℝ) ≤
        configurationShortCycleCountReal
          (Configuration.standardConfiguration (m n) d).partner
          (deterministicConfigurationCycleCutoff d (m n)) sigma
  let good : (n : ℕ) →
      Finset (Equiv.Perm (ConfigurationHalfEdge (m n) (d + d))) :=
    fun n ↦ FiniteLaw.event fun sigma ↦
      configurationShortCycleCountReal
          (Configuration.standardConfiguration (m n) d).partner
          (deterministicConfigurationCycleCutoff d (m n)) sigma ≤
        (m n : ℝ) ^ (3 / 4 : ℝ)
  have hbad : Vanishes fun n ↦ (q n).prob (bad n) := by
    simpa only [q, bad] using
      deterministicConfiguration_fewShortCycles_failure_vanishes d hd m hm
  have hlower : Tendsto (fun n ↦ (1 : ℝ) - (q n).prob (bad n))
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hbad
  refine hlower.squeeze' tendsto_const_nhds ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      have hcomp : Finset.univ \ bad n ⊆ good n := by
        intro sigma hsigma
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, bad, good,
          FiniteLaw.mem_event] at hsigma ⊢
        exact le_of_not_ge hsigma
      have hsplit := (bad n).sum_add_sum_compl (q n).mass
      have hprobComp : (q n).prob (Finset.univ \ bad n) =
          1 - (q n).prob (bad n) := by
        unfold FiniteLaw.prob
        simp only [Finset.compl_eq_univ_sdiff] at hsplit
        rw [(q n).sum_mass] at hsplit
        linarith
      rw [← hprobComp]
      exact (q n).prob_mono hcomp
  · exact Eventually.of_forall fun n ↦ by
      calc
        (q n).prob (good n) ≤ (q n).prob Finset.univ :=
          (q n).prob_mono (Finset.subset_univ _)
        _ = 1 := (q n).prob_univ

/-- Splitting an even total degree into the two equal socket blocks used by
the configuration-model implementation recovers the paper's degree. -/
theorem evenTotalDegree_half_add_half (D : ℕ) (hD : Even D) :
    D / 2 + D / 2 = D := by
  obtain ⟨d, rfl⟩ := hD
  omega

/-- In total-degree notation, the cycle factor used below is exactly the
paper's `K_D = 2(D-1)`. -/
theorem deterministicConfigurationCycleFactor_evenTotalDegree
    (D : ℕ) (hD : Even D) :
    deterministicConfigurationCycleFactor (D / 2) = 2 * (D - 1) := by
  obtain ⟨d, rfl⟩ := hD
  simp only [deterministicConfigurationCycleFactor]
  congr 1
  omega

/-- **Appendix Lemma A.5 (paper-facing even-degree form).**  For every even
total degree `D ≥ 6`, with `d = D/2`, the probability that the number of
distinct-vertex cycles up to
`floor(log m /(2 log(2(D-1))))` is at most `m^(3/4)` tends to one. -/
theorem appendixA5_evenDegree_fewShortCycles_probability_tendsto_one
    (D : ℕ) (hD : Even D) (hD6 : 6 ≤ D)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto
      (fun n ↦
        (configurationPermutationLaw (m n) (D / 2)).prob
          (FiniteLaw.event fun sigma ↦
            configurationShortCycleCountReal
                (Configuration.standardConfiguration (m n) (D / 2)).partner
                (deterministicConfigurationCycleCutoff (D / 2) (m n)) sigma ≤
              (m n : ℝ) ^ (3 / 4 : ℝ)))
      atTop (nhds 1) := by
  apply deterministicConfiguration_fewShortCycles_probability_tendsto_one
  · obtain ⟨d, rfl⟩ := hD
    omega
  · exact hm

/-- Appendix A.5 specialized to the manuscript's plant size
`m_n = floor(n^r)`. -/
theorem appendixPlantSize_fewShortCycles_probability_tendsto_one
    (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun n ↦
        (configurationPermutationLaw (appendixPlantSize r n) d).prob
          (FiniteLaw.event fun sigma ↦
            configurationShortCycleCountReal
                (Configuration.standardConfiguration
                  (appendixPlantSize r n) d).partner
                (deterministicConfigurationCycleCutoff d
                  (appendixPlantSize r n)) sigma ≤
              (appendixPlantSize r n : ℝ) ^ (3 / 4 : ℝ)))
      atTop (nhds 1) := by
  exact deterministicConfiguration_fewShortCycles_probability_tendsto_one
    d hd (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr)

end

end LowDegree
