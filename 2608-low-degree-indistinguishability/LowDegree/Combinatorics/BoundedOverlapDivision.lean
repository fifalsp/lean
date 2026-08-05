import LowDegree.Combinatorics.EdgeOwnedRefinement
import LowDegree.Combinatorics.ClusterInterfaceCharging
import LowDegree.Combinatorics.GraphCopies
import Mathlib.Data.Finset.Preimage

/-!
# Bounded-overlap divisions from treewidth

This module assembles the three constructive ingredients from Section 5:

* an edge-owned subcubic refinement of a width-bounded tree decomposition;
* a connected weighted partition of that refinement tree; and
* the interface-charging bound for the resulting quotient tree.

The main theorem is the unconditional ordered-edge-decomposition conclusion
of Proposition 5.1 in the paper.  Connectedness is not used by the
construction, so the formal theorem is slightly stronger than the stated
proposition.
-/

namespace LowDegree

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

universe u v w

namespace TreeDecomposition

/-! ## Pulling tree decompositions back through graph copies -/

variable {W : Type v} {V : Type u} {X : Type w}
variable [Fintype W] [Fintype V] [Fintype X]
variable {F : SimpleGraph W} {G : SimpleGraph V}

/-- Pull a tree decomposition of an ambient graph back through an injective
graph homomorphism.  Each new bag is the preimage of the corresponding old
bag. -/
noncomputable def Decomposition.pullbackCopy
    (D : Decomposition G X) (copy : SimpleGraph.Copy F G) :
    Decomposition F X where
  tree := D.tree
  bag := fun x ↦ (D.bag x).preimage copy copy.injective.injOn
  isTree := D.isTree
  vertex_mem := by
    intro a
    obtain ⟨x, hx⟩ := D.vertex_mem (copy a)
    exact ⟨x, Finset.mem_preimage.mpr hx⟩
  edge_mem := by
    intro a b hab
    obtain ⟨x, hax, hbx⟩ := D.edge_mem (copy.toHom.map_rel hab)
    exact ⟨x, Finset.mem_preimage.mpr hax, Finset.mem_preimage.mpr hbx⟩
  running_intersection := by
    intro a
    have hset :
        {x : X | a ∈ (D.bag x).preimage copy copy.injective.injOn} =
          {x : X | copy a ∈ D.bag x} := by
      ext x
      exact Finset.mem_preimage
    rw [hset]
    exact D.running_intersection (copy a)

/-- Pullback cannot increase the width of a tree decomposition because the
copy map is injective. -/
theorem Decomposition.pullbackCopy_widthAtMost
    (D : Decomposition G X) (copy : SimpleGraph.Copy F G) {k : ℕ}
    (hwidth : D.WidthAtMost k) :
    (D.pullbackCopy copy).WidthAtMost k := by
  intro x
  change ((D.bag x).preimage copy copy.injective.injOn).card ≤ k + 1
  calc
    ((D.bag x).preimage copy copy.injective.injOn).card ≤
        (D.bag x).card := by
      rw [Finset.card_preimage]
      exact Finset.card_filter_le _ _
    _ ≤ k + 1 := hwidth x

/-- Treewidth is monotone under taking a not-necessarily-induced graph copy:
an injective graph homomorphism into a width-`k` graph supplies a width-`k`
decomposition of its source. -/
theorem hasTreewidthAtMost_of_copy
    (copy : SimpleGraph.Copy F G) {k : ℕ}
    (hG : HasTreewidthAtMost G k) : HasTreewidthAtMost F k := by
  obtain ⟨t, D, hwidth⟩ := hG
  exact ⟨t, D.pullbackCopy copy, D.pullbackCopy_widthAtMost copy hwidth⟩

end TreeDecomposition

namespace FiniteGraphShape

variable {V : Type u} [Fintype V]

/-- Any abstract graph shape that occurs in a width-`k` ambient graph also
has treewidth at most `k`. -/
theorem hasTreewidthAtMost_of_occurrence
    (S : FiniteGraphShape.{u}) (plant : SimpleGraph V) {k : ℕ}
    (hcopy : 0 < S.nonInducedCopyCount plant)
    (hplant : TreeDecomposition.HasTreewidthAtMost plant k) :
    TreeDecomposition.HasTreewidthAtMost S.graph k := by
  have hne : Nonempty (S.ConcreteCopy plant) :=
    Fintype.card_pos_iff.mp hcopy
  let concrete : S.ConcreteCopy plant := Classical.choice hne
  let copy : SimpleGraph.Copy S.graph plant :=
    concrete.1.coeCopy.comp (S.chosenIso concrete).toCopy
  exact TreeDecomposition.hasTreewidthAtMost_of_copy copy hplant

end FiniteGraphShape

namespace TreeDecomposition

/-! ## Paper Proposition 5.1 -/

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} {k l : ℕ}

/-- **Paper Proposition 5.1.**  A finite graph of treewidth at most `k` and
with at least `l > 0` edges admits an ordered edge decomposition whose pieces
have between `l` and `3*l` edges and whose total vertex overlap is at most
`(k+1)(m-1)`.

The paper assumes that the graph is connected.  The proof only uses a tree
decomposition and the lower bound on the total edge count, and hence yields
this stronger statement without a connectedness assumption. -/
theorem exists_boundedOverlap_orderedEdgeDecomposition
    (hG : HasTreewidthAtMost G k) (hl : 0 < l)
    (htotal : l ≤ G.edgeFinset.card) :
    ∃ m : ℕ, ∃ P : OrderedEdgeDecomposition G m,
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ (k + 1) * (m - 1) := by
  obtain ⟨Y, instY, R, hwidth⟩ :=
    exists_edgeOwnedRefinement_of_hasTreewidthAtMost hG
  letI : Fintype Y := instY
  obtain ⟨m, ⟨C⟩⟩ :=
    IndexedWeightedTreePartition.EdgeOwnedRefinementWitness.exists_clusterQuotientWitness
      R hl htotal
  let P : OrderedEdgeDecomposition G m := C.edgeDecomposition hl
  refine ⟨m, P, ?_, ?_⟩
  · intro i
    exact
      ⟨C.edgeDecomposition_piece_card_lower hl i,
        C.edgeDecomposition_piece_card_upper hl i⟩
  · exact (C.interfaceChargingWitness hl hwidth).overlap_le

/-- Connected formulation matching the hypotheses printed in Proposition
5.1.  It is kept as a named paper-facing wrapper even though connectedness is
not needed by the stronger construction theorem above. -/
theorem connected_exists_boundedOverlap_orderedEdgeDecomposition
    (hconn : G.Connected) (hG : HasTreewidthAtMost G k) (hl : 0 < l)
    (htotal : l ≤ G.edgeFinset.card) :
    ∃ m : ℕ, ∃ P : OrderedEdgeDecomposition G m,
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ (k + 1) * (m - 1) := by
  exact exists_boundedOverlap_orderedEdgeDecomposition hG hl htotal

/-! ## Divisibility and paper Lemma 4.3 -/

/-- The paper's `(l,C,a)`-divisibility property, stated intrinsically over
finite support shapes.  The occurrence condition is exactly
`N_Γ(F) > 0`; the shape convention excludes isolated vertices. -/
def IsDivisible (plant : SimpleGraph V) (l C a : ℕ) : Prop :=
  ∀ S : FiniteGraphShape.{u},
    S.graph.Connected →
    0 < S.nonInducedCopyCount plant →
    l ≤ S.edgeCount →
    ∃ m : ℕ, ∃ P : OrderedEdgeDecomposition S.graph m,
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ C * l) ∧
      P.overlap ≤ a * (m - 1)

/-- **Paper Lemma 4.3.**  Every finite graph of treewidth at most `k` is
`(l,3,k+1)`-divisible for every positive `l`. -/
theorem isDivisible_of_hasTreewidthAtMost
    (hplant : HasTreewidthAtMost G k) (hl : 0 < l) :
    IsDivisible G l 3 (k + 1) := by
  intro S hconn hcopy hedge
  have hS : HasTreewidthAtMost S.graph k :=
    S.hasTreewidthAtMost_of_occurrence G hcopy hplant
  have hedge' : l ≤ S.graph.edgeFinset.card := by
    calc
      l ≤ S.edgeCount := hedge
      _ = S.graph.edgeFinset.card := by
        rw [S.edgeCount_eq_ncard]
        exact Set.ncard_eq_toFinset_card' S.graph.edgeSet
  exact connected_exists_boundedOverlap_orderedEdgeDecomposition
    hconn hS hl hedge'

end TreeDecomposition
end
end LowDegree
