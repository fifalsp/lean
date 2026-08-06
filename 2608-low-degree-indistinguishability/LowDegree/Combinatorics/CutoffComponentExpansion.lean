import LowDegree.Combinatorics.GraphComponentExpansion

/-!
# Connected-component expansion with an edge cutoff

Appendix A controls only Fourier supports with at most `D_n` edges.  Cutting
off the parent beta weight is compatible with the component encoding: every
connected component of a graph with at most `D_n` edges also has at most
`D_n` edges.  Consequently the existing injective component expansion gives
the required exponential/geometric majorant without an informal multiset
sum over graph isomorphism types.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable Fintype.ofFinite

open AggregateGraphRestriction

namespace GraphComponentExpansion

variable {n : Nat}

/-- One per-triple beta weight, retained only below an edge cutoff. -/
noncomputable def cutoffTripleBetaScale
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) : Real :=
  if z.1.shape.edgeCount <= D then tripleBetaScale c n z.1.shape else 0

/-- Duplicate-free beta mass over all nonempty graph shapes below the cutoff. -/
noncomputable def cutoffBetaMass
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n)) : Real :=
  ∑ C : AmbientSupportClass n with C.shape.edgeCount <= D,
    C.shape.graphBetaWeight c n plant

/-- Connected portion of `cutoffBetaMass`. -/
noncomputable def connectedCutoffBetaMass
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n)) : Real :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.edgeCount <= D,
    C.shape.graphBetaWeight c n plant

theorem cutoffTripleBetaScale_nonneg {c : Real} (hc : 0 < c)
    (D : Nat) (plant : SimpleGraph (Fin n)) (z : TaggedTriple plant) :
    0 <= cutoffTripleBetaScale c D plant z := by
  unfold cutoffTripleBetaScale
  split
  · exact tripleBetaScale_nonneg hc n z.1.shape
  · exact le_rfl

/-- A component has no more edges than its parent graph. -/
theorem connectedComponent_edgeCount_le
    (F : FiniteGraphShape) (i : Fin F.componentCount) :
    (F.pieceShape F.connectedComponentDecomposition i).edgeCount <=
      F.edgeCount := by
  rw [edgeCount_eq_sum_connectedComponent_edgeCount F]
  exact Finset.single_le_sum
    (fun j _ => Nat.zero_le
      (F.pieceShape F.connectedComponentDecomposition j).edgeCount)
    (Finset.mem_univ i)

/-- Reindexing a restricted component preserves its beta scale. -/
theorem tripleBetaScale_componentTriple
    (c : Real) (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) (i : Fin z.1.shape.componentCount) :
    tripleBetaScale c n (componentTriple plant z i).1.shape =
      tripleBetaScale c n
        (z.1.shape.pieceShape z.1.shape.connectedComponentDecomposition i) := by
  unfold componentTriple
  exact (tripleBetaScale_eq_of_iso
    (pieceShapeIso z.1 z.1.shape.connectedComponentDecomposition i)).symm

/-- Cutoff beta weights remain submultiplicative over connected components. -/
theorem cutoffTripleBetaScale_le_prod_componentTriple
    (c : Real) (hc : 0 < c) (D : Nat)
    (plant : SimpleGraph (Fin n)) (z : TaggedTriple plant) :
    cutoffTripleBetaScale c D plant z <=
      ∏ i : Fin z.1.shape.componentCount,
        cutoffTripleBetaScale c D plant (componentTriple plant z i) := by
  by_cases hparent : z.1.shape.edgeCount <= D
  · rw [cutoffTripleBetaScale, if_pos hparent]
    have hcomponent (i : Fin z.1.shape.componentCount) :
        (componentTriple plant z i).1.shape.edgeCount <= D := by
      change (pieceClass z.1 z.1.shape.connectedComponentDecomposition i).shape.edgeCount <= D
      rw [pieceClass_shape_edgeCount]
      exact (connectedComponent_edgeCount_le z.1.shape i).trans hparent
    simp_rw [cutoffTripleBetaScale, if_pos (hcomponent _),
      tripleBetaScale_componentTriple c plant z]
    exact tripleBetaScale_le_prod_connectedComponents
      c hc n (ambientSize_pos z.1) z.1.shape
  · rw [cutoffTripleBetaScale, if_neg hparent]
    exact Finset.prod_nonneg fun i _ =>
      cutoffTripleBetaScale_nonneg hc D plant (componentTriple plant z i)

/-- List-indexed version needed by the abstract component encoding. -/
theorem cutoffTripleBetaScale_le_prod_components
    (c : Real) (hc : 0 < c) (D : Nat)
    (plant : SimpleGraph (Fin n))
    (z : (encoding plant).ActiveObject) :
    cutoffTripleBetaScale c D plant z.1 <=
      ∏ i : Fin ((encoding plant).components z.1).length,
        cutoffTripleBetaScale c D plant
          (((encoding plant).components z.1).get i) := by
  change cutoffTripleBetaScale c D plant z.1 <=
    ∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
      cutoffTripleBetaScale c D plant
        ((List.ofFn (componentTriple plant z.1)).get i)
  have hprod :
      (∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
        cutoffTripleBetaScale c D plant
          ((List.ofFn (componentTriple plant z.1)).get i)) =
        ∏ i : Fin z.1.1.shape.componentCount,
          cutoffTripleBetaScale c D plant
            (componentTriple plant z.1 i) := by
    refine Fintype.prod_equiv
      (Fin.castOrderIso (List.length_ofFn)).toEquiv _ _ ?_
    intro i
    simp only [List.get_ofFn]
    apply congrArg (fun j => cutoffTripleBetaScale c D plant
      (componentTriple plant z.1 j))
    apply Fin.ext
    rfl
  rw [hprod]
  exact cutoffTripleBetaScale_le_prod_componentTriple
    c hc D plant z.1

/-- Summing cutoff per-triple weights recovers the graph-class cutoff mass. -/
theorem sum_cutoffTripleBetaScale_eq
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n)) :
    (∑ z : TaggedTriple plant, cutoffTripleBetaScale c D plant z) =
      cutoffBetaMass c D plant := by
  rw [Fintype.sum_sigma]
  unfold cutoffBetaMass
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : C.shape.edgeCount <= D
  · simp only [cutoffTripleBetaScale, hC, if_true]
    exact sum_tripleBetaScale_eq_graphBetaWeight c n C.shape plant
  · simp only [cutoffTripleBetaScale, hC, if_false, Finset.sum_const_zero]

/-- The active-object sum is the same cutoff beta mass. -/
theorem sum_active_cutoffTripleBetaScale_eq
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n)) :
    (∑ z : (encoding plant).ActiveObject,
      cutoffTripleBetaScale c D plant z.1) =
      cutoffBetaMass c D plant := by
  calc
    (∑ z : (encoding plant).ActiveObject,
        cutoffTripleBetaScale c D plant z.1) =
        ∑ z : TaggedTriple plant,
          cutoffTripleBetaScale c D plant z := by
      symm
      simpa [encoding] using
        (Finset.sum_subtype
          (Finset.univ : Finset (TaggedTriple plant))
          (by intro z; simp)
          (cutoffTripleBetaScale c D plant))
    _ = cutoffBetaMass c D plant :=
      sum_cutoffTripleBetaScale_eq c D plant

/-- The connected-object sum is exactly the connected cutoff mass. -/
theorem connectedMass_cutoffTripleBetaScale_eq
    (c : Real) (D : Nat) (plant : SimpleGraph (Fin n)) :
    (encoding plant).connectedMass (cutoffTripleBetaScale c D plant) =
      connectedCutoffBetaMass c D plant := by
  unfold ComponentEncoding.connectedMass connectedCutoffBetaMass
  calc
    (∑ z : (encoding plant).ConnectedObject,
        cutoffTripleBetaScale c D plant z.1) =
        ∑ z : TaggedTriple plant with z.1.shape.graph.Connected,
          cutoffTripleBetaScale c D plant z := by
      symm
      simpa [encoding] using (Finset.sum_subtype
        ((Finset.univ : Finset (TaggedTriple plant)).filter
          fun z => z.1.shape.graph.Connected)
        (by intro z; simp) (cutoffTripleBetaScale c D plant))
    _ = ∑ C : AmbientSupportClass n with
          C.shape.graph.Connected ∧ C.shape.edgeCount <= D,
        C.shape.graphBetaWeight c n plant := by
      simp only [Finset.sum_filter]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _
      by_cases hconn : C.shape.graph.Connected
      · by_cases hdegree : C.shape.edgeCount <= D
        · simp only [hconn, hdegree, and_self, if_true,
            cutoffTripleBetaScale]
          exact sum_tripleBetaScale_eq_graphBetaWeight c n C.shape plant
        · have hrep : ¬C.representative.1.card <= D := by
            rw [← C.shape_edgeCount_eq_representative_card]
            exact hdegree
          simp [hconn, hdegree, hrep, cutoffTripleBetaScale]
      · simp only [hconn, false_and, if_false, Finset.sum_const_zero]

/-- Pointwise geometric majorant for the cutoff beta mass. -/
theorem cutoffBetaMass_le_geometric_connectedCutoffBetaMass
    (c : Real) (hc : 0 < c) (D : Nat)
    (plant : SimpleGraph (Fin n))
    (hmass : connectedCutoffBetaMass c D plant < 1) :
    cutoffBetaMass c D plant <=
      connectedCutoffBetaMass c D plant /
        (1 - connectedCutoffBetaMass c D plant) := by
  let E := encoding plant
  let weight : TaggedTriple plant -> Real := cutoffTripleBetaScale c D plant
  have hmass' : E.connectedMass weight < 1 := by
    simpa only [E, weight, connectedMass_cutoffTripleBetaScale_eq] using hmass
  have hmajor := E.sum_active_le_geometric_connectedMass
    weight
    (fun z => cutoffTripleBetaScale_nonneg hc D plant z)
    (fun z => cutoffTripleBetaScale_le_prod_components c hc D plant z)
    hmass'
  simpa only [E, weight, sum_active_cutoffTripleBetaScale_eq,
    connectedMass_cutoffTripleBetaScale_eq] using hmajor

/-- Vanishing connected cutoff mass implies vanishing total cutoff mass. -/
theorem cutoffBetaMass_vanishes_of_connected
    (c : Real) (hc : 0 < c)
    (D : Nat -> Nat) (plant : forall n, SimpleGraph (Fin n))
    (hconnected : Vanishes fun n =>
      connectedCutoffBetaMass c (D n) (plant n)) :
    Vanishes fun n => cutoffBetaMass c (D n) (plant n) := by
  have hlt : ∀ᶠ n in atTop,
      connectedCutoffBetaMass c (D n) (plant n) < 1 :=
    hconnected.eventually_lt_const zero_lt_one
  have hupper : ∀ᶠ n in atTop,
      cutoffBetaMass c (D n) (plant n) <=
        connectedCutoffBetaMass c (D n) (plant n) /
          (1 - connectedCutoffBetaMass c (D n) (plant n)) := by
    filter_upwards [hlt] with n hn
    exact cutoffBetaMass_le_geometric_connectedCutoffBetaMass
      c hc (D n) (plant n) hn
  have hden : Tendsto (fun n =>
      1 - connectedCutoffBetaMass c (D n) (plant n))
      atTop (nhds (1 : Real)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hconnected
  have hfrac : Vanishes fun n =>
      connectedCutoffBetaMass c (D n) (plant n) /
        (1 - connectedCutoffBetaMass c (D n) (plant n)) := by
    simpa only [zero_div] using hconnected.div hden (by norm_num : (1 : Real) ≠ 0)
  have hnonneg : forall n, 0 <= cutoffBetaMass c (D n) (plant n) := by
    intro n
    unfold cutoffBetaMass
    exact Finset.sum_nonneg fun C _ => by
      unfold FiniteGraphShape.graphBetaWeight betaWeight
      exact mul_nonneg
        (div_nonneg
          (div_nonneg (pow_nonneg (Nat.cast_nonneg n) C.shape.edgeCount)
            (pow_nonneg (Nat.cast_nonneg n) C.shape.vertexCount))
          (pow_nonneg hc.le C.shape.edgeCount))
        (mul_nonneg
          (sq_nonneg (C.shape.nonInducedCopyCount (plant n) : Real))
          (Nat.cast_nonneg _))
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hupper hfrac

end GraphComponentExpansion

end

end LowDegree
