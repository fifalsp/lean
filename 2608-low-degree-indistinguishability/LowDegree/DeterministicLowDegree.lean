import LowDegree.Combinatorics.CutoffComponentExpansion
import LowDegree.DeterministicConnectedCount
import LowDegree.DeterministicConfigurationBase
import LowDegree.SupercriticalCanonicalScales
import LowDegree.SupercriticalEnumerationBounds
import LowDegree.SupercriticalExcessBound

/-!
# Low-degree bound for deterministic bounded-degree plants

This module formalizes the analytic part of the revised Appendix theorem.
The construction of the deterministic graph sequence is kept separate.  The
inputs here are exactly the three consequences used in the paper: a
bounded-degree connected-copy count, local sparsity for occurring low-degree
shapes, and logarithmic girth for occurring cyclic shapes.
-/

namespace LowDegree

open Filter Topology Asymptotics
open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable Fintype.ofFinite

open GraphComponentExpansion

/-- Connected acyclic contribution at one exact edge count. -/
noncomputable def deterministicTreeBetaFiber
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (e : Nat) : Real :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount = e,
    C.shape.graphBetaWeight c n plant

/-- Connected cyclic contribution at one exact edge count. -/
noncomputable def deterministicCyclicBetaFiber
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (e : Nat) : Real :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount = e,
    C.shape.graphBetaWeight c n plant

/-- Connected acyclic contribution below a cutoff. -/
noncomputable def deterministicTreeCutoffBetaMass
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (K : Nat) : Real :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount <= K,
    C.shape.graphBetaWeight c n plant

/-- Connected cyclic contribution below a cutoff. -/
noncomputable def deterministicCyclicCutoffBetaMass
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (K : Nat) : Real :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount <= K,
    C.shape.graphBetaWeight c n plant

/-- The connected cutoff mass splits into tree and cyclic pieces. -/
theorem connectedCutoffBetaMass_eq_tree_add_cyclic
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (K : Nat) :
    connectedCutoffBetaMass c K plant =
      deterministicTreeCutoffBetaMass c plant K +
        deterministicCyclicCutoffBetaMass c plant K := by
  unfold connectedCutoffBetaMass deterministicTreeCutoffBetaMass
    deterministicCyclicCutoffBetaMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  have hrepEq : C.representative.1.card = C.shape.edgeCount := by
    exact C.shape_edgeCount_eq_representative_card.symm
  by_cases hconn : C.shape.graph.Connected
  · by_cases hdegree : C.shape.edgeCount <= K
    · by_cases hacyclic : C.shape.graph.IsAcyclic <;>
        simp [hconn, hdegree, hacyclic]
    · have hrep : ¬C.representative.1.card <= K := by
        rw [hrepEq]
        exact hdegree
      simp [hdegree, hrep]
  · simp [hconn]

/-- Regroup the tree cutoff mass by its exact positive edge count. -/
theorem deterministicTreeCutoffBetaMass_eq_sum_fibers
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (K : Nat) :
    deterministicTreeCutoffBetaMass c plant K =
      ∑ e ∈ Finset.Icc 1 K, deterministicTreeBetaFiber c plant e := by
  let s : Finset (AmbientSupportClass n) :=
    (Finset.univ : Finset (AmbientSupportClass n)).filter fun C =>
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic
  let weight : AmbientSupportClass n -> Real := fun C =>
    C.shape.graphBetaWeight c n plant
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    s (Finset.Icc 1 K) (fun C => C.shape.edgeCount) weight
  symm
  calc
    (∑ e ∈ Finset.Icc 1 K, deterministicTreeBetaFiber c plant e) =
        ∑ e ∈ Finset.Icc 1 K,
          ∑ C ∈ s with C.shape.edgeCount = e, weight C := by
      apply Finset.sum_congr rfl
      intro e _
      have hfilter :
          (Finset.univ : Finset (AmbientSupportClass n)).filter
              (fun C => C.shape.graph.Connected ∧
                C.shape.graph.IsAcyclic ∧ C.shape.edgeCount = e) =
            s.filter (fun C => C.shape.edgeCount = e) := by
        ext C
        simp [s, and_assoc]
      unfold deterministicTreeBetaFiber
      rw [hfilter]
    _ = ∑ C ∈ s with C.shape.edgeCount ∈ Finset.Icc 1 K, weight C := hfiber
    _ = deterministicTreeCutoffBetaMass c plant K := by
      unfold deterministicTreeCutoffBetaMass
      simp only [s, weight, Finset.sum_filter, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_Icc]
      apply Finset.sum_congr rfl
      intro C _
      have hedgePos : 0 < C.shape.edgeCount :=
        GraphComponentExpansion.ambientSupportClass_edgeCount_pos C
      by_cases hconn : C.shape.graph.Connected <;>
        by_cases hacyclic : C.shape.graph.IsAcyclic <;>
          by_cases hdegree : C.shape.edgeCount <= K <;>
            simp [hconn, hacyclic, hdegree, hedgePos, C.representative.2]

/-- Regroup the cyclic cutoff mass by its exact positive edge count. -/
theorem deterministicCyclicCutoffBetaMass_eq_sum_fibers
    (c : Real) {n : Nat} (plant : SimpleGraph (Fin n)) (K : Nat) :
    deterministicCyclicCutoffBetaMass c plant K =
      ∑ e ∈ Finset.Icc 1 K, deterministicCyclicBetaFiber c plant e := by
  let s : Finset (AmbientSupportClass n) :=
    (Finset.univ : Finset (AmbientSupportClass n)).filter fun C =>
      C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic
  let weight : AmbientSupportClass n -> Real := fun C =>
    C.shape.graphBetaWeight c n plant
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    s (Finset.Icc 1 K) (fun C => C.shape.edgeCount) weight
  symm
  calc
    (∑ e ∈ Finset.Icc 1 K, deterministicCyclicBetaFiber c plant e) =
        ∑ e ∈ Finset.Icc 1 K,
          ∑ C ∈ s with C.shape.edgeCount = e, weight C := by
      apply Finset.sum_congr rfl
      intro e _
      have hfilter :
          (Finset.univ : Finset (AmbientSupportClass n)).filter
              (fun C => C.shape.graph.Connected ∧
                ¬C.shape.graph.IsAcyclic ∧ C.shape.edgeCount = e) =
            s.filter (fun C => C.shape.edgeCount = e) := by
        ext C
        simp [s, and_assoc]
      unfold deterministicCyclicBetaFiber
      rw [hfilter]
    _ = ∑ C ∈ s with C.shape.edgeCount ∈ Finset.Icc 1 K, weight C := hfiber
    _ = deterministicCyclicCutoffBetaMass c plant K := by
      unfold deterministicCyclicCutoffBetaMass
      simp only [s, weight, Finset.sum_filter, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_Icc]
      apply Finset.sum_congr rfl
      intro C _
      have hedgePos : 0 < C.shape.edgeCount :=
        GraphComponentExpansion.ambientSupportClass_edgeCount_pos C
      by_cases hconn : C.shape.graph.Connected <;>
        by_cases hacyclic : C.shape.graph.IsAcyclic <;>
          by_cases hdegree : C.shape.edgeCount <= K <;>
            simp [hconn, hacyclic, hdegree, hedgePos, C.representative.2]

/-- A connected cyclic finite graph shape has at least as many edges as
vertices. -/
theorem FiniteGraphShape.vertexCount_le_edgeCount_of_connected_not_acyclic
    (F : FiniteGraphShape) (hconn : F.graph.Connected)
    (hcyclic : ¬F.graph.IsAcyclic) :
    F.vertexCount <= F.edgeCount := by
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hcard
  change F.vertexCount <= F.graph.edgeFinset.card + 1 at hcard
  have hedge : F.graph.edgeFinset.card = F.edgeCount := by
    rw [FiniteGraphShape.edgeCount_eq_ncard]
    exact (Set.ncard_eq_toFinset_card' F.graph.edgeSet).symm
  rw [hedge] at hcard
  by_contra hnot
  have heq : F.edgeCount + 1 = F.vertexCount := by omega
  have htree : F.graph.IsTree :=
    SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by
      calc
        Nat.card F.graph.edgeSet + 1 = F.edgeCount + 1 := by
          rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
            hedge]
        _ = F.vertexCount := heq
        _ = Nat.card F.Vertex := by
          simp [FiniteGraphShape.vertexCount, Nat.card_eq_fintype_card]⟩
  exact hcyclic htree.2

/-- For a connected tree shape with `e` edges, the beta scale is exactly
`1/(n c^e)` times its isomorphism-triple count. -/
theorem graphBetaWeight_eq_tree_scale
    {c : Real} {n e : Nat} (hn : 0 < n)
    (F : FiniteGraphShape) (plant : SimpleGraph (Fin n))
    (hconn : F.graph.Connected) (hacyclic : F.graph.IsAcyclic)
    (hedge : F.edgeCount = e) :
    F.graphBetaWeight c n plant =
      (1 / ((n : Real) * c ^ e)) *
        ((F.nonInducedCopyCount plant ^ 2 *
          Fintype.card F.Automorphism : Nat) : Real) := by
  have htree : F.graph.IsTree := ⟨hconn, hacyclic⟩
  have hcard := htree.card_edgeFinset
  have hedgeCard : F.graph.edgeFinset.card = F.edgeCount := by
    rw [FiniteGraphShape.edgeCount_eq_ncard]
    exact (Set.ncard_eq_toFinset_card' F.graph.edgeSet).symm
  have hvertex : F.vertexCount = e + 1 := by
    change Fintype.card F.Vertex = e + 1
    rw [← hcard, hedgeCard, hedge]
  have hnreal : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  unfold FiniteGraphShape.graphBetaWeight betaWeight
  rw [hedge, hvertex, pow_succ]
  push_cast
  field_simp

/-- Local sparsity controls the power `n^(e-v)` by `exp(A)^e`. -/
theorem natPowRatio_le_expPow_of_localSparsity
    (A : Real) {n e v : Nat}
    (hn : 1 < n) (hA : 0 <= A) (hve : v <= e)
    (hlocal : (e : Real) <=
      (1 + A / Real.log (n : Real)) * (v : Real)) :
    (n : Real) ^ e / (n : Real) ^ v <= (Real.exp A) ^ e := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnne : (n : Real) ≠ 0 := hnpos.ne'
  have hlogpos : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast hn)
  have hexcess : ((e - v : Nat) : Real) <=
      A / Real.log (n : Real) * (v : Real) := by
    rw [Nat.cast_sub hve]
    nlinarith
  have hlogexcess : ((e - v : Nat) : Real) * Real.log (n : Real) <=
      A * (e : Real) := by
    calc
      ((e - v : Nat) : Real) * Real.log (n : Real) <=
          (A / Real.log (n : Real) * (v : Real)) *
            Real.log (n : Real) :=
        mul_le_mul_of_nonneg_right hexcess hlogpos.le
      _ = A * (v : Real) := by field_simp
      _ <= A * (e : Real) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hve) hA
  calc
    (n : Real) ^ e / (n : Real) ^ v = (n : Real) ^ (e - v) := by
      rw [div_eq_mul_inv, ← pow_sub₀ (n : Real) hnne hve]
    _ = (Real.exp (Real.log (n : Real))) ^ (e - v) := by
      rw [Real.exp_log hnpos]
    _ = Real.exp (((e - v : Nat) : Real) * Real.log (n : Real)) :=
      (Real.exp_nat_mul (Real.log (n : Real)) (e - v)).symm
    _ <= Real.exp (A * (e : Real)) :=
      Real.exp_le_exp.mpr (by simpa [mul_comm] using hlogexcess)
    _ = (Real.exp A) ^ e := by
      simpa only [mul_comm] using Real.exp_nat_mul A e

/-- Pointwise cyclic beta bound following from local sparsity. -/
theorem graphBetaWeight_le_cyclic_scale
    {c A : Real} {n e : Nat} (hc : 0 < c) (hn : 1 < n)
    (hA : 0 <= A) (F : FiniteGraphShape)
    (plant : SimpleGraph (Fin n))
    (hconn : F.graph.Connected) (hcyclic : ¬F.graph.IsAcyclic)
    (hedge : F.edgeCount = e)
    (hlocal : (F.edgeCount : Real) <=
      (1 + A / Real.log (n : Real)) * (F.vertexCount : Real)) :
    F.graphBetaWeight c n plant <=
      (Real.exp A / c) ^ e *
        ((F.nonInducedCopyCount plant ^ 2 *
          Fintype.card F.Automorphism : Nat) : Real) := by
  have hve := F.vertexCount_le_edgeCount_of_connected_not_acyclic
    hconn hcyclic
  have hratio := natPowRatio_le_expPow_of_localSparsity
    A hn hA hve hlocal
  have hratio' :
      (n : Real) ^ e / (n : Real) ^ F.vertexCount <=
        (Real.exp A) ^ e := by
    simpa [hedge] using hratio
  have hcPow : 0 <= c ^ e := pow_nonneg hc.le e
  have htripleReal : 0 <=
      (F.nonInducedCopyCount plant : Real) ^ 2 *
        (Fintype.card F.Automorphism : Real) := by positivity
  unfold FiniteGraphShape.graphBetaWeight betaWeight
  rw [hedge]
  push_cast
  calc
    (((n : Real) ^ e / (n : Real) ^ F.vertexCount) / c ^ e) *
        ((F.nonInducedCopyCount plant : Real) ^ 2 *
          (Fintype.card F.Automorphism : Real)) <=
      (((Real.exp A) ^ e) / c ^ e) *
        ((F.nonInducedCopyCount plant : Real) ^ 2 *
          (Fintype.card F.Automorphism : Real)) := by
      apply mul_le_mul_of_nonneg_right _ htripleReal
      exact div_le_div_of_nonneg_right hratio' hcPow
    _ = (Real.exp A / c) ^ e *
        ((F.nonInducedCopyCount plant : Real) ^ 2 *
          (Fintype.card F.Automorphism : Real)) := by
      rw [div_pow]

/-- The triple count of the tree fiber is bounded by the full connected
triple count at the same edge count. -/
theorem treeTripleFiber_le_connectedShapeTripleMass
    {n e : Nat} (plant : SimpleGraph (Fin n)) :
    (∑ C : AmbientSupportClass n with
        C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
          C.shape.edgeCount = e,
      ((C.shape.nonInducedCopyCount plant ^ 2 *
        Fintype.card C.shape.Automorphism : Nat) : Real)) <=
      (connectedShapeTripleMass plant e : Real) := by
  exact_mod_cast (show
    (∑ C : AmbientSupportClass n with
        C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
          C.shape.edgeCount = e,
      C.shape.nonInducedCopyCount plant ^ 2 *
        Fintype.card C.shape.Automorphism) <=
      connectedShapeTripleMass plant e from by
    unfold connectedShapeTripleMass connectedShapeClasses
    rw [show Fintype.card (Fin n) = n by simp]
    simp only [Finset.sum_filter]
    apply Finset.sum_le_sum (N := Nat)
    intro C _
    by_cases hs : C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount = e
    · have ht : C.shape.graph.Connected ∧ C.shape.edgeCount = e :=
        ⟨hs.1, hs.2.2⟩
      simp [hs, ht]
    · have hs' : ¬(C.shape.graph.Connected ∧
          C.shape.graph.IsAcyclic ∧ C.representative.1.card = e) := by
        intro h
        apply hs
        exact ⟨h.1, h.2.1, by
          rw [C.shape_edgeCount_eq_representative_card]
          exact h.2.2⟩
      simp [hs'])

/-- The cyclic triple fiber is likewise a sub-sum of the full connected
triple count. -/
theorem cyclicTripleFiber_le_connectedShapeTripleMass
    {n e : Nat} (plant : SimpleGraph (Fin n)) :
    (∑ C : AmbientSupportClass n with
        C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
          C.shape.edgeCount = e,
      ((C.shape.nonInducedCopyCount plant ^ 2 *
        Fintype.card C.shape.Automorphism : Nat) : Real)) <=
      (connectedShapeTripleMass plant e : Real) := by
  exact_mod_cast (show
    (∑ C : AmbientSupportClass n with
        C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
          C.shape.edgeCount = e,
      C.shape.nonInducedCopyCount plant ^ 2 *
        Fintype.card C.shape.Automorphism) <=
      connectedShapeTripleMass plant e from by
    unfold connectedShapeTripleMass connectedShapeClasses
    rw [show Fintype.card (Fin n) = n by simp]
    simp only [Finset.sum_filter]
    apply Finset.sum_le_sum (N := Nat)
    intro C _
    by_cases hs : C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount = e
    · have ht : C.shape.graph.Connected ∧ C.shape.edgeCount = e :=
        ⟨hs.1, hs.2.2⟩
      simp [hs, ht]
    · have hs' : ¬(C.shape.graph.Connected ∧
          ¬C.shape.graph.IsAcyclic ∧ C.representative.1.card = e) := by
        intro h
        apply hs
        exact ⟨h.1, h.2.1, by
          rw [C.shape_edgeCount_eq_representative_card]
          exact h.2.2⟩
      simp [hs'])

/-- The paper's tree-fiber estimate. -/
theorem deterministicTreeBetaFiber_le
    {c : Real} {n m D e : Nat} (hc : 0 < c) (hn : 0 < n)
    (plant : SimpleGraph (Fin n))
    (hcount : connectedShapeTripleMass plant e <= m ^ 2 * D ^ (3 * e)) :
    deterministicTreeBetaFiber c plant e <=
      ((m : Real) ^ 2 / (n : Real)) *
        (((D : Real) ^ 3 / c) ^ e) := by
  let scale : Real := 1 / ((n : Real) * c ^ e)
  have hscale : 0 <= scale := by
    dsimp [scale]
    positivity
  calc
    deterministicTreeBetaFiber c plant e =
        scale *
          ∑ C : AmbientSupportClass n with
              C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
                C.shape.edgeCount = e,
            ((C.shape.nonInducedCopyCount plant ^ 2 *
              Fintype.card C.shape.Automorphism : Nat) : Real) := by
      unfold deterministicTreeBetaFiber
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      simpa [scale] using graphBetaWeight_eq_tree_scale hn C.shape plant
        hC.1 hC.2.1 hC.2.2
    _ <= scale * (connectedShapeTripleMass plant e : Real) :=
      mul_le_mul_of_nonneg_left
        (treeTripleFiber_le_connectedShapeTripleMass plant) hscale
    _ <= scale * ((m ^ 2 * D ^ (3 * e) : Nat) : Real) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hscale
    _ = ((m : Real) ^ 2 / (n : Real)) *
        (((D : Real) ^ 3 / c) ^ e) := by
      dsimp [scale]
      push_cast
      rw [pow_mul, div_pow]
      field_simp

/-- The paper's cyclic-fiber estimate: local sparsity absorbs the ambient
power, and the connected-copy estimate supplies the remaining geometric
factor. -/
theorem deterministicCyclicBetaFiber_le
    {c A : Real} {n m D e : Nat}
    (hc : 0 < c) (hn : 1 < n) (hA : 0 <= A)
    (plant : SimpleGraph (Fin n))
    (hcount : connectedShapeTripleMass plant e <= m ^ 2 * D ^ (3 * e))
    (hlocal : ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      C.shape.edgeCount = e →
      0 < C.shape.nonInducedCopyCount plant →
      (C.shape.edgeCount : Real) <=
        (1 + A / Real.log (n : Real)) * (C.shape.vertexCount : Real)) :
    deterministicCyclicBetaFiber c plant e <=
      (m : Real) ^ 2 *
        ((((D : Real) ^ 3 * Real.exp A) / c) ^ e) := by
  let scale : Real := (Real.exp A / c) ^ e
  have hscale : 0 <= scale := by
    dsimp [scale]
    positivity
  calc
    deterministicCyclicBetaFiber c plant e <=
        ∑ C : AmbientSupportClass n with
            C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
              C.shape.edgeCount = e,
          scale *
            ((C.shape.nonInducedCopyCount plant ^ 2 *
              Fintype.card C.shape.Automorphism : Nat) : Real) := by
      unfold deterministicCyclicBetaFiber
      apply Finset.sum_le_sum (N := Real)
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      by_cases hocc : 0 < C.shape.nonInducedCopyCount plant
      · simpa only [scale] using graphBetaWeight_le_cyclic_scale
          hc hn hA C.shape plant hC.1 hC.2.1 hC.2.2
            (hlocal C hC.1 hC.2.1 hC.2.2 hocc)
      · have hzero : C.shape.nonInducedCopyCount plant = 0 :=
          Nat.eq_zero_of_not_pos hocc
        simp [FiniteGraphShape.graphBetaWeight, betaWeight, hzero, hscale]
    _ = scale *
        ∑ C : AmbientSupportClass n with
            C.shape.graph.Connected ∧ ¬C.shape.graph.IsAcyclic ∧
              C.shape.edgeCount = e,
          ((C.shape.nonInducedCopyCount plant ^ 2 *
            Fintype.card C.shape.Automorphism : Nat) : Real) := by
      rw [Finset.mul_sum]
    _ <= scale * (connectedShapeTripleMass plant e : Real) :=
      mul_le_mul_of_nonneg_left
        (cyclicTripleFiber_le_connectedShapeTripleMass plant) hscale
    _ <= scale * ((m ^ 2 * D ^ (3 * e) : Nat) : Real) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hscale
    _ = (m : Real) ^ 2 *
        ((((D : Real) ^ 3 * Real.exp A) / c) ^ e) := by
      dsimp [scale]
      push_cast
      rw [pow_mul]
      simp only [div_pow, mul_pow]
      field_simp

/-- Sum the tree-fiber estimate over an arbitrary finite degree cutoff. -/
theorem deterministicTreeCutoffBetaMass_le_geometric
    {c : Real} {n m D K : Nat}
    (hc : 0 < c) (hn : 0 < n)
    (plant : SimpleGraph (Fin n))
    (hcount : ∀ e, connectedShapeTripleMass plant e <=
      m ^ 2 * D ^ (3 * e))
    (hq : ((D : Real) ^ 3 / c) < 1) :
    deterministicTreeCutoffBetaMass c plant K <=
      ((m : Real) ^ 2 / (n : Real)) *
        (1 - (D : Real) ^ 3 / c)⁻¹ := by
  let q : Real := (D : Real) ^ 3 / c
  let a : Real := (m : Real) ^ 2 / (n : Real)
  have hq0 : 0 <= q := by dsimp [q]; positivity
  have ha0 : 0 <= a := by dsimp [a]; positivity
  rw [deterministicTreeCutoffBetaMass_eq_sum_fibers]
  calc
    (∑ e ∈ Finset.Icc 1 K, deterministicTreeBetaFiber c plant e) <=
        ∑ e ∈ Finset.Icc 1 K, a * q ^ e := by
      apply Finset.sum_le_sum (N := Real)
      intro e _
      exact deterministicTreeBetaFiber_le hc hn plant (hcount e)
    _ = a * ∑ e ∈ Finset.Icc 1 K, q ^ e := by
      rw [Finset.mul_sum]
    _ <= a * (1 - q)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (finiteGeometricSum_le_inv_one_sub hq0 hq
          (Finset.Icc 1 K)) ha0
    _ = ((m : Real) ^ 2 / (n : Real)) *
        (1 - (D : Real) ^ 3 / c)⁻¹ := rfl

/-- Sum the cyclic-fiber estimate.  The occurrence restriction `start ≤ e`
encodes the girth lower bound and produces the geometric tail in the paper. -/
theorem deterministicCyclicCutoffBetaMass_le_geometricTail
    {c A : Real} {n m D K start : Nat}
    (hc : 0 < c) (hn : 1 < n) (hA : 0 <= A)
    (plant : SimpleGraph (Fin n))
    (hcount : ∀ e, connectedShapeTripleMass plant e <=
      m ^ 2 * D ^ (3 * e))
    (hlocal : ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount plant →
      C.shape.edgeCount <= K →
      (C.shape.edgeCount : Real) <=
        (1 + A / Real.log (n : Real)) * (C.shape.vertexCount : Real))
    (hgirth : ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount plant →
      start <= C.shape.edgeCount)
    (htheta : (((D : Real) ^ 3 * Real.exp A) / c) < 1) :
    deterministicCyclicCutoffBetaMass c plant K <=
      (m : Real) ^ 2 *
        (((((D : Real) ^ 3 * Real.exp A) / c) ^ start) /
          (1 - ((D : Real) ^ 3 * Real.exp A) / c)) := by
  let theta : Real := ((D : Real) ^ 3 * Real.exp A) / c
  let a : Real := (m : Real) ^ 2
  let indices : Finset Nat := (Finset.Icc 1 K).filter fun e => start <= e
  have htheta0 : 0 <= theta := by dsimp [theta]; positivity
  have ha0 : 0 <= a := by dsimp [a]; positivity
  have hfiber (e : Nat) (heK : e <= K) :
      deterministicCyclicBetaFiber c plant e <=
        if start <= e then a * theta ^ e else 0 := by
    by_cases hstart : start <= e
    · rw [if_pos hstart]
      exact deterministicCyclicBetaFiber_le hc hn hA plant (hcount e)
        (fun C hconn hcyclic hedge hocc =>
          hlocal C hconn hcyclic hocc (hedge.trans_le heK))
    · rw [if_neg hstart]
      have hzero : deterministicCyclicBetaFiber c plant e = 0 := by
        unfold deterministicCyclicBetaFiber
        apply Finset.sum_eq_zero
        intro C hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
        by_cases hocc : 0 < C.shape.nonInducedCopyCount plant
        · exact (hstart (hC.2.2 ▸ hgirth C hC.1 hC.2.1 hocc)).elim
        · have hcopyZero : C.shape.nonInducedCopyCount plant = 0 :=
            Nat.eq_zero_of_not_pos hocc
          simp [FiniteGraphShape.graphBetaWeight, betaWeight, hcopyZero]
      rw [hzero]
  have hsubset : indices ⊆ Finset.Ico start (K + 1) := by
    intro e he
    simp only [indices, Finset.mem_filter, Finset.mem_Icc] at he
    simp only [Finset.mem_Ico]
    omega
  rw [deterministicCyclicCutoffBetaMass_eq_sum_fibers]
  calc
    (∑ e ∈ Finset.Icc 1 K, deterministicCyclicBetaFiber c plant e) <=
      ∑ e ∈ Finset.Icc 1 K,
          if start <= e then a * theta ^ e else 0 := by
      exact Finset.sum_le_sum fun e he => hfiber e (Finset.mem_Icc.mp he).2
    _ = ∑ e ∈ indices, a * theta ^ e := by
      dsimp [indices]
      rw [Finset.sum_filter]
    _ = a * ∑ e ∈ indices, theta ^ e := by
      rw [Finset.mul_sum]
    _ <= a * ∑ e ∈ Finset.Ico start (K + 1), theta ^ e := by
      apply mul_le_mul_of_nonneg_left _ ha0
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro e _ _
      exact pow_nonneg htheta0 e
    _ <= a * (theta ^ start / (1 - theta)) :=
      mul_le_mul_of_nonneg_left
        (finiteGeometricIco_le_tail htheta0 htheta start (K + 1)) ha0
    _ = (m : Real) ^ 2 *
        (((((D : Real) ^ 3 * Real.exp A) / c) ^ start) /
          (1 - ((D : Real) ^ 3 * Real.exp A) / c)) := rfl

/-- The logarithmic-girth geometric tail beats the square of the canonical
plant size.  The exponent `3r/kappa` is the explicit slack used in the
manuscript. -/
theorem appendixPlantSize_sq_mul_geometricLogTail_vanishes
    {r kappa theta : Real}
    (hr : 0 < r) (hkappa : 0 < kappa)
    (htheta0 : 0 <= theta)
    (htheta : theta < Real.exp (-3 * r / kappa)) :
    Vanishes fun n : Nat =>
      (appendixPlantSize r n : Real) ^ 2 *
        (theta ^ Nat.ceil (kappa * Real.log (n : Real)) /
          (1 - theta)) := by
  let q0 : Real := Real.exp (-3 * r / kappa)
  have hq0pos : 0 < q0 := by dsimp [q0]; positivity
  have hq0lt : q0 < 1 := by
    dsimp [q0]
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < 3 * r / kappa := by positivity
    calc
      -3 * r / kappa = -(3 * r / kappa) := by ring
      _ < 0 := neg_neg_of_pos hpos
  have htheta1 : theta < 1 := htheta.trans hq0lt
  have hden : 0 < 1 - theta := sub_pos.mpr htheta1
  have htarget : Vanishes fun n : Nat =>
      (n : Real) ^ (-r) / (1 - theta) := by
    have hp : Vanishes fun n : Nat => (n : Real) ^ (-r) :=
      (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
    simpa only [zero_div] using hp.div_const (1 - theta)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
    have hnpos : (0 : Real) < n := by exact_mod_cast hn
    have hfloor : (appendixPlantSize r n : Real) <= (n : Real) ^ r :=
      Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have hmSq : (appendixPlantSize r n : Real) ^ 2 <=
        (n : Real) ^ (2 * r) := by
      calc
        (appendixPlantSize r n : Real) ^ 2 <=
            ((n : Real) ^ r) ^ 2 := by gcongr
        _ = (n : Real) ^ (2 * r) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hnpos.le]
          congr 1
          ring
    have hceil : kappa * Real.log (n : Real) <=
        (Nat.ceil (kappa * Real.log (n : Real)) : Real) :=
      Nat.le_ceil _
    have hpowQ0 :
        q0 ^ (Nat.ceil (kappa * Real.log (n : Real)) : Nat) <=
          q0 ^ (kappa * Real.log (n : Real)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hq0pos hq0lt.le hceil
    have hq0Formula :
        q0 ^ (kappa * Real.log (n : Real)) =
          (n : Real) ^ (-3 * r) := by
      dsimp [q0]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        Real.rpow_def_of_pos hnpos]
      congr 1
      field_simp [hkappa.ne']
    have hthetaPow :
        theta ^ Nat.ceil (kappa * Real.log (n : Real)) <=
          (n : Real) ^ (-3 * r) := by
      calc
        theta ^ Nat.ceil (kappa * Real.log (n : Real)) <=
            q0 ^ Nat.ceil (kappa * Real.log (n : Real)) :=
          pow_le_pow_left₀ htheta0 htheta.le _
        _ <= q0 ^ (kappa * Real.log (n : Real)) := hpowQ0
        _ = (n : Real) ^ (-3 * r) := hq0Formula
    have hproduct :
        (appendixPlantSize r n : Real) ^ 2 *
            theta ^ Nat.ceil (kappa * Real.log (n : Real)) <=
          (n : Real) ^ (2 * r) * (n : Real) ^ (-3 * r) := by
      exact mul_le_mul hmSq hthetaPow (pow_nonneg htheta0 _)
        (Real.rpow_nonneg hnpos.le _)
    calc
      (appendixPlantSize r n : Real) ^ 2 *
          (theta ^ Nat.ceil (kappa * Real.log (n : Real)) /
            (1 - theta)) =
          ((appendixPlantSize r n : Real) ^ 2 *
            theta ^ Nat.ceil (kappa * Real.log (n : Real))) /
              (1 - theta) := by ring
      _ <= ((n : Real) ^ (2 * r) * (n : Real) ^ (-3 * r)) /
          (1 - theta) :=
        div_le_div_of_nonneg_right hproduct hden.le
      _ = (n : Real) ^ (-r) / (1 - theta) := by
        rw [← Real.rpow_add hnpos]
        congr 2
        ring
  · exact htarget

/-- An explicit admissible null-density threshold for the deterministic
Appendix.  Above it, the tree series is geometric and the cyclic series has
enough exponential slack to beat `m_n^2`. -/
noncomputable def deterministicLargeCThreshold
    (D : Nat) (A r kappa : Real) : Real :=
  max 2 <| max ((D : Real) ^ 3 + 1) <|
    (((D : Real) ^ 3 * Real.exp A) /
        Real.exp (-3 * r / kappa) + 1)

theorem one_lt_deterministicLargeCThreshold
    (D : Nat) (A r kappa : Real) :
    1 < deterministicLargeCThreshold D A r kappa := by
  unfold deterministicLargeCThreshold
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem deterministic_largeC_geometric_ratios
    (D : Nat) (A r kappa : Real)
    (hr : 0 < r) (hkappa : 0 < kappa)
    {c : Real} (hc : deterministicLargeCThreshold D A r kappa <= c) :
    0 < c ∧
      (D : Real) ^ 3 / c < 1 ∧
      ((D : Real) ^ 3 * Real.exp A) / c <
        Real.exp (-3 * r / kappa) ∧
      ((D : Real) ^ 3 * Real.exp A) / c < 1 := by
  let q0 : Real := Real.exp (-3 * r / kappa)
  have hq0pos : 0 < q0 := by dsimp [q0]; positivity
  have hq0lt : q0 < 1 := by
    dsimp [q0]
    rw [Real.exp_lt_one_iff]
    calc
      -3 * r / kappa = -(3 * r / kappa) := by ring
      _ < 0 := neg_neg_of_pos (by positivity)
  have htwo : (2 : Real) <= c :=
    (le_max_left (2 : Real) _).trans hc
  have hcpos : 0 < c := by linarith
  have htreeRaw : (D : Real) ^ 3 + 1 <= c := by
    exact (le_max_left ((D : Real) ^ 3 + 1) _).trans
      ((le_max_right (2 : Real) _).trans hc)
  have hcyclicRaw :
      ((D : Real) ^ 3 * Real.exp A) / q0 + 1 <= c := by
    exact (le_max_right ((D : Real) ^ 3 + 1) _).trans
      ((le_max_right (2 : Real) _).trans hc)
  have htree : (D : Real) ^ 3 / c < 1 := by
    rw [div_lt_one hcpos]
    linarith
  have hcyclicDiv :
      ((D : Real) ^ 3 * Real.exp A) / q0 < c := by linarith
  have hcyclicMul :
      (D : Real) ^ 3 * Real.exp A < c * q0 :=
    (div_lt_iff₀ hq0pos).mp hcyclicDiv
  have hcyclic :
      ((D : Real) ^ 3 * Real.exp A) / c < q0 :=
    (div_lt_iff₀ hcpos).mpr (by simpa only [mul_comm] using hcyclicMul)
  exact ⟨hcpos, htree, hcyclic, hcyclic.trans hq0lt⟩

/-- Analytic low-degree conclusion for any deterministic graph sequence
satisfying the three structural inputs of Appendix A: connected-copy
counting, local sparsity, and logarithmic girth. -/
theorem deterministic_connectedCutoffBetaMass_vanishes
    (D : Nat) (A r kappa : Real)
    (hr : r ∈ Set.Ioo (0 : Real) (1 / 2 : Real))
    (hA : 0 <= A) (hkappa : 0 < kappa)
    (plant : ∀ n, SimpleGraph (Fin n))
    (hcount : ∀ n e, connectedShapeTripleMass (plant n) e <=
      appendixPlantSize r n ^ 2 * D ^ (3 * e))
    (hlocal : ∀ᶠ n in atTop, ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount (plant n) →
      C.shape.edgeCount <= appendixDegreeCutoff n →
      (C.shape.edgeCount : Real) <=
        (1 + A / Real.log (n : Real)) * (C.shape.vertexCount : Real))
    (hgirth : ∀ᶠ n in atTop, ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount (plant n) →
      kappa * Real.log (n : Real) <= (C.shape.edgeCount : Real))
    {c : Real} (hc : deterministicLargeCThreshold D A r kappa <= c) :
    Vanishes fun n =>
      connectedCutoffBetaMass c (appendixDegreeCutoff n) (plant n) := by
  obtain ⟨hcpos, htreeRatio, hcyclicSlack, hcyclicRatio⟩ :=
    deterministic_largeC_geometric_ratios D A r kappa hr.1 hkappa hc
  let treeEnvelope : Nat -> Real := fun n =>
    ((appendixPlantSize r n : Real) ^ 2 / (n : Real)) *
      (1 - (D : Real) ^ 3 / c)⁻¹
  let theta : Real := ((D : Real) ^ 3 * Real.exp A) / c
  let cyclicEnvelope : Nat -> Real := fun n =>
    (appendixPlantSize r n : Real) ^ 2 *
      (theta ^ Nat.ceil (kappa * Real.log (n : Real)) /
        (1 - theta))
  have htreeEnvelope : Vanishes treeEnvelope := by
    have hbase := appendixPlantSize_sq_div_index_vanishes hr.2
    simpa only [treeEnvelope, zero_mul] using
      hbase.mul_const (1 - (D : Real) ^ 3 / c)⁻¹
  have hcyclicEnvelope : Vanishes cyclicEnvelope := by
    exact appendixPlantSize_sq_mul_geometricLogTail_vanishes
      hr.1 hkappa (by positivity)
        (by simpa only [theta] using hcyclicSlack)
  have htreeUpper : ∀ᶠ n in atTop,
      deterministicTreeCutoffBetaMass c (plant n)
          (appendixDegreeCutoff n) <= treeEnvelope n := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
    exact deterministicTreeCutoffBetaMass_le_geometric hcpos hn (plant n)
      (hcount n) htreeRatio
  have hcyclicUpper : ∀ᶠ n in atTop,
      deterministicCyclicCutoffBetaMass c (plant n)
          (appendixDegreeCutoff n) <= cyclicEnvelope n := by
    filter_upwards [hlocal, hgirth,
      Filter.eventually_gt_atTop (1 : Nat)] with n hlocalN hgirthN hn
    exact deterministicCyclicCutoffBetaMass_le_geometricTail
      hcpos hn hA (plant n) (hcount n) hlocalN
      (fun C hconn hcyclic hocc =>
        Nat.ceil_le.mpr (hgirthN C hconn hcyclic hocc))
      hcyclicRatio
  have htreeNonneg : ∀ n,
      0 <= deterministicTreeCutoffBetaMass c (plant n)
        (appendixDegreeCutoff n) := by
    intro n
    unfold deterministicTreeCutoffBetaMass
    exact Finset.sum_nonneg fun C _ => by
      unfold FiniteGraphShape.graphBetaWeight betaWeight
      positivity
  have hcyclicNonneg : ∀ n,
      0 <= deterministicCyclicCutoffBetaMass c (plant n)
        (appendixDegreeCutoff n) := by
    intro n
    unfold deterministicCyclicCutoffBetaMass
    exact Finset.sum_nonneg fun C _ => by
      unfold FiniteGraphShape.graphBetaWeight betaWeight
      positivity
  have htreeVanishes : Vanishes fun n =>
      deterministicTreeCutoffBetaMass c (plant n)
        (appendixDegreeCutoff n) :=
    squeeze_zero' (Eventually.of_forall htreeNonneg) htreeUpper htreeEnvelope
  have hcyclicVanishes : Vanishes fun n =>
      deterministicCyclicCutoffBetaMass c (plant n)
        (appendixDegreeCutoff n) :=
    squeeze_zero' (Eventually.of_forall hcyclicNonneg)
      hcyclicUpper hcyclicEnvelope
  simpa only [connectedCutoffBetaMass_eq_tree_add_cyclic] using
    htreeVanishes.add hcyclicVanishes

/-- The canonical logarithmic cutoff is `o(sqrt n)`, the uniform range in
which the exact Fourier weight is comparable to its leading beta weight. -/
theorem appendixDegreeCutoff_isLittleO_sqrt :
    (fun n : Nat => (appendixDegreeCutoff n : Real)) =o[atTop]
      (fun n : Nat => Real.sqrt (n : Real)) := by
  have hlog :
      (fun n : Nat => Real.log (n : Real) ^ 2) =o[atTop]
        (fun n : Nat => Real.sqrt (n : Real)) := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : Real)
        (by norm_num : (0 : Real) < 1 / 2)).comp_tendsto
          tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : Nat => Real.sqrt (n : Real)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
  have hone : (fun _n : Nat => (1 : Real)) =o[atTop]
      (fun n : Nat => Real.sqrt (n : Real)) := by
    rw [isLittleO_const_left_of_ne one_ne_zero]
    exact hsqrt.congr' <| Eventually.of_forall fun n =>
      (Real.norm_of_nonneg (Real.sqrt_nonneg (n : Real))).symm
  have hsum := hone.add hlog
  have hmajor :
      (fun n : Nat => (appendixDegreeCutoff n : Real)) =O[atTop]
        (fun n : Nat => 1 + Real.log (n : Real) ^ 2) := by
    apply Eventually.isBigO
    exact Eventually.of_forall fun n => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      simpa only [appendixDegreeCutoff, add_comm] using
        (Nat.ceil_lt_add_one
          (sq_nonneg (Real.log (n : Real)))).le
  exact hmajor.trans_isLittleO hsum

/-- Vanishing cutoff beta mass implies the exact deterministic planted
low-degree norm tends to one.  This is the precise alpha-to-beta transfer
used at the end of the revised Appendix proof. -/
theorem plantedLowDegreeNormSq_tendsToOne_of_cutoffBetaMass
    (c : Real) (hc : 0 < c)
    (D : Nat -> Nat) (plant : ∀ n, SimpleGraph (Fin n))
    (hD : (fun n : Nat => (D n : Real)) =o[atTop]
      (fun n : Nat => Real.sqrt (n : Real)))
    (hbeta : Vanishes fun n => cutoffBetaMass c (D n) (plant n)) :
    TendsToOne fun n =>
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
        (plant n) (D n) := by
  have hcompare := alpha_beta_eventually_between_half_and_two c hc hD
  have hp := eventually_sparseBernoulliParameter_p_eq hc
  have hupper : ∀ᶠ n in atTop,
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
          (plant n) (D n) - 1 <=
        2 * cutoffBetaMass c (D n) (plant n) := by
    filter_upwards [hcompare, hp] with n hn hpn
    rw [plantedLowDegreeNormSq_sub_one_eq_sum_alphaWeights
      (sparseBernoulliParameter c n) (plant n) (D n) c hpn]
    unfold cutoffBetaMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum (N := Real)
    intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    by_cases hocc : 0 < C.shape.nonInducedCopyCount (plant n)
    · have hedge : 0 < C.shape.edgeCount := by
        rw [C.shape_edgeCount_eq_representative_card]
        exact C.representative.2.card_pos
      let datum : LeadingTermDatum n :=
        C.shape.leadingTermDatumOfOccurrence (plant n) hedge hocc
      have hdatum := (hn datum hC).2
      dsimp [datum, FiniteGraphShape.leadingTermDatumOfOccurrence] at hdatum
      exact hdatum
    · have hzero : C.shape.nonInducedCopyCount (plant n) = 0 :=
        Nat.eq_zero_of_not_pos hocc
      simp [alphaWeight, FiniteGraphShape.graphBetaWeight, betaWeight, hzero]
  have hnonneg : ∀ n,
      0 <= plantedLowDegreeNormSq (sparseBernoulliParameter c n)
          (plant n) (D n) - 1 := by
    intro n
    exact sub_nonneg.mpr (one_le_plantedLowDegreeNormSq _ _ _)
  have hdiff : Vanishes fun n =>
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
          (plant n) (D n) - 1 :=
    squeeze_zero' (Eventually.of_forall hnonneg) hupper
      (hbeta.const_mul 2)
  exact tendsToOne_iff_vanishes_sub.mpr hdiff

/-- Complete low-degree half of the revised deterministic Appendix theorem,
from its three graph-theoretic inputs. -/
theorem deterministic_lowDegreeIndistinguishability
    (D : Nat) (A r kappa : Real)
    (hr : r ∈ Set.Ioo (0 : Real) (1 / 2 : Real))
    (hA : 0 <= A) (hkappa : 0 < kappa)
    (plant : ∀ n, SimpleGraph (Fin n))
    (hcount : ∀ n e, connectedShapeTripleMass (plant n) e <=
      appendixPlantSize r n ^ 2 * D ^ (3 * e))
    (hlocal : ∀ᶠ n in atTop, ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount (plant n) →
      C.shape.edgeCount <= appendixDegreeCutoff n →
      (C.shape.edgeCount : Real) <=
        (1 + A / Real.log (n : Real)) * (C.shape.vertexCount : Real))
    (hgirth : ∀ᶠ n in atTop, ∀ C : AmbientSupportClass n,
      C.shape.graph.Connected → ¬C.shape.graph.IsAcyclic →
      0 < C.shape.nonInducedCopyCount (plant n) →
      kappa * Real.log (n : Real) <= (C.shape.edgeCount : Real))
    {c : Real} (hc : deterministicLargeCThreshold D A r kappa <= c) :
    TendsToOne fun n =>
      plantedLowDegreeNormSq (sparseBernoulliParameter c n)
        (plant n) (appendixDegreeCutoff n) := by
  have hcpos :=
    (deterministic_largeC_geometric_ratios D A r kappa
      hr.1 hkappa hc).1
  have hconnected := deterministic_connectedCutoffBetaMass_vanishes
    D A r kappa hr hA hkappa plant hcount hlocal hgirth hc
  have hbeta := cutoffBetaMass_vanishes_of_connected
    c hcpos appendixDegreeCutoff plant hconnected
  exact plantedLowDegreeNormSq_tendsToOne_of_cutoffBetaMass
    c hcpos appendixDegreeCutoff plant
      appendixDegreeCutoff_isLittleO_sqrt hbeta

end

end LowDegree
