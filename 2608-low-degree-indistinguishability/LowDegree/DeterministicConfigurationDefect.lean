import LowDegree.DeterministicConfigurationLocalSparsity
import LowDegree.DeterministicConfigurationModelBridge
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Fintype.Sum

/-!
# Projection defects in the finite configuration model

This module controls the pairs lost when a configuration is projected to a
simple graph.  A lost pair is charged either to a loop presentation or to an
ordered collision between two non-loop half-edges having the same projected
dart.  The latter charge is encoded by two disjoint prescribed pairs, so the
exact uniform-pairing probability from
`DeterministicConfigurationLocalSparsity` applies.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A generic collision bound for a finite surjection -/

/-- Ordered distinct pairs in one fibre of a finite function. -/
abbrev FunctionFiberCollision {A B : Type*} (f : A → B) :=
  {p : A × A // p.1 ≠ p.2 ∧ f p.1 = f p.2}

noncomputable def surjectiveSection {A B : Type*} (f : A → B)
    (hf : Function.Surjective f) : B → A :=
  fun b ↦ Classical.choose (hf b)

@[simp] theorem surjectiveSection_spec {A B : Type*} (f : A → B)
    (hf : Function.Surjective f) (b : B) :
    f (surjectiveSection f hf b) = b :=
  Classical.choose_spec (hf b)

/-- Encode each point either by its fibre label, when it is the selected
representative, or by its collision with the selected representative. -/
noncomputable def surjectionCollisionCode {A B : Type*} (f : A → B)
    (hf : Function.Surjective f) (a : A) :
    B ⊕ FunctionFiberCollision f :=
  if ha : a = surjectiveSection f hf (f a) then
    Sum.inl (f a)
  else
    Sum.inr ⟨(a, surjectiveSection f hf (f a)), ha,
      (surjectiveSection_spec f hf (f a)).symm⟩

theorem surjectionCollisionCode_injective {A B : Type*} (f : A → B)
    (hf : Function.Surjective f) :
    Function.Injective (surjectionCollisionCode f hf) := by
  intro a a' haa'
  by_cases ha : a = surjectiveSection f hf (f a)
  · by_cases ha' : a' = surjectiveSection f hf (f a')
    · simp only [surjectionCollisionCode, dif_pos ha, dif_pos ha',
        Sum.inl.injEq] at haa'
      calc
        a = surjectiveSection f hf (f a) := ha
        _ = surjectiveSection f hf (f a') := congrArg _ haa'
        _ = a' := ha'.symm
    · dsimp only [surjectionCollisionCode] at haa'
      rw [dif_pos ha, dif_neg ha'] at haa'
      cases haa'
  · by_cases ha' : a' = surjectiveSection f hf (f a')
    · dsimp only [surjectionCollisionCode] at haa'
      rw [dif_neg ha, dif_pos ha'] at haa'
      cases haa'
    · simp only [surjectionCollisionCode, dif_neg ha, dif_neg ha',
        Sum.inr.injEq] at haa'
      exact congrArg (fun z : FunctionFiberCollision f ↦ z.1.1) haa'

/-- A finite surjection loses at most one point per ordered fibre collision. -/
theorem card_sub_card_le_functionFiberCollision
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) :
    Fintype.card A - Fintype.card B ≤
      Fintype.card (FunctionFiberCollision f) := by
  have hcard : Fintype.card A ≤
      Fintype.card (B ⊕ FunctionFiberCollision f) :=
    Fintype.card_le_of_injective _
      (surjectionCollisionCode_injective f hf)
  simp only [Fintype.card_sum] at hcard
  omega

/-! ## Loop and parallel-pair presentations -/

/-- An ordered pair of distinct sockets. -/
abbrev OrderedDistinctSocketPair (D : ℕ) :=
  {p : Fin D × Fin D // p.1 ≠ p.2}

/-- One ordered presentation of a loop pair. -/
abbrev ConfigurationLoopPresentation (m D : ℕ) :=
  Fin m × OrderedDistinctSocketPair D

namespace ConfigurationLoopPresentation

variable {m D : ℕ}

def leftEndpoint (w : ConfigurationLoopPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1, w.2.1.1)

def rightEndpoint (w : ConfigurationLoopPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1, w.2.1.2)

def pairs (w : ConfigurationLoopPresentation m D) :
    List (ConfigurationHalfEdge m D × ConfigurationHalfEdge m D) :=
  [(w.leftEndpoint, w.rightEndpoint)]

def Realized (C : Configuration m D)
    (w : ConfigurationLoopPresentation m D) : Prop :=
  C.partner w.leftEndpoint = w.rightEndpoint

@[simp] theorem mem_event
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    (w : ConfigurationLoopPresentation m D)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    sigma ∈ conjugatePairsEvent pairing w.pairs ↔
      conjugatedPartner pairing sigma w.leftEndpoint = w.rightEndpoint := by
  simp [pairs]

theorem endpoints_nodup (w : ConfigurationLoopPresentation m D) :
    (prescribedPairEndpoints w.pairs).Nodup := by
  simp [pairs, leftEndpoint, rightEndpoint, w.2.2]

end ConfigurationLoopPresentation

/-- One ordered presentation of two parallel non-loop configuration pairs. -/
abbrev ConfigurationParallelPresentation (m D : ℕ) :=
  {uv : Fin m × Fin m // uv.1 ≠ uv.2} ×
    OrderedDistinctSocketPair D × OrderedDistinctSocketPair D

namespace ConfigurationParallelPresentation

variable {m D : ℕ}

def leftEndpointOne (w : ConfigurationParallelPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1.1.1, w.2.1.1.1)

def rightEndpointOne (w : ConfigurationParallelPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1.1.2, w.2.2.1.1)

def leftEndpointTwo (w : ConfigurationParallelPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1.1.1, w.2.1.1.2)

def rightEndpointTwo (w : ConfigurationParallelPresentation m D) :
    ConfigurationHalfEdge m D :=
  (w.1.1.2, w.2.2.1.2)

def pairs (w : ConfigurationParallelPresentation m D) :
    List (ConfigurationHalfEdge m D × ConfigurationHalfEdge m D) :=
  [(w.leftEndpointOne, w.rightEndpointOne),
    (w.leftEndpointTwo, w.rightEndpointTwo)]

def Realized (C : Configuration m D)
    (w : ConfigurationParallelPresentation m D) : Prop :=
  C.partner w.leftEndpointOne = w.rightEndpointOne ∧
    C.partner w.leftEndpointTwo = w.rightEndpointTwo

@[simp] theorem mem_event
    (pairing : Equiv.Perm (ConfigurationHalfEdge m D))
    (w : ConfigurationParallelPresentation m D)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m D)) :
    sigma ∈ conjugatePairsEvent pairing w.pairs ↔
      conjugatedPartner pairing sigma w.leftEndpointOne = w.rightEndpointOne ∧
      conjugatedPartner pairing sigma w.leftEndpointTwo = w.rightEndpointTwo := by
  simp [pairs]

theorem endpoints_nodup (w : ConfigurationParallelPresentation m D) :
    (prescribedPairEndpoints w.pairs).Nodup := by
  rcases w with ⟨⟨⟨u, v⟩, huv⟩, ⟨⟨i, j⟩, hij⟩, ⟨⟨k, l⟩, hkl⟩⟩
  simp [pairs, prescribedPairEndpoints, leftEndpointOne,
    rightEndpointOne, leftEndpointTwo, rightEndpointTwo,
    huv, hij, hkl]
  intro hv
  exact (huv hv.symm).elim

end ConfigurationParallelPresentation

/-! ## Projection defect dominated by realized presentations -/

namespace Configuration

variable {m D : ℕ}

noncomputable def loopHalfEdges (C : Configuration m D) :
    Finset (ConfigurationHalfEdge m D) :=
  Finset.univ.filter fun h ↦ (C.partner h).1 = h.1

noncomputable def nonloopHalfEdges (C : Configuration m D) :
    Finset (ConfigurationHalfEdge m D) :=
  Finset.univ.filter fun h ↦ (C.partner h).1 ≠ h.1

abbrev NonloopHalfEdge (C : Configuration m D) :=
  {h : ConfigurationHalfEdge m D // h ∈ C.nonloopHalfEdges}

def nonloopHalfEdgeDart (C : Configuration m D) (h : C.NonloopHalfEdge) :
    C.projectedGraph.Dart :=
  ⟨(h.1.1, (C.partner h.1).1), by
    rw [C.projectedGraph_adj]
    refine ⟨?_, h.1.2, rfl⟩
    exact ((Finset.mem_filter.mp h.2).2).symm⟩

theorem nonloopHalfEdgeDart_surjective (C : Configuration m D) :
    Function.Surjective C.nonloopHalfEdgeDart := by
  rintro ⟨⟨u, v⟩, huv⟩
  rw [C.projectedGraph_adj] at huv
  rcases huv with ⟨huv, i, hi⟩
  let h : ConfigurationHalfEdge m D := (u, i)
  have hnonloop : h ∈ C.nonloopHalfEdges := by
    simp only [nonloopHalfEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, h]
    intro heq
    apply huv
    calc
      u = C.socketNeighbor u i := by simpa [socketNeighbor, h] using heq.symm
      _ = v := hi
  refine ⟨⟨h, hnonloop⟩, ?_⟩
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · simpa [nonloopHalfEdgeDart, socketNeighbor, h] using hi

abbrev NonloopDartCollision (C : Configuration m D) :=
  FunctionFiberCollision C.nonloopHalfEdgeDart

noncomputable def loopHalfEdgePresentation (C : Configuration m D)
    (h : {h : ConfigurationHalfEdge m D // h ∈ C.loopHalfEdges}) :
    {w : ConfigurationLoopPresentation m D // w.Realized C} := by
  let j : Fin D := (C.partner h.1).2
  have hij : h.1.2 ≠ j := by
    intro hij
    apply C.partner_ne h.1
    apply Prod.ext
    · exact (Finset.mem_filter.mp h.2).2
    · exact hij.symm
  let w : ConfigurationLoopPresentation m D :=
    (h.1.1, ⟨(h.1.2, j), hij⟩)
  refine ⟨w, ?_⟩
  apply Prod.ext
  · exact (Finset.mem_filter.mp h.2).2
  · rfl

theorem loopHalfEdgePresentation_injective (C : Configuration m D) :
    Function.Injective C.loopHalfEdgePresentation := by
  intro h h' heq
  apply Subtype.ext
  have hw := congrArg
    (fun z : {w : ConfigurationLoopPresentation m D // w.Realized C} ↦
      (z.1.1, z.1.2.1.1)) heq
  simpa [loopHalfEdgePresentation] using hw

noncomputable def collisionParallelPresentation (C : Configuration m D)
    (p : C.NonloopDartCollision) :
    {w : ConfigurationParallelPresentation m D // w.Realized C} := by
  let h := p.1.1.1
  let h' := p.1.2.1
  have hdart := p.2.2
  have hsource : h.1 = h'.1 :=
    congrArg (fun q ↦ q.fst) hdart
  have htarget : (C.partner h).1 = (C.partner h').1 :=
    congrArg (fun q ↦ q.snd) hdart
  have hsockets : h.2 ≠ h'.2 := by
    intro hs
    apply p.2.1
    apply Subtype.ext
    apply Prod.ext hsource hs
  have hpartnerSockets : (C.partner h).2 ≠ (C.partner h').2 := by
    intro hs
    apply p.2.1
    apply Subtype.ext
    apply C.partner.injective
    apply Prod.ext htarget hs
  have huv : h.1 ≠ (C.partner h).1 := by
    exact ((Finset.mem_filter.mp p.1.1.2).2).symm
  let w : ConfigurationParallelPresentation m D :=
    (⟨(h.1, (C.partner h).1), huv⟩,
      ⟨(h.2, h'.2), hsockets⟩,
      ⟨(C.partner h |>.2, C.partner h' |>.2), hpartnerSockets⟩)
  refine ⟨w, ?_⟩
  constructor
  · dsimp [w, ConfigurationParallelPresentation.leftEndpointOne,
      ConfigurationParallelPresentation.rightEndpointOne]
  · dsimp [w, ConfigurationParallelPresentation.leftEndpointTwo,
      ConfigurationParallelPresentation.rightEndpointTwo]
    have hh' : (h.1, h'.2) = h' := by
      exact Prod.ext hsource rfl
    rw [hh']
    exact Prod.ext htarget.symm rfl

theorem collisionParallelPresentation_injective (C : Configuration m D) :
    Function.Injective C.collisionParallelPresentation := by
  intro p p' heq
  have hfirst := congrArg
    (fun z : {w : ConfigurationParallelPresentation m D // w.Realized C} ↦
      z.1.leftEndpointOne) heq
  have hsecond := congrArg
    (fun z : {w : ConfigurationParallelPresentation m D // w.Realized C} ↦
      z.1.leftEndpointTwo) heq
  have hfirst' : p.1.1.1 = p'.1.1.1 := by
    simpa [collisionParallelPresentation,
      ConfigurationParallelPresentation.leftEndpointOne] using hfirst
  have hsecondSocket : p.1.2.1.2 = p'.1.2.1.2 := by
    have := congrArg Prod.snd hsecond
    simpa [collisionParallelPresentation,
      ConfigurationParallelPresentation.leftEndpointTwo] using this
  have hsource : p.1.1.1.1 = p.1.2.1.1 := by
    exact congrArg (fun q ↦ q.fst) p.2.2
  have hsource' : p'.1.1.1.1 = p'.1.2.1.1 := by
    exact congrArg (fun q ↦ q.fst) p'.2.2
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hfirst'
  · apply Subtype.ext
    apply Prod.ext
    · exact hsource.symm.trans
        ((congrArg Prod.fst hfirst').trans hsource')
    · exact hsecondSocket

/-- Number of realized ordered loop presentations. -/
def loopPresentationCount (C : Configuration m D) : ℕ :=
  Fintype.card {w : ConfigurationLoopPresentation m D // w.Realized C}

/-- Number of realized ordered parallel-pair presentations. -/
def parallelPresentationCount (C : Configuration m D) : ℕ :=
  Fintype.card {w : ConfigurationParallelPresentation m D // w.Realized C}

theorem card_loopHalfEdges_le_loopPresentationCount
    (C : Configuration m D) :
    C.loopHalfEdges.card ≤ C.loopPresentationCount := by
  rw [loopPresentationCount, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective _
    C.loopHalfEdgePresentation_injective

theorem card_nonloopDartCollision_le_parallelPresentationCount
    (C : Configuration m D) :
    Fintype.card C.NonloopDartCollision ≤ C.parallelPresentationCount := by
  unfold parallelPresentationCount
  exact Fintype.card_le_of_injective _
    C.collisionParallelPresentation_injective

/-- The projection defect is charged deterministically to loop and parallel
presentations.  The restriction to `d+d` sockets records the even degree of
the configuration model used in the Appendix construction. -/
theorem projectionDefect_le_loop_add_parallelPresentationCount
    (C : Configuration m (d + d)) :
    C.projectionDefect ≤
      C.loopPresentationCount + C.parallelPresentationCount := by
  letI : DecidableEq C.NonloopHalfEdge := Classical.decEq _
  letI : DecidableEq C.projectedGraph.Dart := Classical.decEq _
  have hsurj : Function.Surjective C.nonloopHalfEdgeDart :=
    C.nonloopHalfEdgeDart_surjective
  have htarget : Fintype.card C.projectedGraph.Dart ≤
      Fintype.card C.NonloopHalfEdge :=
    Fintype.card_le_of_surjective _ hsurj
  have hcollision : Fintype.card C.NonloopHalfEdge -
      Fintype.card C.projectedGraph.Dart ≤
      Fintype.card (FunctionFiberCollision C.nonloopHalfEdgeDart) :=
    card_sub_card_le_functionFiberCollision C.nonloopHalfEdgeDart hsurj
  have hpartition : C.loopHalfEdges.card + C.nonloopHalfEdges.card =
      Fintype.card (ConfigurationHalfEdge m (d + d)) := by
    simpa [loopHalfEdges, nonloopHalfEdges] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (ConfigurationHalfEdge m (d + d))))
        (fun h ↦ (C.partner h).1 = h.1))
  have hA : Fintype.card C.NonloopHalfEdge =
      C.nonloopHalfEdges.card := by
    simp
  have hB : Fintype.card C.projectedGraph.Dart =
      2 * C.projectedGraph.edgeFinset.card := by
    exact C.projectedGraph.dart_card_eq_twice_card_edges
  have hhalf : m * (d + d) / 2 = m * d := by
    rw [Nat.mul_add]
    omega
  have hraw : C.projectionDefect ≤
      C.loopHalfEdges.card +
        Fintype.card (FunctionFiberCollision C.nonloopHalfEdgeDart) := by
    unfold projectionDefect
    simp only [Fintype.card_prod, Fintype.card_fin] at hpartition
    rw [hhalf]
    rw [hA, hB] at htarget hcollision
    omega
  have hparallel :
      Fintype.card (FunctionFiberCollision C.nonloopHalfEdgeDart) ≤
        C.parallelPresentationCount :=
    Fintype.card_le_of_injective _
      C.collisionParallelPresentation_injective
  exact hraw.trans (Nat.add_le_add
    C.card_loopHalfEdges_le_loopPresentationCount
    hparallel)

theorem projectionDefect_cast_le_loop_add_parallelPresentationCount
    (C : Configuration m (d + d)) :
    (C.projectionDefect : ℝ) ≤
      (C.loopPresentationCount : ℝ) +
        (C.parallelPresentationCount : ℝ) := by
  exact_mod_cast C.projectionDefect_le_loop_add_parallelPresentationCount

end Configuration

/-! ## Indicator-count form and first moments -/

/-- Real-valued count of a finite family of predicates. -/
noncomputable def finitePredicateCountReal
    {I : Type*} [Fintype I] (p : I → Prop) : ℝ :=
  ∑ i, if p i then 1 else 0

theorem finitePredicateCountReal_eq_card
    {I : Type*} [Fintype I] (p : I → Prop) :
    finitePredicateCountReal p = (Fintype.card {i : I // p i} : ℝ) := by
  classical
  rw [Fintype.card_subtype]
  unfold finitePredicateCountReal
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_filter]

noncomputable def configurationLoopPresentationCountReal
    (C : Configuration m D) : ℝ :=
  finitePredicateCountReal fun w : ConfigurationLoopPresentation m D ↦
    w.Realized C

noncomputable def configurationParallelPresentationCountReal
    (C : Configuration m D) : ℝ :=
  finitePredicateCountReal fun w : ConfigurationParallelPresentation m D ↦
    w.Realized C

theorem configurationLoopPresentationCountReal_eq
    (C : Configuration m D) :
    configurationLoopPresentationCountReal C =
      (C.loopPresentationCount : ℝ) := by
  exact finitePredicateCountReal_eq_card _

theorem configurationParallelPresentationCountReal_eq
    (C : Configuration m D) :
    configurationParallelPresentationCountReal C =
      (C.parallelPresentationCount : ℝ) := by
  exact finitePredicateCountReal_eq_card _

theorem projectionDefect_cast_le_presentationCounts
    (C : Configuration m (d + d)) :
    (C.projectionDefect : ℝ) ≤
      configurationLoopPresentationCountReal C +
        configurationParallelPresentationCountReal C := by
  rw [configurationLoopPresentationCountReal_eq,
    configurationParallelPresentationCountReal_eq]
  exact C.projectionDefect_cast_le_loop_add_parallelPresentationCount

/-- Real-valued count of a finite family of events at one outcome. -/
noncomputable def finiteEventCountReal
    {Omega I : Type*} [Fintype Omega] [Fintype I]
    (event : I → Finset Omega) (omega : Omega) : ℝ :=
  ∑ i, if omega ∈ event i then 1 else 0

theorem expect_finiteEventCountReal
    {Omega I : Type*} [Fintype Omega] [Fintype I]
    (q : FiniteLaw Omega) (event : I → Finset Omega) :
    q.expect (finiteEventCountReal event) =
      ∑ i, q.prob (event i) := by
  classical
  unfold finiteEventCountReal FiniteLaw.expect FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext omega
    simp
  · intro omega homega
    rfl

theorem configurationLoopPresentationCountReal_randomConfiguration
    (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    configurationLoopPresentationCountReal (randomConfiguration m d sigma) =
      finiteEventCountReal
        (fun w : ConfigurationLoopPresentation m (d + d) ↦
          conjugatePairsEvent
            (Configuration.standardConfiguration m d).partner w.pairs)
        sigma := by
  unfold configurationLoopPresentationCountReal finitePredicateCountReal
  unfold finiteEventCountReal
  apply Finset.sum_congr rfl
  intro w _hw
  simp only [ConfigurationLoopPresentation.Realized,
    randomConfiguration_partner,
    ConfigurationLoopPresentation.mem_event]
  by_cases hp : conjugatedPartner
      (Configuration.standardConfiguration m d).partner sigma w.leftEndpoint =
        w.rightEndpoint <;> simp [hp]

theorem configurationParallelPresentationCountReal_randomConfiguration
    (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    configurationParallelPresentationCountReal (randomConfiguration m d sigma) =
      finiteEventCountReal
        (fun w : ConfigurationParallelPresentation m (d + d) ↦
          conjugatePairsEvent
            (Configuration.standardConfiguration m d).partner w.pairs)
        sigma := by
  unfold configurationParallelPresentationCountReal finitePredicateCountReal
  unfold finiteEventCountReal
  apply Finset.sum_congr rfl
  intro w _hw
  simp only [ConfigurationParallelPresentation.Realized,
    randomConfiguration_partner,
    ConfigurationParallelPresentation.mem_event]
  by_cases hp : conjugatedPartner
      (Configuration.standardConfiguration m d).partner sigma w.leftEndpointOne =
        w.rightEndpointOne
  · by_cases hp' : conjugatedPartner
        (Configuration.standardConfiguration m d).partner sigma w.leftEndpointTwo =
          w.rightEndpointTwo <;> simp [hp, hp']
  · simp [hp]

/-- Version of the exact prescribed-pair formula for the repository's
concrete `configurationPermutationLaw`.  The generic theorem uses a
classically synthesized permutation Fintype, whereas this law uses the
canonical decidable equality on finite socket labels; rewriting both
permutation cardinalities as factorials bridges the harmless instance
difference. -/
theorem configurationPermutationLaw_prob_conjugatePairsEvent
    (m d : ℕ)
    (pairs : List
      (ConfigurationHalfEdge m (d + d) × ConfigurationHalfEdge m (d + d)))
    (hdisjoint : (prescribedPairEndpoints pairs).Nodup) :
    (configurationPermutationLaw m d).prob
        (conjugatePairsEvent
          (Configuration.standardConfiguration m d).partner pairs) =
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ)⁻¹ := by
  rw [configurationPermutationLaw, FiniteLaw.uniform_prob]
  have hcard : Fintype.card (ConfigurationHalfEdge m (d + d)) =
      m * (d + d) := by simp
  rw [← Nat.card_eq_fintype_card, Nat.card_perm,
    Nat.card_eq_fintype_card, hcard]
  letI : DecidableEq (ConfigurationHalfEdge m (d + d)) := Classical.decEq _
  have hcount := prescribedPairDenominator_mul_event_card
    (Configuration.standardConfiguration m d).partner
    (Configuration.standardConfiguration m d).partner_involutive
    (Configuration.standardConfiguration m d).partner_ne
    pairs hdisjoint
  rw [Fintype.card_perm, hcard] at hcount
  have hdenNat := prescribedPairDenominator_pos pairs hdisjoint
  rw [hcard] at hdenNat
  have hden :
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  have hperm : ((Nat.factorial (m * (d + d)) : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hcountReal :
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ) *
          ((conjugatePairsEvent
            (Configuration.standardConfiguration m d).partner pairs).card : ℝ) =
        ((Nat.factorial (m * (d + d)) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  field_simp [hden, hperm]
  nlinarith

theorem uniform_prob_loopPresentation_event
    (m d : ℕ) (w : ConfigurationLoopPresentation m (d + d)) :
    (configurationPermutationLaw m d).prob
        (conjugatePairsEvent
          (Configuration.standardConfiguration m d).partner w.pairs) =
      ((m * (d + d) - 1 : ℕ) : ℝ)⁻¹ := by
  rw [configurationPermutationLaw_prob_conjugatePairsEvent
    m d w.pairs w.endpoints_nodup]
  have hden : prescribedPairDenominator
      (m * (d + d)) w.pairs.length =
      m * (d + d) - 1 := by
    simp [ConfigurationLoopPresentation.pairs,
      prescribedPairDenominator]
  rw [hden]

theorem uniform_prob_parallelPresentation_event
    (m d : ℕ) (w : ConfigurationParallelPresentation m (d + d)) :
    (configurationPermutationLaw m d).prob
        (conjugatePairsEvent
          (Configuration.standardConfiguration m d).partner w.pairs) =
      (((m * (d + d) - 1) * (m * (d + d) - 3) : ℕ) : ℝ)⁻¹ := by
  rw [configurationPermutationLaw_prob_conjugatePairsEvent
    m d w.pairs w.endpoints_nodup]
  have hden : prescribedPairDenominator
      (m * (d + d)) w.pairs.length =
      (m * (d + d) - 1) * (m * (d + d) - 3) := by
    simp [ConfigurationParallelPresentation.pairs,
      prescribedPairDenominator, Finset.prod_range_succ]
  rw [hden]

theorem card_orderedDistinctSocketPair (D : ℕ) :
    Fintype.card (OrderedDistinctSocketPair D) = D * (D - 1) := by
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Fin D)).offDiag).card = _
  rw [Finset.offDiag_card]
  simp [Nat.mul_sub_left_distrib]

theorem card_configurationLoopPresentation (m D : ℕ) :
    Fintype.card (ConfigurationLoopPresentation m D) =
      m * (D * (D - 1)) := by
  change Fintype.card (Fin m × OrderedDistinctSocketPair D) = _
  rw [Fintype.card_prod, Fintype.card_fin,
    card_orderedDistinctSocketPair]

theorem card_configurationParallelPresentation (m D : ℕ) :
    Fintype.card (ConfigurationParallelPresentation m D) =
      (m * (m - 1)) * (D * (D - 1)) ^ 2 := by
  change Fintype.card
      (OrderedDistinctSocketPair m ×
        (OrderedDistinctSocketPair D × OrderedDistinctSocketPair D)) = _
  simp only [Fintype.card_prod, card_orderedDistinctSocketPair]
  rw [pow_two]

theorem expect_configurationLoopPresentationCountReal
    (m d : ℕ) :
    (configurationPermutationLaw m d).expect
        (fun sigma ↦ configurationLoopPresentationCountReal
          (randomConfiguration m d sigma)) =
      (Fintype.card (ConfigurationLoopPresentation m (d + d)) : ℝ) *
        ((m * (d + d) - 1 : ℕ) : ℝ)⁻¹ := by
  simp_rw [configurationLoopPresentationCountReal_randomConfiguration]
  rw [expect_finiteEventCountReal]
  simp_rw [uniform_prob_loopPresentation_event]
  simp

theorem expect_configurationParallelPresentationCountReal
    (m d : ℕ) :
    (configurationPermutationLaw m d).expect
        (fun sigma ↦ configurationParallelPresentationCountReal
          (randomConfiguration m d sigma)) =
      (Fintype.card (ConfigurationParallelPresentation m (d + d)) : ℝ) *
        (((m * (d + d) - 1) * (m * (d + d) - 3) : ℕ) : ℝ)⁻¹ := by
  simp_rw [configurationParallelPresentationCountReal_randomConfiguration]
  rw [expect_finiteEventCountReal]
  simp_rw [uniform_prob_parallelPresentation_event]
  simp

noncomputable def configurationProjectionDefectReal
    (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) : ℝ :=
  ((randomConfiguration m d sigma).projectionDefect : ℝ)

theorem configurationProjectionDefectReal_nonneg
    (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    0 ≤ configurationProjectionDefectReal m d sigma := by
  exact Nat.cast_nonneg _

/-- Exact first-moment envelope for the projection defect. -/
theorem expect_configurationProjectionDefectReal_le
    (m d : ℕ) :
    (configurationPermutationLaw m d).expect
        (configurationProjectionDefectReal m d) ≤
      (Fintype.card (ConfigurationLoopPresentation m (d + d)) : ℝ) *
          ((m * (d + d) - 1 : ℕ) : ℝ)⁻¹ +
        (Fintype.card
          (ConfigurationParallelPresentation m (d + d)) : ℝ) *
          (((m * (d + d) - 1) * (m * (d + d) - 3) : ℕ) : ℝ)⁻¹ := by
  let q := configurationPermutationLaw m d
  let L := fun sigma ↦ configurationLoopPresentationCountReal
    (randomConfiguration m d sigma)
  let P := fun sigma ↦ configurationParallelPresentationCountReal
    (randomConfiguration m d sigma)
  have hpoint : ∀ sigma, configurationProjectionDefectReal m d sigma ≤
      L sigma + P sigma := by
    intro sigma
    exact projectionDefect_cast_le_presentationCounts
      (randomConfiguration m d sigma)
  calc
    q.expect (configurationProjectionDefectReal m d) ≤
        q.expect (fun sigma ↦ L sigma + P sigma) := by
      unfold FiniteLaw.expect
      exact Finset.sum_le_sum fun sigma _hsigma ↦
        mul_le_mul_of_nonneg_left (hpoint sigma) (q.mass_nonneg sigma)
    _ = q.expect L + q.expect P := by
      unfold FiniteLaw.expect
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      ring
    _ = _ := by
      rw [show q.expect L =
          (Fintype.card (ConfigurationLoopPresentation m (d + d)) : ℝ) *
            ((m * (d + d) - 1 : ℕ) : ℝ)⁻¹ by
        exact expect_configurationLoopPresentationCountReal m d,
        show q.expect P =
          (Fintype.card
            (ConfigurationParallelPresentation m (d + d)) : ℝ) *
            (((m * (d + d) - 1) *
              (m * (d + d) - 3) : ℕ) : ℝ)⁻¹ by
          exact expect_configurationParallelPresentationCountReal m d]

/-- Finite Markov bound with the exact loop-plus-parallel first moment. -/
theorem configurationPermutationLaw_prob_projectionDefect_ge_le
    (m d : ℕ) {a : ℝ} (ha : 0 < a) :
    (configurationPermutationLaw m d).prob
        (FiniteLaw.event fun sigma ↦
          a ≤ configurationProjectionDefectReal m d sigma) ≤
      ((Fintype.card (ConfigurationLoopPresentation m (d + d)) : ℝ) *
          ((m * (d + d) - 1 : ℕ) : ℝ)⁻¹ +
        (Fintype.card
          (ConfigurationParallelPresentation m (d + d)) : ℝ) *
          (((m * (d + d) - 1) *
            (m * (d + d) - 3) : ℕ) : ℝ)⁻¹) / a := by
  exact ((configurationPermutationLaw m d).markov
    (configurationProjectionDefectReal m d)
    (configurationProjectionDefectReal_nonneg m d) ha).trans
      (div_le_div_of_nonneg_right
        (expect_configurationProjectionDefectReal_le m d) ha.le)

/-! ## A fixed-degree envelope -/

/-- The loop contribution to the first moment is uniformly bounded in the
number of vertices. -/
theorem configurationLoopFirstMoment_le
    (m D : ℕ) (hN : 2 ≤ m * D) :
    (Fintype.card (ConfigurationLoopPresentation m D) : ℝ) *
        ((m * D - 1 : ℕ) : ℝ)⁻¹ ≤
      2 * (D : ℝ) := by
  rw [card_configurationLoopPresentation]
  have hDsub : 1 ≤ D := by
    by_contra h
    have : D = 0 := by omega
    simp [this] at hN
  have hNsub : 1 ≤ m * D := by omega
  push_cast [Nat.cast_sub hDsub, Nat.cast_sub hNsub]
  rw [← div_eq_mul_inv]
  rw [div_le_iff₀ (by exact_mod_cast (show 0 < m * D - 1 by omega))]
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDsub
  have hNreal : (2 : ℝ) ≤ (m : ℝ) * D := by exact_mod_cast hN
  nlinarith

/-- The parallel-pair collision contribution to the first moment is also
uniformly bounded in the number of vertices. -/
theorem configurationParallelFirstMoment_le
    (m D : ℕ) (hN : 6 ≤ m * D) :
    (Fintype.card (ConfigurationParallelPresentation m D) : ℝ) *
        (((m * D - 1) * (m * D - 3) : ℕ) : ℝ)⁻¹ ≤
      4 * (D : ℝ) ^ 2 := by
  rw [card_configurationParallelPresentation]
  have hmSub : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    simp [this] at hN
  have hDsub : 1 ≤ D := by
    by_contra h
    have : D = 0 := by omega
    simp [this] at hN
  have hN1 : 1 ≤ m * D := by omega
  have hN3 : 3 ≤ m * D := by omega
  push_cast [Nat.cast_sub hmSub, Nat.cast_sub hDsub,
    Nat.cast_sub hN1, Nat.cast_sub hN3]
  rw [← div_eq_mul_inv]
  rw [div_le_iff₀]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmSub
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDsub
    have hNreal : (6 : ℝ) ≤ (m : ℝ) * D := by exact_mod_cast hN
    have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm1
    have hD0 : (0 : ℝ) ≤ D := zero_le_one.trans hD1
    have hnum :
        (m : ℝ) * (m - 1) * ((D : ℝ) * (D - 1)) ^ 2 ≤
          (m : ℝ) * m * ((D : ℝ) * D) ^ 2 := by
      gcongr <;> nlinarith
    have hden :
        ((m : ℝ) * D) ^ 2 ≤
          4 * (((m : ℝ) * D - 1) * ((m : ℝ) * D - 3)) := by
      have hprod : 0 ≤ ((m : ℝ) * D - 6) * (3 * ((m : ℝ) * D) + 2) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    calc
      (m : ℝ) * (m - 1) * ((D : ℝ) * (D - 1)) ^ 2 ≤
          (m : ℝ) * m * ((D : ℝ) * D) ^ 2 := hnum
      _ = (D : ℝ) ^ 2 * (((m : ℝ) * D) ^ 2) := by ring
      _ ≤ (D : ℝ) ^ 2 *
          (4 * (((m : ℝ) * D - 1) * ((m : ℝ) * D - 3))) := by
        exact mul_le_mul_of_nonneg_left hden (sq_nonneg _)
      _ = 4 * (D : ℝ) ^ 2 *
          (((m : ℝ) * D - 1) * ((m : ℝ) * D - 3)) := by ring
  · have hNreal : (6 : ℝ) ≤ (m : ℝ) * D := by exact_mod_cast hN
    exact mul_pos (by linarith) (by linarith)

/-- For fixed degree, the expected projection defect is bounded by a
constant independent of the number of vertices. -/
theorem expect_configurationProjectionDefectReal_le_degreeEnvelope
    (m d : ℕ) (hN : 6 ≤ m * (d + d)) :
    (configurationPermutationLaw m d).expect
        (configurationProjectionDefectReal m d) ≤
      2 * ((d + d : ℕ) : ℝ) + 4 * ((d + d : ℕ) : ℝ) ^ 2 := by
  exact (expect_configurationProjectionDefectReal_le m d).trans
    (add_le_add
      (configurationLoopFirstMoment_le m (d + d) (by omega))
      (configurationParallelFirstMoment_le m (d + d) hN))

/-! ## A canonical sublinear budget -/

/-- The canonical defect budget is the ceiling of `m^(3/4)`.  Any exponent
strictly between zero and one would work; `3/4` matches the short-cycle
threshold used elsewhere in the appendix. -/
noncomputable def configurationProjectionDefectBudget (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ (3 / 4 : ℝ))

/-- The corresponding budget along the paper's plant-size sequence. -/
noncomputable def appendixConfigurationProjectionDefectBudget
    (r : ℝ) (n : ℕ) : ℕ :=
  configurationProjectionDefectBudget (appendixPlantSize r n)

/-- Pointwise Markov bound for exceeding the canonical defect budget. -/
theorem configurationPermutationLaw_prob_projectionDefectBudget_lt_le
    (m d : ℕ) (hN : 6 ≤ m * (d + d)) :
    (configurationPermutationLaw m d).prob
        (FiniteLaw.event fun sigma ↦
          configurationProjectionDefectBudget m <
            (randomConfiguration m d sigma).projectionDefect) ≤
      (2 * ((d + d : ℕ) : ℝ) + 4 * ((d + d : ℕ) : ℝ) ^ 2) /
        (m : ℝ) ^ (3 / 4 : ℝ) := by
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    simp [this] at hN
  have hthreshold : 0 < (m : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  calc
    (configurationPermutationLaw m d).prob
        (FiniteLaw.event fun sigma ↦
          configurationProjectionDefectBudget m <
            (randomConfiguration m d sigma).projectionDefect) ≤
        (configurationPermutationLaw m d).prob
          (FiniteLaw.event fun sigma ↦
            (m : ℝ) ^ (3 / 4 : ℝ) ≤
              configurationProjectionDefectReal m d sigma) := by
      apply (configurationPermutationLaw m d).prob_mono
      intro sigma hsigma
      simp only [FiniteLaw.mem_event] at hsigma ⊢
      have hceil :
          (m : ℝ) ^ (3 / 4 : ℝ) ≤
            (configurationProjectionDefectBudget m : ℝ) := by
        exact Nat.le_ceil _
      have hbudget :
          (configurationProjectionDefectBudget m : ℝ) ≤
            configurationProjectionDefectReal m d sigma := by
        change (configurationProjectionDefectBudget m : ℝ) ≤
          ((randomConfiguration m d sigma).projectionDefect : ℝ)
        exact_mod_cast hsigma.le
      exact hceil.trans hbudget
    _ ≤ (configurationPermutationLaw m d).expect
          (configurationProjectionDefectReal m d) /
          (m : ℝ) ^ (3 / 4 : ℝ) :=
      (configurationPermutationLaw m d).markov
        (configurationProjectionDefectReal m d)
        (configurationProjectionDefectReal_nonneg m d) hthreshold
    _ ≤ (2 * ((d + d : ℕ) : ℝ) +
          4 * ((d + d : ℕ) : ℝ) ^ 2) /
          (m : ℝ) ^ (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_right
        (expect_configurationProjectionDefectReal_le_degreeEnvelope m d hN)
        hthreshold.le

/-- Along every size sequence tending to infinity, the probability of
exceeding the canonical defect budget vanishes. -/
theorem configurationProjectionDefectBudget_failure_vanishes
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (configurationPermutationLaw (m n) d).prob
        (FiniteLaw.event fun sigma ↦
          configurationProjectionDefectBudget (m n) <
            (randomConfiguration (m n) d sigma).projectionDefect) := by
  let C : ℝ :=
    2 * ((d + d : ℕ) : ℝ) + 4 * ((d + d : ℕ) : ℝ) ^ 2
  have hmReal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hthreequarters : (0 : ℝ) < 3 / 4 := by norm_num
  have hpower : Vanishes fun n ↦
      (m n : ℝ) ^ (-(3 / 4 : ℝ)) :=
    (tendsto_rpow_neg_atTop hthreequarters).comp hmReal
  have henvelope : Vanishes fun n ↦
      C / (m n : ℝ) ^ (3 / 4 : ℝ) := by
    have hscaled : Vanishes fun n ↦
        C * (m n : ℝ) ^ (-(3 / 4 : ℝ)) := hpower.const_mul C
    apply hscaled.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hmn
    change C * (m n : ℝ) ^ (-(3 / 4 : ℝ)) =
      C * ((m n : ℝ) ^ (3 / 4 : ℝ))⁻¹
    rw [Real.rpow_neg (by positivity)]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      (configurationPermutationLaw (m n) d).prob_nonneg _
  · filter_upwards [hm.eventually (eventually_ge_atTop 3)] with n hmn
    have hD : 2 ≤ d + d := by omega
    have hN : 6 ≤ m n * (d + d) := by
      calc
        6 = 3 * 2 := by norm_num
        _ ≤ m n * (d + d) := Nat.mul_le_mul hmn hD
    simpa only [C] using
      configurationPermutationLaw_prob_projectionDefectBudget_lt_le
        (m n) d hN
  · exact henvelope

/-- The canonical natural-valued budget itself is sublinear along every
size sequence tending to infinity. -/
theorem configurationProjectionDefectBudget_div_vanishes
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (configurationProjectionDefectBudget (m n) : ℝ) / (m n : ℝ) := by
  have hmReal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hpow : Vanishes fun n ↦
      (m n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    (tendsto_rpow_neg_atTop hquarter).comp hmReal
  have hinv : Vanishes fun n ↦ (1 : ℝ) / (m n : ℝ) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hmReal
  have htarget : Vanishes fun n ↦
      (m n : ℝ) ^ (-(1 / 4 : ℝ)) + 1 / (m n : ℝ) :=
    hpow.add hinv
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hmn
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast hmn
    have hceil :
        (configurationProjectionDefectBudget (m n) : ℝ) ≤
          (m n : ℝ) ^ (3 / 4 : ℝ) + 1 := by
      exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hmpos.le _)).le
    have hratio :
        (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) =
          (m n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      calc
        (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) =
            (m n : ℝ) ^ (3 / 4 : ℝ) / (m n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (m n : ℝ) ^ ((3 / 4 : ℝ) - 1) := by
          rw [← Real.rpow_sub hmpos]
        _ = (m n : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
    calc
      (configurationProjectionDefectBudget (m n) : ℝ) / (m n : ℝ) ≤
          ((m n : ℝ) ^ (3 / 4 : ℝ) + 1) / (m n : ℝ) := by
        exact div_le_div_of_nonneg_right hceil hmpos.le
      _ = (m n : ℝ) ^ (-(1 / 4 : ℝ)) + 1 / (m n : ℝ) := by
        rw [add_div, hratio]
  · exact htarget

/-- Appendix-facing specialization of the bad-defect probability estimate. -/
theorem appendixConfigurationBadDefect_probability_vanishes
    (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    Vanishes fun n ↦
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadDefectEvent d r
          (appendixConfigurationProjectionDefectBudget r) n) := by
  simpa only [configurationBadDefectEvent,
    appendixConfigurationProjectionDefectBudget] using
      configurationProjectionDefectBudget_failure_vanishes d hd
        (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr)

/-- Appendix-facing specialization of sublinearity of the defect budget. -/
theorem appendixConfigurationProjectionDefectBudget_div_vanishes
    {r : ℝ} (hr : 0 < r) :
    Vanishes fun n ↦
      (appendixConfigurationProjectionDefectBudget r n : ℝ) /
        (appendixPlantSize r n : ℝ) := by
  simpa only [appendixConfigurationProjectionDefectBudget] using
    configurationProjectionDefectBudget_div_vanishes
      (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr)

end

end LowDegree
