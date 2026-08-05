import LowDegree.Combinatorics.NoisedClassWeights
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Finite isomorphism classes of ambient graph supports

Nonempty Fourier supports in the complete graph on `Fin n` are partitioned
by the action of ambient vertex permutations.  Every orbit is represented by
a canonical finite graph shape with no isolated vertices.  Its orbit fiber is
equivalent to the type of unlabelled concrete copies of that shape in the
ambient complete graph.  This gives the duplicate-free finite regrouping used
in paper Equations (3.5) and (3.6).
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace FiniteGraphShape

/-- The ambient edge-coordinate equivalence acts by the underlying vertex
permutation on unordered pairs. -/
@[simp]
theorem coe_ambientEdgeEquivOfPerm {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (e : AmbientEdge n) :
    ((ambientEdgeEquivOfPerm τ e : AmbientEdge n) : Sym2 (Fin n)) =
      Sym2.map τ (e : Sym2 (Fin n)) := rfl

@[simp]
theorem permuteAmbientSupport_one {n : ℕ}
    (S : Finset (AmbientEdge n)) :
    permuteAmbientSupport (1 : Equiv.Perm (Fin n)) S = S := by
  have heq : ambientEdgeEquivOfPerm (1 : Equiv.Perm (Fin n)) =
      Equiv.refl (AmbientEdge n) := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change Sym2.map (1 : Equiv.Perm (Fin n)) e.1 = e.1
    simp
  rw [permuteAmbientSupport, heq]
  simp

theorem permuteAmbientSupport_mul {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (S : Finset (AmbientEdge n)) :
    permuteAmbientSupport (σ * τ) S =
      permuteAmbientSupport σ (permuteAmbientSupport τ S) := by
  have heq : ambientEdgeEquivOfPerm (σ * τ) =
      (ambientEdgeEquivOfPerm τ).trans (ambientEdgeEquivOfPerm σ) := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change Sym2.map (fun x ↦ σ (τ x)) e.1 =
      Sym2.map σ (Sym2.map τ e.1)
    exact (Sym2.map_map e.1).symm
  rw [permuteAmbientSupport, heq, permuteAmbientSupport,
    permuteAmbientSupport, Finset.map_map]
  rfl

end FiniteGraphShape

/-- A nonempty finite Fourier support in the ambient complete graph. -/
abbrev NonemptyAmbientSupport (n : ℕ) :=
  {S : Finset (AmbientEdge n) // S.Nonempty}

noncomputable instance nonemptyAmbientSupportMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (NonemptyAmbientSupport n) where
  smul τ S :=
    ⟨FiniteGraphShape.permuteAmbientSupport τ S.1,
      S.2.map⟩
  one_smul S := by
    apply Subtype.ext
    exact FiniteGraphShape.permuteAmbientSupport_one S.1
  mul_smul σ τ S := by
    apply Subtype.ext
    exact FiniteGraphShape.permuteAmbientSupport_mul σ τ S.1

/-- The finite quotient indexing nonempty ambient supports up to vertex
relabeling. -/
abbrev AmbientSupportClass (n : ℕ) :=
  MulAction.orbitRel.Quotient
    (Equiv.Perm (Fin n)) (NonemptyAmbientSupport n)

noncomputable instance ambientSupportClassFintype (n : ℕ) :
    Fintype (AmbientSupportClass n) := Fintype.ofFinite _

/-- Send a nonempty support to its unique vertex-permutation orbit. -/
def ambientSupportClass {n : ℕ} (S : NonemptyAmbientSupport n) :
    AmbientSupportClass n :=
  Quotient.mk'' S

namespace AmbientSupportClass

/-- A chosen support representing the orbit. -/
noncomputable def representative {n : ℕ} (C : AmbientSupportClass n) :
    NonemptyAmbientSupport n :=
  Quotient.out C

@[simp]
theorem representative_class {n : ℕ} (C : AmbientSupportClass n) :
    ambientSupportClass C.representative = C :=
  Quotient.out_eq' C

end AmbientSupportClass

/-! ## The graph shape canonically attached to a support -/

/-- Forget the proof that an edge belongs to the complete graph and regard a
finite ambient support as a set of unordered vertex pairs. -/
def ambientSupportEdgeSet {n : ℕ} (S : Finset (AmbientEdge n)) :
    Set (Sym2 (Fin n)) :=
  {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet,
    (⟨e, h⟩ : AmbientEdge n) ∈ S}

/-- The spanning simple graph with precisely the edges in `S`. -/
def ambientSupportGraph {n : ℕ} (S : Finset (AmbientEdge n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (ambientSupportEdgeSet S)

@[simp]
theorem mem_ambientSupportGraph_edgeSet_iff {n : ℕ}
    (S : Finset (AmbientEdge n)) (e : AmbientEdge n) :
    (e : Sym2 (Fin n)) ∈ (ambientSupportGraph S).edgeSet ↔ e ∈ S := by
  simp only [ambientSupportGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_diff, ambientSupportEdgeSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h, he⟩, _⟩
    simpa using he
  · intro he
    exact ⟨⟨e.property, he⟩,
      (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet e.property⟩

/-- The edge-support graph as a subgraph of the ambient complete graph, with
its vertex set restricted to incident vertices. -/
def ambientSupportSubgraph {n : ℕ} (S : Finset (AmbientEdge n)) :
    (⊤ : SimpleGraph (Fin n)).Subgraph where
  verts := (ambientSupportGraph S).support
  Adj := (ambientSupportGraph S).Adj
  adj_sub := fun {_ _} h ↦ SimpleGraph.top_adj _ _ |>.2 h.ne
  edge_vert := by
    intro u v huv
    rw [SimpleGraph.mem_support]
    exact ⟨v, huv⟩
  symm := (ambientSupportGraph S).symm

/-- The canonical concrete copy attached to an ambient support. -/
noncomputable def supportConcreteCopy {n : ℕ}
    (S : Finset (AmbientEdge n)) :
    (FiniteGraphShape.supportShape (ambientSupportGraph S)).ConcreteCopy
      (⊤ : SimpleGraph (Fin n)) :=
  ⟨ambientSupportSubgraph S, ⟨by
    change (ambientSupportGraph S).induce
        (ambientSupportGraph S).support ≃g
      (ambientSupportSubgraph S).coe
    exact SimpleGraph.Iso.refl⟩⟩

@[simp]
theorem concreteCopyEdges_supportConcreteCopy {n : ℕ}
    (S : Finset (AmbientEdge n)) :
    (FiniteGraphShape.supportShape (ambientSupportGraph S)).concreteCopyEdges
        (supportConcreteCopy S) = S := by
  ext e
  rw [FiniteGraphShape.mem_concreteCopyEdges]
  change (e : Sym2 (Fin n)) ∈ (ambientSupportGraph S).edgeSet ↔ e ∈ S
  exact mem_ambientSupportGraph_edgeSet_iff S e

/-- Mapping a concrete copy by an ambient vertex permutation maps its finite
edge support by the corresponding edge permutation. -/
theorem FiniteGraphShape.concreteCopyEdges_mapConcreteCopy {n : ℕ}
    (F : FiniteGraphShape) (τ : Equiv.Perm (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    F.concreteCopyEdges
        (F.mapConcreteCopy (FiniteGraphShape.completeGraphIsoOfPerm τ) copy) =
      FiniteGraphShape.permuteAmbientSupport τ
        (F.concreteCopyEdges copy) := by
  ext e
  rw [FiniteGraphShape.mem_concreteCopyEdges,
    F.mapConcreteCopy_subgraph,
    SimpleGraph.Subgraph.edgeSet_map,
    FiniteGraphShape.permuteAmbientSupport, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hea⟩
    have hatop : a ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
      copy.1.edgeSet_subset ha
    let ambient : AmbientEdge n := ⟨a, hatop⟩
    refine ⟨ambient, ?_, ?_⟩
    · rw [F.mem_concreteCopyEdges]
      exact ha
    · apply Subtype.ext
      exact hea
  · rintro ⟨a, ha, hea⟩
    rw [F.mem_concreteCopyEdges] at ha
    refine ⟨(a : Sym2 (Fin n)), ha, ?_⟩
    exact congrArg Subtype.val hea

/-- The no-isolated-vertices graph shape chosen for an ambient support
orbit. -/
noncomputable def AmbientSupportClass.shape {n : ℕ}
    (C : AmbientSupportClass n) : FiniteGraphShape :=
  FiniteGraphShape.supportShape
    (ambientSupportGraph C.representative.1)

/-- The representative support, viewed as a concrete copy of the class
shape. -/
noncomputable def AmbientSupportClass.representativeCopy {n : ℕ}
    (C : AmbientSupportClass n) :
    C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
  supportConcreteCopy C.representative.1

@[simp]
theorem AmbientSupportClass.concreteCopyEdges_representativeCopy {n : ℕ}
    (C : AmbientSupportClass n) :
    C.shape.concreteCopyEdges C.representativeCopy = C.representative.1 :=
  concreteCopyEdges_supportConcreteCopy C.representative.1

/-! ## Orbit fibers are exactly concrete-copy supports -/

theorem ambientSupportClass_eq_iff {n : ℕ}
    (S T : NonemptyAmbientSupport n) :
    ambientSupportClass S = ambientSupportClass T ↔
      ∃ τ : Equiv.Perm (Fin n), τ • T = S := by
  change Quotient.mk'' S = Quotient.mk'' T ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]

/-- A nonempty support lies in an orbit fiber exactly when it is one of the
ambient supports carrying the representative graph shape. -/
theorem AmbientSupportClass.mem_ambientCopySupports_iff {n : ℕ}
    (C : AmbientSupportClass n) (S : NonemptyAmbientSupport n) :
    S.1 ∈ C.shape.ambientCopySupports ↔ ambientSupportClass S = C := by
  constructor
  · intro hS
    rw [FiniteGraphShape.ambientCopySupports, Finset.mem_image] at hS
    rcases hS with ⟨copy, _hcopyUniv, hcopy⟩
    rw [← C.representative_class]
    apply (ambientSupportClass_eq_iff S C.representative).2
    let τ := C.shape.concreteCopyTransportPerm C.representativeCopy copy
    refine ⟨τ, ?_⟩
    apply Subtype.ext
    change FiniteGraphShape.permuteAmbientSupport τ C.representative.1 = S.1
    calc
      FiniteGraphShape.permuteAmbientSupport τ C.representative.1 =
          FiniteGraphShape.permuteAmbientSupport τ
            (C.shape.concreteCopyEdges C.representativeCopy) := by
        rw [C.concreteCopyEdges_representativeCopy]
      _ = C.shape.concreteCopyEdges copy :=
        C.shape.permuteAmbientSupport_concreteCopyTransportPerm
          C.representativeCopy copy
      _ = S.1 := hcopy
  · intro hclass
    have hrepresentative :
        ambientSupportClass S = ambientSupportClass C.representative :=
      hclass.trans C.representative_class.symm
    rcases (ambientSupportClass_eq_iff S C.representative).1
      hrepresentative with ⟨τ, hτ⟩
    let copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
      C.shape.mapConcreteCopy
        (FiniteGraphShape.completeGraphIsoOfPerm τ) C.representativeCopy
    rw [FiniteGraphShape.ambientCopySupports, Finset.mem_image]
    refine ⟨copy, Finset.mem_univ _, ?_⟩
    calc
      C.shape.concreteCopyEdges copy =
          FiniteGraphShape.permuteAmbientSupport τ
            (C.shape.concreteCopyEdges C.representativeCopy) :=
        C.shape.concreteCopyEdges_mapConcreteCopy τ C.representativeCopy
      _ = FiniteGraphShape.permuteAmbientSupport τ C.representative.1 := by
        rw [C.concreteCopyEdges_representativeCopy]
      _ = S.1 := congrArg Subtype.val hτ

@[simp]
theorem AmbientSupportClass.shape_edgeCount_eq_representative_card {n : ℕ}
    (C : AmbientSupportClass n) :
    C.shape.edgeCount = C.representative.1.card := by
  calc
    C.shape.edgeCount =
        (C.shape.concreteCopyEdges C.representativeCopy).card :=
      (C.shape.card_concreteCopyEdges C.representativeCopy).symm
    _ = C.representative.1.card := by
      rw [C.concreteCopyEdges_representativeCopy]

theorem AmbientSupportClass.card_eq_shape_edgeCount_of_class {n : ℕ}
    (C : AmbientSupportClass n) (S : NonemptyAmbientSupport n)
    (hS : ambientSupportClass S = C) :
    S.1.card = C.shape.edgeCount := by
  have hmem := (C.mem_ambientCopySupports_iff S).2 hS
  rw [FiniteGraphShape.ambientCopySupports, Finset.mem_image] at hmem
  rcases hmem with ⟨copy, _hcopyUniv, hcopy⟩
  rw [← hcopy, C.shape.card_concreteCopyEdges]

/-- Map a concrete copy to the corresponding point of the orbit fiber. -/
noncomputable def AmbientSupportClass.concreteCopyToFiber {n : ℕ}
    (C : AmbientSupportClass n)
    (copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    {S : NonemptyAmbientSupport n // ambientSupportClass S = C} := by
  let edges := C.shape.concreteCopyEdges copy
  have hedgesNonempty : edges.Nonempty := by
    apply Finset.card_pos.mp
    rw [C.shape.card_concreteCopyEdges copy,
      C.shape_edgeCount_eq_representative_card]
    exact C.representative.2.card_pos
  let S : NonemptyAmbientSupport n := ⟨edges, hedgesNonempty⟩
  refine ⟨S, (C.mem_ambientCopySupports_iff S).1 ?_⟩
  rw [FiniteGraphShape.ambientCopySupports, Finset.mem_image]
  exact ⟨copy, Finset.mem_univ _, rfl⟩

/-- The quotient fiber over a class is equivalent to the type of unlabelled
concrete copies of its chosen graph shape. -/
noncomputable def AmbientSupportClass.fiberEquivConcreteCopies {n : ℕ}
    (C : AmbientSupportClass n) :
    C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)) ≃
      {S : NonemptyAmbientSupport n // ambientSupportClass S = C} :=
  Equiv.ofBijective C.concreteCopyToFiber ⟨by
    intro source target h
    apply C.shape.concreteCopyEdges_injective
    exact congrArg (fun S ↦ S.1.1) h
  , by
    rintro ⟨S, hS⟩
    have hmem := (C.mem_ambientCopySupports_iff S).2 hS
    rw [FiniteGraphShape.ambientCopySupports, Finset.mem_image] at hmem
    rcases hmem with ⟨copy, _hcopyUniv, hcopy⟩
    refine ⟨copy, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hcopy⟩

/-! ## Duplicate-free regrouping of finite support sums -/

/-- Regroup a sum over all nonempty ambient supports by the finite orbit
quotient. -/
theorem sum_nonempty_ambientSupports_eq_sum_classFibers
    {n : ℕ} (weight : Finset (AmbientEdge n) → ℝ) :
    (∑ S : Finset (AmbientEdge n) with S.Nonempty, weight S) =
      ∑ C : AmbientSupportClass n,
        ∑ S : NonemptyAmbientSupport n with ambientSupportClass S = C,
          weight S.1 := by
  calc
    (∑ S : Finset (AmbientEdge n) with S.Nonempty, weight S) =
        ∑ S : NonemptyAmbientSupport n, weight S.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (Finset (AmbientEdge n))).filter
          Finset.Nonempty)
        (by intro S; simp) weight
    _ = ∑ C : AmbientSupportClass n,
        ∑ S : NonemptyAmbientSupport n with ambientSupportClass S = C,
          weight S.1 := by
      simpa using (Finset.sum_fiberwise
        (Finset.univ : Finset (NonemptyAmbientSupport n))
        ambientSupportClass (fun S ↦ weight S.1)).symm

/-- One quotient fiber sums exactly over the concrete copies of its chosen
shape. -/
theorem AmbientSupportClass.sum_fiber_eq_sum_concreteCopies {n : ℕ}
    (C : AmbientSupportClass n) (weight : Finset (AmbientEdge n) → ℝ) :
    (∑ S : NonemptyAmbientSupport n with ambientSupportClass S = C,
        weight S.1) =
      ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        weight (C.shape.concreteCopyEdges copy) := by
  calc
    (∑ S : NonemptyAmbientSupport n with ambientSupportClass S = C,
        weight S.1) =
        ∑ S : {S : NonemptyAmbientSupport n // ambientSupportClass S = C},
          weight S.1.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (NonemptyAmbientSupport n)).filter
          fun S ↦ ambientSupportClass S = C)
        (by intro S; simp) (fun S ↦ weight S.1)
    _ = ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        weight (C.shape.concreteCopyEdges copy) := by
      symm
      apply Fintype.sum_equiv C.fiberEquivConcreteCopies
      intro copy
      rfl

/-- Full regrouping of an arbitrary nonempty-support weight into exactly one
sum for each graph-shape class. -/
theorem sum_nonempty_ambientSupports_eq_sum_concreteCopyClasses
    {n : ℕ} (weight : Finset (AmbientEdge n) → ℝ) :
    (∑ S : Finset (AmbientEdge n) with S.Nonempty, weight S) =
      ∑ C : AmbientSupportClass n,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          weight (C.shape.concreteCopyEdges copy) := by
  rw [sum_nonempty_ambientSupports_eq_sum_classFibers]
  apply Finset.sum_congr rfl
  intro C _hC
  exact C.sum_fiber_eq_sum_concreteCopies weight

/-- Degree-restricted version of the full orbit regrouping. -/
theorem sum_nonempty_ambientSupports_degree_eq_sum_concreteCopyClasses
    {n D : ℕ} (weight : Finset (AmbientEdge n) → ℝ) :
    (∑ S : Finset (AmbientEdge n) with S.card ≤ D ∧ S.Nonempty,
        weight S) =
      ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          weight (C.shape.concreteCopyEdges copy) := by
  let restrictedWeight : Finset (AmbientEdge n) → ℝ := fun S ↦
    if S.card ≤ D then weight S else 0
  calc
    (∑ S : Finset (AmbientEdge n) with S.card ≤ D ∧ S.Nonempty,
        weight S) =
        ∑ S : Finset (AmbientEdge n) with S.Nonempty,
          restrictedWeight S := by
      dsimp [restrictedWeight]
      simp only [← Finset.sum_filter]
      congr 1
      ext S
      simp [and_comm]
    _ = ∑ C : AmbientSupportClass n,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          restrictedWeight (C.shape.concreteCopyEdges copy) :=
      sum_nonempty_ambientSupports_eq_sum_concreteCopyClasses restrictedWeight
    _ = ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          weight (C.shape.concreteCopyEdges copy) := by
      dsimp [restrictedWeight]
      simp_rw [FiniteGraphShape.card_concreteCopyEdges]
      calc
        (∑ C : AmbientSupportClass n,
            ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
              if C.shape.edgeCount ≤ D then
                weight (C.shape.concreteCopyEdges copy) else 0) =
            ∑ C : AmbientSupportClass n,
              if C.shape.edgeCount ≤ D then
                ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
                  weight (C.shape.concreteCopyEdges copy)
              else 0 := by
          apply Finset.sum_congr rfl
          intro C _hC
          by_cases hdegree : C.shape.edgeCount ≤ D
          · simp only [if_pos hdegree]
          · simp only [if_neg hdegree, Finset.sum_const_zero]
        _ = _ := by rw [Finset.sum_filter]

/-! ## Full Equations (3.5) and (3.6) -/

/-- **Equation (3.5), fully regrouped by graph isomorphism class.**

This is the exact-parameter form.  The quotient index ensures that no two
summands represent isomorphic nonempty supports. -/
theorem plantedLowDegreeNormSq_sub_one_eq_sum_supportClasses
    {n : ℕ} (θ : BernoulliParameter)
    (plant : SimpleGraph (Fin n)) (D : ℕ) :
    plantedLowDegreeNormSq θ plant D - 1 =
      ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        ((1 - θ.p) / θ.p) ^ C.shape.edgeCount *
          ((C.shape.nonInducedCopyCount plant : ℝ) ^ 2 *
            (Fintype.card C.shape.Automorphism : ℝ)) /
              fallingFactorial n C.shape.vertexCount := by
  rw [plantedLowDegreeNormSq_sub_one_eq_sum_nonempty]
  calc
    (∑ S : Finset (AmbientEdge n) with S.card ≤ D ∧ S.Nonempty,
        ((((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2)) =
        ∑ S : Finset (AmbientEdge n) with S.card ≤ D ∧ S.Nonempty,
          (fourierCoeff θ (plantedLikelihood θ plant) S) ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [fourierCoeff_plantedLikelihood]
    _ = ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff θ (plantedLikelihood θ plant)
            (C.shape.concreteCopyEdges copy)) ^ 2 :=
      sum_nonempty_ambientSupports_degree_eq_sum_concreteCopyClasses
        (fun S ↦ (fourierCoeff θ (plantedLikelihood θ plant) S) ^ 2)
    _ = ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        ((1 - θ.p) / θ.p) ^ C.shape.edgeCount *
          ((C.shape.nonInducedCopyCount plant : ℝ) ^ 2 *
            (Fintype.card C.shape.Automorphism : ℝ)) /
              fallingFactorial n C.shape.vertexCount := by
      apply Finset.sum_congr rfl
      intro C _hC
      exact C.shape.sum_fourierCoeff_sq_over_concreteCopies
        θ plant C.representativeCopy

/-- Sparse-parameter form of full Equation (3.5), as a duplicate-free sum
of the paper's exact `alphaWeight` terms. -/
theorem plantedLowDegreeNormSq_sub_one_eq_sum_alphaWeights
    {n : ℕ} (θ : BernoulliParameter)
    (plant : SimpleGraph (Fin n)) (D : ℕ)
    (c : ℝ) (hp : θ.p = c / (n : ℝ)) :
    plantedLowDegreeNormSq θ plant D - 1 =
      ∑ C : AmbientSupportClass n with C.shape.edgeCount ≤ D,
        alphaWeight c n C.shape.edgeCount C.shape.vertexCount
          (C.shape.nonInducedCopyCount plant)
          (Fintype.card C.shape.Automorphism) := by
  rw [plantedLowDegreeNormSq_sub_one_eq_sum_supportClasses]
  apply Finset.sum_congr rfl
  intro C _hC
  rw [alphaWeight, hp]

/-- **Equation (3.6), fully regrouped by graph isomorphism class.**

Every class contribution is its exact Equation (3.5) weight multiplied by
the common squared noise eigenvalue `(1-ε)^(2e(F))`. -/
theorem plantedNoisedNormSq_sub_one_eq_sum_supportClasses
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    plantedNoisedNormSq θ ε plant - 1 =
      ∑ C : AmbientSupportClass n,
        (1 - (ε : ℝ)) ^ (2 * C.shape.edgeCount) *
          (((1 - θ.p) / θ.p) ^ C.shape.edgeCount *
            ((C.shape.nonInducedCopyCount plant : ℝ) ^ 2 *
              (Fintype.card C.shape.Automorphism : ℝ)) /
                fallingFactorial n C.shape.vertexCount) := by
  rw [plantedNoisedNormSq_sub_one_eq_sum_nonempty]
  calc
    (∑ S : Finset (AmbientEdge n) with S.Nonempty,
        (((1 - (ε : ℝ)) ^ S.card *
          ((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2)) =
        ∑ S : Finset (AmbientEdge n) with S.Nonempty,
          (fourierCoeff θ (noisedLikelihood θ ε plant) S) ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [fourierCoeff_noisedLikelihood]
    _ = ∑ C : AmbientSupportClass n,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (fourierCoeff θ (noisedLikelihood θ ε plant)
            (C.shape.concreteCopyEdges copy)) ^ 2 :=
      sum_nonempty_ambientSupports_eq_sum_concreteCopyClasses
        (fun S ↦ (fourierCoeff θ (noisedLikelihood θ ε plant) S) ^ 2)
    _ = ∑ C : AmbientSupportClass n,
        (1 - (ε : ℝ)) ^ (2 * C.shape.edgeCount) *
          (((1 - θ.p) / θ.p) ^ C.shape.edgeCount *
            ((C.shape.nonInducedCopyCount plant : ℝ) ^ 2 *
              (Fintype.card C.shape.Automorphism : ℝ)) /
                fallingFactorial n C.shape.vertexCount) := by
      apply Finset.sum_congr rfl
      intro C _hC
      exact C.shape.sum_fourierCoeff_sq_noised_over_concreteCopies
        θ ε plant C.representativeCopy

/-- Sparse-parameter form of full Equation (3.6). -/
theorem plantedNoisedNormSq_sub_one_eq_sum_noisedAlphaWeights
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (c : ℝ) (hp : θ.p = c / (n : ℝ)) :
    plantedNoisedNormSq θ ε plant - 1 =
      ∑ C : AmbientSupportClass n,
        (1 - (ε : ℝ)) ^ (2 * C.shape.edgeCount) *
          alphaWeight c n C.shape.edgeCount C.shape.vertexCount
            (C.shape.nonInducedCopyCount plant)
            (Fintype.card C.shape.Automorphism) := by
  rw [plantedNoisedNormSq_sub_one_eq_sum_supportClasses]
  apply Finset.sum_congr rfl
  intro C _hC
  rw [alphaWeight, hp]

end

end LowDegree
