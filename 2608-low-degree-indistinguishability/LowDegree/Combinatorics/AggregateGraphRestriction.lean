import LowDegree.Combinatorics.GraphShapeClasses
import LowDegree.Combinatorics.ClusterInterfaceCharging

/-!
# Aggregate restriction across graph-shape classes

The pointwise restriction map of Lemma 4.2 is not enough after summing over
all parent shapes: two different parents must not collide in the product of
piece-triple spaces.  This module tags every restricted piece by its ambient
support orbit and proves that the resulting aggregate map is injective.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace FiniteGraphShape

universe u w

/-- Concrete copies of possibly different support shapes in a complete graph
are equal as ambient subgraphs when their finite edge supports agree. -/
theorem concreteCopy_subgraph_eq_of_edges_eq {n : ℕ}
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}}
    (source : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (target : H.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hedge : F.concreteCopyEdges source = H.concreteCopyEdges target) :
    source.1 = target.1 := by
  apply SimpleGraph.Subgraph.ext
  · rw [← F.concreteCopy_support_eq_verts source,
      ← H.concreteCopy_support_eq_verts target]
    ext v
    simp only [SimpleGraph.Subgraph.mem_support]
    constructor
    · rintro ⟨w, hvw⟩
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset source.1 hvw⟩
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heTarget : e ∈ H.concreteCopyEdges target := by
        rw [← hedge]
        exact heSource
      rw [H.mem_concreteCopyEdges] at heTarget
      exact ⟨w, heTarget⟩
    · rintro ⟨w, hvw⟩
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset target.1 hvw⟩
      have heTarget : e ∈ H.concreteCopyEdges target := by
        rw [H.mem_concreteCopyEdges]
        exact hvw
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [hedge]
        exact heTarget
      rw [F.mem_concreteCopyEdges] at heSource
      exact ⟨w, heSource⟩
  · funext v w
    apply propext
    constructor
    · intro hvw
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset source.1 hvw⟩
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heTarget : e ∈ H.concreteCopyEdges target := by
        rw [← hedge]
        exact heSource
      rwa [H.mem_concreteCopyEdges] at heTarget
    · intro hvw
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset target.1 hvw⟩
      have heTarget : e ∈ H.concreteCopyEdges target := by
        rw [H.mem_concreteCopyEdges]
        exact hvw
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [hedge]
        exact heTarget
      rwa [F.mem_concreteCopyEdges] at heSource

/-- Reinterpret a concrete copy after changing its abstract shape by a graph
isomorphism.  Its ambient subgraph is unchanged. -/
noncomputable def reindexConcreteCopy {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) (copy : F.ConcreteCopy G) : H.ConcreteCopy G :=
  ⟨copy.1, ⟨(chosenIso copy).comp e.symm⟩⟩

@[simp]
theorem reindexConcreteCopy_val {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) (copy : F.ConcreteCopy G) :
    (reindexConcreteCopy e copy).1 = copy.1 := rfl

/-- Reindex every coordinate of an isomorphism triple along an abstract shape
isomorphism. -/
noncomputable def reindexIsomorphismTriple {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) (triple : F.IsomorphismTripleIn G) :
    H.IsomorphismTripleIn G where
  source := reindexConcreteCopy e triple.source
  target := reindexConcreteCopy e triple.target
  hom := triple.hom

@[simp]
theorem reindexIsomorphismTriple_source_val {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) (triple : F.IsomorphismTripleIn G) :
    (reindexIsomorphismTriple e triple).source.1 = triple.source.1 := rfl

@[simp]
theorem reindexIsomorphismTriple_target_val {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) (triple : F.IsomorphismTripleIn G) :
    (reindexIsomorphismTriple e triple).target.1 = triple.target.1 := rfl

/-- Reindexing triples is a bijection. -/
noncomputable def reindexIsomorphismTripleEquiv {V : Type*} [Fintype V]
    {F : FiniteGraphShape.{u}} {H : FiniteGraphShape.{w}} {G : SimpleGraph V}
    (e : F.graph ≃g H.graph) :
    F.IsomorphismTripleIn G ≃ H.IsomorphismTripleIn G where
  toFun := reindexIsomorphismTriple e
  invFun := reindexIsomorphismTriple e.symm
  left_inv := by
    rintro ⟨source, target, hom⟩
    rfl
  right_inv := by
    rintro ⟨source, target, hom⟩
    rfl

/-- The ambient orbit class represented by a nonempty concrete copy. -/
noncomputable def concreteCopyClass {n : ℕ} (F : FiniteGraphShape.{u})
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hpos : 0 < F.edgeCount) : AmbientSupportClass n :=
  ambientSupportClass ⟨F.concreteCopyEdges copy, by
    apply Finset.card_pos.mp
    simpa [F.card_concreteCopyEdges copy] using hpos⟩

/-- The canonical copy of the chosen representative shape above the same
ambient support as `copy`. -/
noncomputable def classCopyOfConcreteCopy {n : ℕ}
    (F : FiniteGraphShape.{u})
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hpos : 0 < F.edgeCount) :
    (F.concreteCopyClass copy hpos).shape.ConcreteCopy
      (⊤ : SimpleGraph (Fin n)) :=
  ((F.concreteCopyClass copy hpos).fiberEquivConcreteCopies).symm
    ⟨⟨F.concreteCopyEdges copy, by
      apply Finset.card_pos.mp
      simpa [F.card_concreteCopyEdges copy] using hpos⟩, rfl⟩

theorem concreteCopyEdges_classCopyOfConcreteCopy {n : ℕ}
    (F : FiniteGraphShape.{u})
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hpos : 0 < F.edgeCount) :
    (F.concreteCopyClass copy hpos).shape.concreteCopyEdges
        (F.classCopyOfConcreteCopy copy hpos) =
      F.concreteCopyEdges copy := by
  let C := F.concreteCopyClass copy hpos
  let S : NonemptyAmbientSupport n := ⟨F.concreteCopyEdges copy, by
    apply Finset.card_pos.mp
    simpa [F.card_concreteCopyEdges copy] using hpos⟩
  let tagged : {T : NonemptyAmbientSupport n // ambientSupportClass T = C} :=
    ⟨S, rfl⟩
  have h := C.fiberEquivConcreteCopies.apply_symm_apply tagged
  have hval := congrArg (fun z ↦ z.1.1) h
  change C.shape.concreteCopyEdges
      (C.fiberEquivConcreteCopies.symm tagged) = S.1 at hval
  change C.shape.concreteCopyEdges
      (C.fiberEquivConcreteCopies.symm tagged) = S.1
  exact hval

/-- The original abstract shape is isomorphic to the canonical shape of the
ambient orbit class represented by any of its nonempty concrete copies. -/
noncomputable def concreteCopyClassShapeIso {n : ℕ}
    (F : FiniteGraphShape.{u})
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hpos : 0 < F.edgeCount) :
    F.graph ≃g (F.concreteCopyClass copy hpos).shape.graph := by
  let classCopy := F.classCopyOfConcreteCopy copy hpos
  have hsub : copy.1 = classCopy.1 :=
    concreteCopy_subgraph_eq_of_edges_eq
      (F := F) (H := (F.concreteCopyClass copy hpos).shape)
      copy classCopy <|
        (F.concreteCopyEdges_classCopyOfConcreteCopy copy hpos).symm
  let middle : copy.1.coe ≃g classCopy.1.coe := by
    rw [hsub]
  exact (chosenIso classCopy).symm.comp (middle.comp (chosenIso copy))

@[simp]
theorem concreteCopyClass_shape_edgeCount {n : ℕ}
    (F : FiniteGraphShape.{u})
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (hpos : 0 < F.edgeCount) :
    (F.concreteCopyClass copy hpos).shape.edgeCount = F.edgeCount := by
  let S : NonemptyAmbientSupport n := ⟨F.concreteCopyEdges copy, by
    apply Finset.card_pos.mp
    simpa [F.card_concreteCopyEdges copy] using hpos⟩
  have hcard := (F.concreteCopyClass copy hpos).card_eq_shape_edgeCount_of_class
    S (by rfl)
  calc
    (F.concreteCopyClass copy hpos).shape.edgeCount = S.1.card := hcard.symm
    _ = F.edgeCount := by
      simp [S, F.card_concreteCopyEdges copy]

end FiniteGraphShape

namespace AggregateGraphRestriction

open TreeDecomposition

variable {n m : ℕ}

/-- The contribution of one isomorphism triple to the leading `β` weight. -/
noncomputable def tripleBetaScale (c : ℝ) (n : ℕ)
    (F : FiniteGraphShape) : ℝ :=
  betaFromTriple (n : ℝ) c F.edgeCount F.vertexCount 1

theorem tripleBetaScale_nonneg {c : ℝ} (hc : 0 < c) (n : ℕ)
    (F : FiniteGraphShape) : 0 ≤ tripleBetaScale c n F := by
  unfold tripleBetaScale betaFromTriple
  positivity

/-- Summing the per-triple scale over all concrete triples gives exactly the
graph-specialized leading weight. -/
theorem sum_tripleBetaScale_eq_graphBetaWeight
    (c : ℝ) (n : ℕ) (F : FiniteGraphShape)
    (G : SimpleGraph (Fin n)) :
    (∑ _triple : F.IsomorphismTripleIn G, tripleBetaScale c n F) =
      F.graphBetaWeight c n G := by
  rw [F.graphBetaWeight_eq_betaFromTriple]
  simp only [tripleBetaScale, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  unfold betaFromTriple
  ring

/-- Isomorphic abstract shapes have the same vertex count. -/
theorem vertexCount_eq_of_iso {F H : FiniteGraphShape}
    (e : F.graph ≃g H.graph) : F.vertexCount = H.vertexCount := by
  exact Fintype.card_congr e.toEquiv

/-- Isomorphic abstract shapes have the same edge count. -/
theorem edgeCount_eq_of_iso {F H : FiniteGraphShape}
    (e : F.graph ≃g H.graph) : F.edgeCount = H.edgeCount := by
  rw [F.edgeCount_eq_ncard, H.edgeCount_eq_ncard,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr e.mapEdgeSet

/-- The per-triple scale is invariant under changing the representative of a
graph isomorphism class. -/
theorem tripleBetaScale_eq_of_iso {c : ℝ} {n : ℕ}
    {F H : FiniteGraphShape} (e : F.graph ≃g H.graph) :
    tripleBetaScale c n F = tripleBetaScale c n H := by
  unfold tripleBetaScale
  rw [edgeCount_eq_of_iso e, vertexCount_eq_of_iso e]

/-- The `i`th abstract piece embedded in the complete ambient graph through
the canonical representative of its parent support class. -/
noncomputable def pieceTopEmbedding (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    SimpleGraph.Copy (C.shape.pieceShape P i).graph
      (⊤ : SimpleGraph (Fin n)) :=
  (FiniteGraphShape.concreteCopyToAmbientCopy C.representativeCopy).comp
    (C.shape.pieceToParentCopy P i)

/-- Unlabelled form of `pieceTopEmbedding`. -/
noncomputable def pieceTopCopy (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    (C.shape.pieceShape P i).ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
  ⟨(pieceTopEmbedding C P i).toSubgraph,
    ⟨(pieceTopEmbedding C P i).isoToSubgraph⟩⟩

theorem pieceShape_edgeCount_pos (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    0 < (C.shape.pieceShape P i).edgeCount := by
  have hne : (P.piece i).edgeFinset.Nonempty := by
    rw [SimpleGraph.edgeFinset_nonempty]
    exact P.piece_nonempty i
  rw [C.shape.pieceShape_edgeCount P i]
  rw [Set.ncard_eq_toFinset_card']
  exact Finset.card_pos.mpr hne

@[simp]
theorem pieceShape_edgeCount_eq_edgeFinset_card
    (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    (C.shape.pieceShape P i).edgeCount = (P.piece i).edgeFinset.card := by
  rw [C.shape.pieceShape_edgeCount P i]
  exact Set.ncard_eq_toFinset_card' (P.piece i).edgeSet

/-- Orbit tag of a decomposition piece. -/
noncomputable def pieceClass (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    AmbientSupportClass n :=
  (C.shape.pieceShape P i).concreteCopyClass (pieceTopCopy C P i)
    (pieceShape_edgeCount_pos C P i)

/-- Canonical isomorphism from the support-stripped piece shape to the shape
chosen for its ambient orbit tag. -/
noncomputable def pieceShapeIso (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    (C.shape.pieceShape P i).graph ≃g (pieceClass C P i).shape.graph :=
  (C.shape.pieceShape P i).concreteCopyClassShapeIso (pieceTopCopy C P i)
    (pieceShape_edgeCount_pos C P i)

@[simp]
theorem pieceClass_shape_edgeCount (C : AmbientSupportClass n)
    (P : OrderedEdgeDecomposition C.shape.graph m) (i : Fin m) :
    (pieceClass C P i).shape.edgeCount =
      (C.shape.pieceShape P i).edgeCount :=
  FiniteGraphShape.concreteCopyClass_shape_edgeCount _ _ _

/-- A concrete triple of a class shape remembers that class through the
ambient edge orbit of its first copy. -/
theorem class_eq_of_triple_source_subgraph_eq
    (G : SimpleGraph (Fin n))
    {C D : AmbientSupportClass n}
    (left : C.shape.IsomorphismTripleIn G)
    (right : D.shape.IsomorphismTripleIn G)
    (hsource : left.source.1 = right.source.1) : C = D := by
  classical
  let leftTop : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
    C.shape.liftConcreteCopy (by exact le_top) left.source
  let rightTop : D.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)) :=
    D.shape.liftConcreteCopy (by exact le_top) right.source
  let leftFiber := C.concreteCopyToFiber leftTop
  let rightFiber := D.concreteCopyToFiber rightTop
  have hedge : C.shape.concreteCopyEdges leftTop =
      D.shape.concreteCopyEdges rightTop := by
    ext e
    rw [C.shape.mem_concreteCopyEdges, D.shape.mem_concreteCopyEdges]
    change (e : Sym2 (Fin n)) ∈ left.source.1.edgeSet ↔
      (e : Sym2 (Fin n)) ∈ right.source.1.edgeSet
    rw [hsource]
  have hfiber : leftFiber.1 = rightFiber.1 := by
    apply Subtype.ext
    exact hedge
  calc
    C = ambientSupportClass leftFiber.1 := leftFiber.2.symm
    _ = ambientSupportClass rightFiber.1 := congrArg ambientSupportClass hfiber
    _ = D := rightFiber.2

/-- A finite collection of distinct parent graph classes, each with a fixed
ordered `m`-piece edge decomposition.  Unlike `FixedPieceClassDivision`
below, this structure imposes no edge-count window on the pieces.  It is the
data in the paper's aggregate restriction lemma. -/
structure FixedPieceClassDecomposition (Parent : Type*) (n m : ℕ) where
  classOf : Parent → AmbientSupportClass n
  classOf_injective : Function.Injective classOf
  decomposition : ∀ a : Parent,
    OrderedEdgeDecomposition (classOf a).shape.graph m

namespace FixedPieceClassDecomposition

variable {Parent : Type*}
    (D : FixedPieceClassDecomposition Parent n m)

/-- The disjoint union of isomorphism triples over the parent collection. -/
abbrev GlobalTriple (G : SimpleGraph (Fin n)) :=
  Σ a : Parent, (D.classOf a).shape.IsomorphismTripleIn G

/-- One tagged piece triple, with the tag recording its abstract piece type. -/
abbrev PieceTriple (G : SimpleGraph (Fin n)) :=
  Σ C : AmbientSupportClass n, C.shape.IsomorphismTripleIn G

/-- The aggregate restriction map into ordered tuples of tagged piece
triples.  The function type `Fin m → ...` is the finite ordered product in
the displayed statement of the paper. -/
noncomputable def encode (G : SimpleGraph (Fin n)) :
    D.GlobalTriple G → Fin m → PieceTriple (n := n) G
  | ⟨a, triple⟩, i =>
      ⟨pieceClass (D.classOf a) (D.decomposition a) i,
        FiniteGraphShape.reindexIsomorphismTriple
          (pieceShapeIso (D.classOf a) (D.decomposition a) i)
          ((D.classOf a).shape.restrictIsomorphismTriple G
            (D.decomposition a) triple i)⟩

/-- **Paper Lemma 4.3 (aggregate restriction injection).**

For any finite collection of distinct parent graph types equipped with
compatible ordered decompositions into the same number of pieces, the
restriction maps combine to an injection into the disjoint union of ordered
tuples of piece triples.  No block-size hypothesis is needed. -/
theorem encode_injective (G : SimpleGraph (Fin n)) :
    Function.Injective (D.encode G) := by
  classical
  rintro ⟨a, left⟩ ⟨b, right⟩ hencode
  have hsourcePiece (i : Fin m) :
      ((D.classOf a).shape.sourcePiece G (D.decomposition a) left i).1 =
        ((D.classOf b).shape.sourcePiece G (D.decomposition b) right i).1 := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : PieceTriple (n := n) G ↦ z.2.source.1) hi
    exact hval
  have htargetPiece (i : Fin m) :
      ((D.classOf a).shape.targetPiece G (D.decomposition a) left i).1 =
        ((D.classOf b).shape.targetPiece G (D.decomposition b) right i).1 := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : PieceTriple (n := n) G ↦ z.2.target.1) hi
    exact hval
  have hgraphPiece (i : Fin m) :
      FiniteGraphShape.ambientIsomorphismGraph
          ((D.classOf a).shape.restrictIsomorphismTriple G
            (D.decomposition a) left i) =
        FiniteGraphShape.ambientIsomorphismGraph
          ((D.classOf b).shape.restrictIsomorphismTriple G
            (D.decomposition b) right i) := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : PieceTriple (n := n) G ↦
        FiniteGraphShape.ambientIsomorphismGraph z.2) hi
    exact hval
  have hsource : left.source.1 = right.source.1 := by
    calc
      left.source.1 =
          ⨆ i, ((D.classOf a).shape.sourcePiece G
            (D.decomposition a) left i).1 :=
        ((D.classOf a).shape.iSup_sourcePieceEmbedding_toSubgraph G
          (D.decomposition a) left).symm
      _ = ⨆ i, ((D.classOf b).shape.sourcePiece G
            (D.decomposition b) right i).1 := by
        exact congrArg (⨆ i, · i) (funext hsourcePiece)
      _ = right.source.1 :=
        (D.classOf b).shape.iSup_sourcePieceEmbedding_toSubgraph G
          (D.decomposition b) right
  have hclass : D.classOf a = D.classOf b :=
    class_eq_of_triple_source_subgraph_eq G left right hsource
  have hab : a = b := D.classOf_injective hclass
  subst b
  have htarget : left.target.1 = right.target.1 := by
    calc
      left.target.1 =
          ⨆ i, ((D.classOf a).shape.targetPiece G
            (D.decomposition a) left i).1 :=
        ((D.classOf a).shape.iSup_targetPieceEmbedding_toSubgraph G
          (D.decomposition a) left).symm
      _ = ⨆ i, ((D.classOf a).shape.targetPiece G
            (D.decomposition a) right i).1 := by
        exact congrArg (⨆ i, · i) (funext htargetPiece)
      _ = right.target.1 :=
        (D.classOf a).shape.iSup_targetPieceEmbedding_toSubgraph G
          (D.decomposition a) right
  have hgraph :
      FiniteGraphShape.ambientIsomorphismGraph left =
        FiniteGraphShape.ambientIsomorphismGraph right := by
    calc
      FiniteGraphShape.ambientIsomorphismGraph left =
          ⋃ i, FiniteGraphShape.ambientIsomorphismGraph
            ((D.classOf a).shape.restrictIsomorphismTriple G
              (D.decomposition a) left i) :=
        ((D.classOf a).shape.iUnion_ambientIsomorphismGraph_restrict G
          (D.decomposition a) left).symm
      _ = ⋃ i, FiniteGraphShape.ambientIsomorphismGraph
            ((D.classOf a).shape.restrictIsomorphismTriple G
              (D.decomposition a) right i) := by
        exact congrArg (⋃ i, · i) (funext hgraphPiece)
      _ = FiniteGraphShape.ambientIsomorphismGraph right :=
        (D.classOf a).shape.iUnion_ambientIsomorphismGraph_restrict G
          (D.decomposition a) right
  have hsourceCopy : left.source = right.source := Subtype.ext hsource
  have htargetCopy : left.target = right.target := Subtype.ext htarget
  have htriple := FiniteGraphShape.isomorphismTriple_eq_of_source_target_ambientGraph
    hsourceCopy htargetCopy hgraph
  exact Sigma.ext rfl (by simpa using htriple)

end FixedPieceClassDecomposition

/-- Ambient support classes in the block range `[l,3l]`. -/
abbrev BlockClass (n l : ℕ) :=
  {C : AmbientSupportClass n //
    l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l}

/-- A family of parent support classes, each equipped with a fixed `m`-piece
division satisfying the block edge bounds.  Injectivity of `classOf` ensures
that the parent index carries no duplicate isomorphism class. -/
structure FixedPieceClassDivision (Parent : Type*) [Fintype Parent]
    (n m l : ℕ) where
  classOf : Parent → AmbientSupportClass n
  classOf_injective : Function.Injective classOf
  decomposition : ∀ a : Parent,
    OrderedEdgeDecomposition (classOf a).shape.graph m
  piece_lower : ∀ a i,
    l ≤ ((decomposition a).piece i).edgeFinset.card
  piece_upper : ∀ a i,
    ((decomposition a).piece i).edgeFinset.card ≤ 3 * l

namespace FixedPieceClassDivision

variable {Parent : Type*} [Fintype Parent] {l : ℕ}
    (D : FixedPieceClassDivision Parent n m l)

/-- Tagged global triples over the duplicate-free parent class family. -/
abbrev GlobalTriple (G : SimpleGraph (Fin n)) :=
  Σ a : Parent, (D.classOf a).shape.IsomorphismTripleIn G

/-- Tagged block triples.  This is the one-coordinate space whose total
weight is `blockBetaMass`. -/
abbrev BlockTriple (G : SimpleGraph (Fin n)) :=
  Σ B : BlockClass n l, B.1.shape.IsomorphismTripleIn G

/-- The orbit tag of one fixed decomposition piece, bundled with its block
edge-count proof. -/
noncomputable def pieceBlockClass (a : Parent) (i : Fin m) : BlockClass n l :=
  ⟨pieceClass (D.classOf a) (D.decomposition a) i, by
    rw [pieceClass_shape_edgeCount,
      pieceShape_edgeCount_eq_edgeFinset_card]
    exact ⟨D.piece_lower a i, D.piece_upper a i⟩⟩

/-- Aggregate restriction: restrict a global triple, tag each piece by its
ambient support orbit, and reindex it to that orbit's canonical shape. -/
noncomputable def encode (G : SimpleGraph (Fin n)) :
    D.GlobalTriple G → Fin m → BlockTriple (n := n) (l := l) G
  | ⟨a, triple⟩, i =>
      ⟨D.pieceBlockClass a i,
        FiniteGraphShape.reindexIsomorphismTriple
          (pieceShapeIso (D.classOf a) (D.decomposition a) i)
          ((D.classOf a).shape.restrictIsomorphismTriple G
            (D.decomposition a) triple i)⟩

/-- Block-window specialization of the aggregate restriction injection used
in the proof of paper Lemma 4.6.

The tuple recovers the parent class from the union of the first-coordinate
piece subgraphs.  Once that tag is recovered, the pointwise restriction
injection of Lemma 4.2 recovers the global triple. -/
theorem encode_injective (G : SimpleGraph (Fin n)) :
    Function.Injective (D.encode G) := by
  classical
  rintro ⟨a, left⟩ ⟨b, right⟩ hencode
  have hsourcePiece (i : Fin m) :
      ((D.classOf a).shape.sourcePiece G (D.decomposition a) left i).1 =
        ((D.classOf b).shape.sourcePiece G (D.decomposition b) right i).1 := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : BlockTriple (n := n) (l := l) G ↦ z.2.source.1) hi
    exact hval
  have htargetPiece (i : Fin m) :
      ((D.classOf a).shape.targetPiece G (D.decomposition a) left i).1 =
        ((D.classOf b).shape.targetPiece G (D.decomposition b) right i).1 := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : BlockTriple (n := n) (l := l) G ↦ z.2.target.1) hi
    exact hval
  have hgraphPiece (i : Fin m) :
      FiniteGraphShape.ambientIsomorphismGraph
          ((D.classOf a).shape.restrictIsomorphismTriple G
            (D.decomposition a) left i) =
        FiniteGraphShape.ambientIsomorphismGraph
          ((D.classOf b).shape.restrictIsomorphismTriple G
            (D.decomposition b) right i) := by
    have hi := congrFun hencode i
    have hval := congrArg
      (fun z : BlockTriple (n := n) (l := l) G ↦
        FiniteGraphShape.ambientIsomorphismGraph z.2) hi
    exact hval
  have hsource : left.source.1 = right.source.1 := by
    calc
      left.source.1 =
          ⨆ i, ((D.classOf a).shape.sourcePiece G
            (D.decomposition a) left i).1 :=
        ((D.classOf a).shape.iSup_sourcePieceEmbedding_toSubgraph G
          (D.decomposition a) left).symm
      _ = ⨆ i, ((D.classOf b).shape.sourcePiece G
            (D.decomposition b) right i).1 := by
        exact congrArg (⨆ i, · i) (funext hsourcePiece)
      _ = right.source.1 :=
        (D.classOf b).shape.iSup_sourcePieceEmbedding_toSubgraph G
          (D.decomposition b) right
  have hclass : D.classOf a = D.classOf b :=
    class_eq_of_triple_source_subgraph_eq G left right hsource
  have hab : a = b := D.classOf_injective hclass
  subst b
  have htarget : left.target.1 = right.target.1 := by
    calc
      left.target.1 =
          ⨆ i, ((D.classOf a).shape.targetPiece G
            (D.decomposition a) left i).1 :=
        ((D.classOf a).shape.iSup_targetPieceEmbedding_toSubgraph G
          (D.decomposition a) left).symm
      _ = ⨆ i, ((D.classOf a).shape.targetPiece G
            (D.decomposition a) right i).1 := by
        exact congrArg (⨆ i, · i) (funext htargetPiece)
      _ = right.target.1 :=
        (D.classOf a).shape.iSup_targetPieceEmbedding_toSubgraph G
          (D.decomposition a) right
  have hgraph :
      FiniteGraphShape.ambientIsomorphismGraph left =
        FiniteGraphShape.ambientIsomorphismGraph right := by
    calc
      FiniteGraphShape.ambientIsomorphismGraph left =
          ⋃ i, FiniteGraphShape.ambientIsomorphismGraph
            ((D.classOf a).shape.restrictIsomorphismTriple G
              (D.decomposition a) left i) :=
        ((D.classOf a).shape.iUnion_ambientIsomorphismGraph_restrict G
          (D.decomposition a) left).symm
      _ = ⋃ i, FiniteGraphShape.ambientIsomorphismGraph
            ((D.classOf a).shape.restrictIsomorphismTriple G
              (D.decomposition a) right i) := by
        exact congrArg (⋃ i, · i) (funext hgraphPiece)
      _ = FiniteGraphShape.ambientIsomorphismGraph right :=
        (D.classOf a).shape.iUnion_ambientIsomorphismGraph_restrict G
          (D.decomposition a) right
  have hsourceCopy : left.source = right.source := Subtype.ext hsource
  have htargetCopy : left.target = right.target := Subtype.ext htarget
  have htriple := FiniteGraphShape.isomorphismTriple_eq_of_source_target_ambientGraph
    hsourceCopy htargetCopy hgraph
  exact Sigma.ext rfl (by simpa using htriple)

end FixedPieceClassDivision

end AggregateGraphRestriction

end

end LowDegree
