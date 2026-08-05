import LowDegree.Asymptotics.LeadingTerm
import LowDegree.Combinatorics.IsomorphismTriples
import LowDegree.Combinatorics.TreeDecomposition
import LowDegree.Combinatorics.WeightedTransport
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Concrete finite graph copies and isomorphism triples

This file supplies the graph-facing specialization of the finite counting
kernel in `LowDegree.Combinatorics.IsomorphismTriples`.

The paper indexes Fourier supports by finite simple graphs with no isolated
vertices.  `FiniteGraphShape` records that convention explicitly.  A concrete
copy in an ambient graph is a (not necessarily induced) mathlib subgraph
isomorphic to the shape.  Thus its cardinality is mathlib's
`SimpleGraph.copyCount`, rather than the labelled embedding count.
-/

namespace LowDegree

open scoped SimpleGraph

universe u v

/-- A finite simple-graph shape whose vertex type is exactly its support.

The bundled `Fintype` makes the shape intrinsically finite, while
`support_eq_univ` excludes isolated vertices. -/
structure FiniteGraphShape where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  graph : SimpleGraph Vertex
  support_eq_univ : graph.support = Set.univ

attribute [instance] FiniteGraphShape.vertexFintype

namespace FiniteGraphShape

/-- Strip the ambient isolated vertices from a finite simple graph. -/
noncomputable def supportShape {V : Type u} [Fintype V] (G : SimpleGraph V) :
    FiniteGraphShape.{u} := by
  classical
  letI : Fintype G.support := Fintype.ofFinite G.support
  refine
    { Vertex := G.support
      graph := G.induce G.support
      support_eq_univ := ?_ }
  ext v
  simp only [Set.mem_univ, iff_true]
  rw [SimpleGraph.mem_support]
  rcases v.property with ⟨w, hvw⟩
  have hw : w ∈ G.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨v, G.symm hvw⟩
  exact ⟨⟨w, hw⟩, hvw⟩

/-- The graph automorphisms of a finite support shape. -/
abbrev Automorphism (F : FiniteGraphShape.{u}) : Type u := F.graph ≃g F.graph

/-- Number of vertices of a finite graph shape. -/
def vertexCount (F : FiniteGraphShape.{u}) : ℕ := Fintype.card F.Vertex

/-- Number of edges of a finite graph shape. -/
noncomputable def edgeCount (F : FiniteGraphShape.{u}) : ℕ := by
  exact F.graph.edgeSet.ncard

/-- Stripping isolated ambient vertices preserves the incident-vertex count. -/
theorem supportShape_vertexCount_eq_ncard {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    (supportShape G).vertexCount = G.support.ncard := by
  classical
  change Fintype.card (supportShape G).Vertex = G.support.ncard
  rw [← Nat.card_eq_fintype_card]
  rfl

/-- The inclusion of the support-induced graph maps its edge set bijectively
onto the original graph's edge set. -/
noncomputable def supportShapeEdgeEquiv {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    (supportShape G).graph.edgeSet ≃ G.edgeSet := by
  classical
  let copy : SimpleGraph.Copy (supportShape G).graph G := by
    simpa only [supportShape] using SimpleGraph.Copy.induce G G.support
  let embedding := copy.mapEdgeSet
  refine Equiv.ofBijective embedding ⟨embedding.injective, ?_⟩
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      have ha : a ∈ G.support := by
        rw [SimpleGraph.mem_support]
        exact ⟨b, he⟩
      have hb : b ∈ G.support := by
        rw [SimpleGraph.mem_support]
        exact ⟨a, G.symm he⟩
      let sourceEdge : (supportShape G).graph.edgeSet :=
        ⟨s(⟨a, ha⟩, ⟨b, hb⟩), he⟩
      refine ⟨sourceEdge, ?_⟩
      apply Subtype.ext
      rfl

/-- A finite graph shape's edge count is the cardinality of its edge set. -/
theorem edgeCount_eq_ncard (F : FiniteGraphShape.{u}) :
    F.edgeCount = F.graph.edgeSet.ncard := rfl

/-- Stripping isolated ambient vertices preserves the edge count. -/
theorem supportShape_edgeCount_eq_ncard {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    (supportShape G).edgeCount = G.edgeSet.ncard := by
  rw [edgeCount_eq_ncard, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (supportShapeEdgeEquiv G)

/-- A concrete, unlabelled, non-induced copy of `F` in `G`.

This is deliberately the same subtype used in the definition of
`SimpleGraph.copyCount`.  The subgraph carries its precise vertex set; because
`F` has no isolated vertices, that vertex set contains no artificial isolated
vertices either. -/
def ConcreteCopy {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) : Type v :=
  {H : G.Subgraph // Nonempty (F.graph ≃g H.coe)}

/-- An isomorphism between two concrete copies of the same abstract shape. -/
abbrev CopyIsomorphism {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (source target : F.ConcreteCopy G) : Type v :=
  source.1.coe ≃g target.1.coe

noncomputable instance instFintypeAutomorphism (F : FiniteGraphShape.{u}) :
    Fintype F.Automorphism := by
  letI : Finite F.Automorphism := DFunLike.finite F.Automorphism
  exact Fintype.ofFinite F.Automorphism

noncomputable instance instFintypeConcreteCopy {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) : Fintype (F.ConcreteCopy G) := by
  classical
  change Fintype {H : G.Subgraph // Nonempty (F.graph ≃g H.coe)}
  infer_instance

noncomputable instance instFintypeCopyIsomorphism {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (source target : F.ConcreteCopy G) :
    Fintype (F.CopyIsomorphism source target) := by
  letI : Finite (F.CopyIsomorphism source target) :=
    DFunLike.finite (F.CopyIsomorphism source target)
  exact Fintype.ofFinite (F.CopyIsomorphism source target)

/-- The paper's non-induced copy count `N_G(F)`. -/
noncomputable def nonInducedCopyCount {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) : ℕ :=
  Fintype.card (F.ConcreteCopy G)

/-- Our concrete-copy count is definitionally mathlib's unlabelled
`SimpleGraph.copyCount`. -/
theorem nonInducedCopyCount_eq_copyCount {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    F.nonInducedCopyCount G = G.copyCount F.graph := by
  classical
  unfold nonInducedCopyCount SimpleGraph.copyCount ConcreteCopy
  exact Fintype.card_subtype _

/-- A chosen isomorphism from the abstract shape to a concrete copy. -/
noncomputable def chosenIso {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G) :
    F.graph ≃g copy.1.coe :=
  copy.2.some

/-- A concrete copy of a support shape has no isolated vertices. -/
theorem concreteCopy_coe_support_eq_univ {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G) :
    copy.1.coe.support = Set.univ := by
  let e := chosenIso copy
  ext y
  simp only [Set.mem_univ, iff_true]
  rw [SimpleGraph.mem_support]
  have hx : e.symm y ∈ F.graph.support := by rw [F.support_eq_univ]; trivial
  rw [SimpleGraph.mem_support] at hx
  rcases hx with ⟨z, hz⟩
  refine ⟨e z, ?_⟩
  simpa [e] using (e.map_adj_iff.mpr hz)

/-- Equivalently, the ambient subgraph representing a concrete copy has no
extra isolated vertices: its incident support is exactly its vertex set. -/
theorem concreteCopy_support_eq_verts {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G) :
    copy.1.support = copy.1.verts := by
  apply Set.Subset.antisymm copy.1.support_subset_verts
  intro v hv
  have hsupport : (⟨v, hv⟩ : copy.1.verts) ∈ copy.1.coe.support := by
    rw [concreteCopy_coe_support_eq_univ copy]
    exact Set.mem_univ _
  rw [SimpleGraph.mem_support] at hsupport
  rcases hsupport with ⟨w, hvw⟩
  rw [SimpleGraph.Subgraph.mem_support]
  exact ⟨w, hvw⟩

/-- Isomorphisms between two copies form a torsor for `Aut(F)`.

Conjugating by the chosen identifications with `F` gives the required fiber
equivalence.  The resulting cardinality statements are independent of those
classical choices. -/
noncomputable def copyIsomorphismEquivAutomorphism
    {V : Type v} [Fintype V] {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (source target : F.ConcreteCopy G) :
    F.CopyIsomorphism source target ≃ F.Automorphism where
  toFun hom := (chosenIso target).symm.comp (hom.comp (chosenIso source))
  invFun aut := (chosenIso target).comp (aut.comp (chosenIso source).symm)
  left_inv hom := by
    apply RelIso.ext
    intro v
    simp
  right_inv aut := by
    apply RelIso.ext
    intro v
    simp

/-- The concrete graph instance of the generic `IsomorphismFamily`. -/
noncomputable def isomorphismFamily {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    IsomorphismFamily (F.ConcreteCopy G) F.Automorphism where
  Hom := F.CopyIsomorphism
  fiberEquiv := F.copyIsomorphismEquivAutomorphism

/-- Every concrete isomorphism fiber has cardinality `|Aut(F)|`. -/
theorem card_copyIsomorphism {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (source target : F.ConcreteCopy G) :
    Fintype.card (F.CopyIsomorphism source target) =
      Fintype.card F.Automorphism :=
  Fintype.card_congr (F.copyIsomorphismEquivAutomorphism source target)

/-- The paper's concrete type `Tri_G(F)`: two unlabelled copies of `F` in `G`
together with an isomorphism between them. -/
abbrev IsomorphismTripleIn {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) : Type v :=
  IsomorphismTriple (F.isomorphismFamily G)

/-- **Paper Lemma 4.1 (concrete graph form).**

The number of triples `(F₁°, F₂°, φ)` is
`N_G(F)² |Aut(F)|`. -/
theorem card_isomorphismTriplesIn {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    Fintype.card (F.IsomorphismTripleIn G) =
      F.nonInducedCopyCount G ^ 2 * Fintype.card F.Automorphism := by
  exact card_isomorphismTriples (F.isomorphismFamily G)

/-- Lemma 4.1 stated directly with mathlib's `copyCount`. -/
theorem card_isomorphismTriplesIn_eq_copyCount {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    Fintype.card (F.IsomorphismTripleIn G) =
      G.copyCount F.graph ^ 2 * Fintype.card F.Automorphism := by
  rw [F.card_isomorphismTriplesIn, F.nonInducedCopyCount_eq_copyCount]

/-- The graph-specialized leading weight `β_n(F)`. -/
noncomputable def graphBetaWeight {V : Type v} [Fintype V]
    (c : ℝ) (n : ℕ) (F : FiniteGraphShape.{u}) (G : SimpleGraph V) : ℝ :=
  betaWeight c n F.edgeCount F.vertexCount
    (F.nonInducedCopyCount G) (Fintype.card F.Automorphism)

/-- **Paper Lemma 4.1, second identity (concrete graph form).**

Writing the leading weight using the concrete triple count gives exactly
`n^(e(F)-v(F)) / c^e(F) * |Tri_G(F)|`; negative excess is represented by the
quotient `n^e / n^v`. -/
theorem graphBetaWeight_eq_betaFromTriple {V : Type v} [Fintype V]
    (c : ℝ) (n : ℕ) (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    graphBetaWeight c n F G =
      betaFromTriple (n : ℝ) c F.edgeCount F.vertexCount
        (Fintype.card (F.IsomorphismTripleIn G) : ℝ) := by
  rw [graphBetaWeight, betaFromTriple, betaWeight, F.card_isomorphismTriplesIn]
  push_cast
  rfl

/-- The preceding identity with `N_G(F)` exposed as mathlib's
`SimpleGraph.copyCount`. -/
theorem graphBetaWeight_eq_copyCount_formula {V : Type v} [Fintype V]
    (c : ℝ) (n : ℕ) (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    graphBetaWeight c n F G =
      ((((n : ℝ) ^ F.edgeCount / (n : ℝ) ^ F.vertexCount) /
          c ^ F.edgeCount) *
        ((G.copyCount F.graph : ℝ) ^ 2 *
          (Fintype.card F.Automorphism : ℝ))) := by
  rw [graphBetaWeight, betaWeight, F.nonInducedCopyCount_eq_copyCount]

section Restriction

open TreeDecomposition

variable {m : ℕ}

/-- The support-stripped abstract shape of the `i`th edge piece. -/
noncomputable def pieceShape (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) : FiniteGraphShape.{u} :=
  supportShape (P.piece i)

@[simp]
theorem pieceShape_vertexCount (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) :
    (F.pieceShape P i).vertexCount = (P.vertexFinset i).card := by
  classical
  rw [pieceShape, supportShape_vertexCount_eq_ncard]
  exact Set.ncard_eq_toFinset_card' (P.piece i).support

@[simp]
theorem pieceShape_edgeCount (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) :
    (F.pieceShape P i).edgeCount = (P.piece i).edgeSet.ncard := by
  rw [pieceShape, supportShape_edgeCount_eq_ncard]

theorem vertexCount_eq_graphVertexFinset_card (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) :
    F.vertexCount = P.graphVertexFinset.card := by
  classical
  calc
    F.vertexCount = F.graph.support.ncard := by
      rw [F.support_eq_univ]
      simp [vertexCount]
    _ = P.graphVertexFinset.card := by
      unfold OrderedEdgeDecomposition.graphVertexFinset
      exact Set.ncard_eq_toFinset_card' F.graph.support

/-- The canonical copy of a support-stripped piece inside its parent shape. -/
noncomputable def pieceToParentCopy (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) :
    SimpleGraph.Copy (F.pieceShape P i).graph F.graph :=
  (SimpleGraph.Copy.ofLE (P.piece i) F.graph (P.piece_le i)).comp
    (SimpleGraph.Copy.induce (P.piece i) (P.piece i).support)

@[simp]
theorem pieceToParentCopy_toSubgraph_verts (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) :
    (F.pieceToParentCopy P i).toSubgraph.verts = (P.piece i).support := by
  ext v
  simp [pieceToParentCopy, SimpleGraph.Copy.toSubgraph,
    SimpleGraph.Subgraph.map]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hv
    exact ⟨⟨v, hv⟩, rfl⟩

@[simp]
theorem pieceToParentCopy_toSubgraph_adj (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) (i : Fin m) (v w : F.Vertex) :
    (F.pieceToParentCopy P i).toSubgraph.Adj v w ↔ (P.piece i).Adj v w := by
  simp [pieceToParentCopy, SimpleGraph.Copy.toSubgraph,
    SimpleGraph.Subgraph.map, Relation.Map]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact hab
  · intro hvw
    have hv : v ∈ (P.piece i).support := by
      rw [SimpleGraph.mem_support]
      exact ⟨w, hvw⟩
    have hw : w ∈ (P.piece i).support := by
      rw [SimpleGraph.mem_support]
      exact ⟨v, (P.piece i).symm hvw⟩
    exact ⟨⟨v, hv⟩, ⟨w, hw⟩, hvw, rfl, rfl⟩

/-- The edge pieces, after stripping their isolated ambient vertices and
including them back into the parent, recover the whole parent shape. -/
theorem iSup_pieceToParentCopy_toSubgraph (F : FiniteGraphShape.{u})
    (P : OrderedEdgeDecomposition F.graph m) :
    (⨆ i, (F.pieceToParentCopy P i).toSubgraph) = ⊤ := by
  apply SimpleGraph.Subgraph.ext
  · rw [SimpleGraph.Subgraph.verts_iSup, SimpleGraph.Subgraph.verts_top]
    ext v
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true,
      F.pieceToParentCopy_toSubgraph_verts]
    have hv : v ∈ F.graph.support := by
      rw [F.support_eq_univ]
      exact Set.mem_univ v
    rw [SimpleGraph.mem_support] at hv
    rcases hv with ⟨w, hvw⟩
    have hpiece : ∃ i, (P.piece i).Adj v w := by
      rw [← SimpleGraph.iSup_adj, P.cover]
      exact hvw
    rcases hpiece with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [SimpleGraph.mem_support]
    exact ⟨w, hi⟩
  · funext v w
    apply propext
    simp only [SimpleGraph.Subgraph.iSup_adj,
      F.pieceToParentCopy_toSubgraph_adj, SimpleGraph.Subgraph.top_adj]
    rw [← SimpleGraph.iSup_adj, P.cover]

/-- Mapping subgraphs along a homomorphism commutes with an indexed union. -/
theorem subgraphMap_iSup {A : Type u} {B : Type v}
    {GA : SimpleGraph A} {GB : SimpleGraph B} {I : Type*}
    (f : GA →g GB) (H : I → GA.Subgraph) :
    SimpleGraph.Subgraph.map f (⨆ i, H i) =
      ⨆ i, SimpleGraph.Subgraph.map f (H i) := by
  apply SimpleGraph.Subgraph.ext
  · simp only [SimpleGraph.Subgraph.map_verts,
      SimpleGraph.Subgraph.verts_iSup, Set.image_iUnion]
  · funext a b
    apply propext
    simp only [SimpleGraph.Subgraph.map_adj,
      SimpleGraph.Subgraph.iSup_adj, Relation.Map]
    constructor
    · rintro ⟨x, y, ⟨i, hxy⟩, rfl, rfl⟩
      exact ⟨i, x, y, hxy, rfl, rfl⟩
    · rintro ⟨i, x, y, hxy, rfl, rfl⟩
      exact ⟨x, y, ⟨i, hxy⟩, rfl, rfl⟩

/-- A chosen labelled representative of an unlabelled concrete copy. -/
noncomputable def concreteCopyToAmbientCopy {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G) :
    SimpleGraph.Copy F.graph G :=
  copy.1.coeCopy.comp (chosenIso copy).toCopy

/-- Any isomorphic labelling of a concrete copy has that concrete subgraph as
its image; the conclusion does not depend on the chosen labelling. -/
theorem isoToAmbientCopy_toSubgraph {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G)
    (e : F.graph ≃g copy.1.coe) :
    (copy.1.coeCopy.comp e.toCopy).toSubgraph = copy.1 := by
  apply SimpleGraph.Subgraph.ext
  · ext v
    simp [SimpleGraph.Copy.toSubgraph, SimpleGraph.Subgraph.map]
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).2
    · intro hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      rw [RelIso.apply_symm_apply]
      rfl
  · funext v w
    apply propext
    simp [SimpleGraph.Copy.toSubgraph, SimpleGraph.Subgraph.map, Relation.Map]
    constructor
    · rintro ⟨a, b, hab, rfl, rfl⟩
      exact e.map_adj_iff.mpr hab
    · intro hvw
      have hv : v ∈ copy.1.verts := copy.1.edge_vert hvw
      have hw : w ∈ copy.1.verts := copy.1.edge_vert (copy.1.symm hvw)
      let a : F.Vertex := e.symm ⟨v, hv⟩
      let b : F.Vertex := e.symm ⟨w, hw⟩
      have hab : F.graph.Adj a b := by
        apply e.map_adj_iff.mp
        simpa [a, b] using hvw
      refine ⟨a, b, hab, ?_, ?_⟩
      · dsimp [a]
        rw [RelIso.apply_symm_apply]
        rfl
      · dsimp [b]
        rw [RelIso.apply_symm_apply]
        rfl

/-- The chosen labelled representative has exactly the original unlabelled
subgraph as its image. -/
theorem concreteCopyToAmbientCopy_toSubgraph {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V} (copy : F.ConcreteCopy G) :
    (concreteCopyToAmbientCopy copy).toSubgraph = copy.1 := by
  exact isoToAmbientCopy_toSubgraph copy (chosenIso copy)

/-- Embed an abstract edge piece into the first concrete copy of a global
triple. -/
noncomputable def sourcePieceEmbedding {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    SimpleGraph.Copy (F.pieceShape P i).graph G :=
  (concreteCopyToAmbientCopy triple.source).comp (F.pieceToParentCopy P i)

/-- The first coordinates of all restricted triples recover the first global
concrete copy. -/
theorem iSup_sourcePieceEmbedding_toSubgraph {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) :
    (⨆ i, (F.sourcePieceEmbedding G P triple i).toSubgraph) = triple.source.1 := by
  simp only [sourcePieceEmbedding, SimpleGraph.Copy.toSubgraph]
  change
    (⨆ i, SimpleGraph.Subgraph.map
      ((concreteCopyToAmbientCopy triple.source).toHom.comp
        (F.pieceToParentCopy P i).toHom) ⊤) = triple.source.1
  simp_rw [SimpleGraph.Subgraph.map_comp]
  rw [← subgraphMap_iSup]
  rw [F.iSup_pieceToParentCopy_toSubgraph]
  exact concreteCopyToAmbientCopy_toSubgraph triple.source

/-- The labelled global copy obtained by transporting the chosen labelling of
the first copy through the triple isomorphism. -/
noncomputable def transportedConcreteCopyToAmbientCopy {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (triple : F.IsomorphismTripleIn G) : SimpleGraph.Copy F.graph G :=
  triple.target.1.coeCopy.comp
    (triple.hom.comp (chosenIso triple.source)).toCopy

theorem transportedConcreteCopyToAmbientCopy_toSubgraph
    {V : Type v} [Fintype V] (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (triple : F.IsomorphismTripleIn G) :
    (F.transportedConcreteCopyToAmbientCopy G triple).toSubgraph = triple.target.1 := by
  exact isoToAmbientCopy_toSubgraph triple.target
    (triple.hom.comp (chosenIso triple.source))

/-- Embed the same abstract piece into the second global copy by transporting
it through the global isomorphism.  This is the paper's `ψ(T₁,ᵢ°)`. -/
noncomputable def targetPieceEmbedding {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    SimpleGraph.Copy (F.pieceShape P i).graph G :=
  (F.transportedConcreteCopyToAmbientCopy G triple).comp (F.pieceToParentCopy P i)

/-- The second coordinates of all restricted triples recover the second
global concrete copy. -/
theorem iSup_targetPieceEmbedding_toSubgraph {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) :
    (⨆ i, (F.targetPieceEmbedding G P triple i).toSubgraph) = triple.target.1 := by
  simp only [targetPieceEmbedding, SimpleGraph.Copy.toSubgraph]
  change
    (⨆ i, SimpleGraph.Subgraph.map
      ((F.transportedConcreteCopyToAmbientCopy G triple).toHom.comp
        (F.pieceToParentCopy P i).toHom) ⊤) = triple.target.1
  simp_rw [SimpleGraph.Subgraph.map_comp]
  rw [← subgraphMap_iSup]
  rw [F.iSup_pieceToParentCopy_toSubgraph]
  exact F.transportedConcreteCopyToAmbientCopy_toSubgraph G triple

/-- The first concrete piece in the restriction of a global triple. -/
noncomputable def sourcePiece {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    (F.pieceShape P i).ConcreteCopy G :=
  ⟨(F.sourcePieceEmbedding G P triple i).toSubgraph,
    ⟨(F.sourcePieceEmbedding G P triple i).isoToSubgraph⟩⟩

/-- The transported second concrete piece in the restriction of a global
triple. -/
noncomputable def targetPiece {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    (F.pieceShape P i).ConcreteCopy G :=
  ⟨(F.targetPieceEmbedding G P triple i).toSubgraph,
    ⟨(F.targetPieceEmbedding G P triple i).isoToSubgraph⟩⟩

/-- Restrict the global isomorphism to a piece.  Both piece subgraphs are
identified with the same abstract piece, so their induced isomorphism is the
composition through that abstract graph. -/
noncomputable def pieceIsomorphism {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    (F.pieceShape P i).CopyIsomorphism
      (F.sourcePiece G P triple i) (F.targetPiece G P triple i) :=
  (F.targetPieceEmbedding G P triple i).isoToSubgraph.comp
    (F.sourcePieceEmbedding G P triple i).isoToSubgraph.symm

/-- The concrete restriction map `Δ_F` from Equation (4.3). -/
noncomputable def restrictIsomorphismTriple {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m) :
    F.IsomorphismTripleIn G →
      (∀ i, (F.pieceShape P i).IsomorphismTripleIn G) :=
  fun triple i ↦
    { source := F.sourcePiece G P triple i
      target := F.targetPiece G P triple i
      hom := F.pieceIsomorphism G P triple i }

/-- Expose the graph isomorphism stored in a concrete triple.  This small
adapter unfolds the `Hom` field of the specialized generic family. -/
noncomputable def tripleIsomorphism {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (triple : F.IsomorphismTripleIn G) :
    F.CopyIsomorphism triple.source triple.target :=
  triple.hom

/-- The graph of a concrete triple's isomorphism, viewed in the common
ambient vertex type.  This erases the dependent subgraph vertex types while
retaining the entire partial bijection. -/
def ambientIsomorphismGraph {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (triple : F.IsomorphismTripleIn G) : Set (V × V) :=
  Set.range fun x : triple.source.1.verts ↦
    ((x : V),
      (tripleIsomorphism triple x : V))

/-- On a restricted triple, the ambient isomorphism graph is parametrized by
the common abstract piece. -/
theorem ambientIsomorphismGraph_restrict {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) (i : Fin m) :
    ambientIsomorphismGraph (F.restrictIsomorphismTriple G P triple i) =
      Set.range (fun z : (F.pieceShape P i).Vertex ↦
        ((F.sourcePieceEmbedding G P triple i z : V),
          (F.targetPieceEmbedding G P triple i z : V))) := by
  ext pair
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(F.sourcePieceEmbedding G P triple i).isoToSubgraph.symm x, ?_⟩
    apply Prod.ext
    · exact congrArg Subtype.val
        ((F.sourcePieceEmbedding G P triple i).isoToSubgraph.apply_symm_apply x)
    · rfl
  · rintro ⟨z, rfl⟩
    refine ⟨(F.sourcePieceEmbedding G P triple i).isoToSubgraph z, ?_⟩
    apply Prod.ext
    · rfl
    · change
        ((F.targetPieceEmbedding G P triple i).isoToSubgraph
          ((F.sourcePieceEmbedding G P triple i).isoToSubgraph.symm
            ((F.sourcePieceEmbedding G P triple i).isoToSubgraph z)) : V) =
          (F.targetPieceEmbedding G P triple i z : V)
      rw [RelIso.symm_apply_apply]
      rfl

/-- The piece isomorphisms cover, and agree with, the global isomorphism. -/
theorem iUnion_ambientIsomorphismGraph_restrict {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m)
    (triple : F.IsomorphismTripleIn G) :
    (⋃ i, ambientIsomorphismGraph (F.restrictIsomorphismTriple G P triple i)) =
      ambientIsomorphismGraph triple := by
  ext pair
  constructor
  · intro hpair
    rw [Set.mem_iUnion] at hpair
    rcases hpair with ⟨i, hi⟩
    rw [F.ambientIsomorphismGraph_restrict G P triple i] at hi
    rcases hi with ⟨z, rfl⟩
    refine ⟨(chosenIso triple.source) (F.pieceToParentCopy P i z), ?_⟩
    apply Prod.ext <;> rfl
  · rintro ⟨x, rfl⟩
    let a : F.Vertex := (chosenIso triple.source).symm x
    have ha : a ∈ F.graph.support := by
      rw [F.support_eq_univ]
      exact Set.mem_univ a
    rw [SimpleGraph.mem_support] at ha
    rcases ha with ⟨b, hab⟩
    have hpiece : ∃ i, (P.piece i).Adj a b := by
      rw [← SimpleGraph.iSup_adj, P.cover]
      exact hab
    rcases hpiece with ⟨i, hi⟩
    have hai : a ∈ (P.piece i).support := by
      rw [SimpleGraph.mem_support]
      exact ⟨b, hi⟩
    let z : (F.pieceShape P i).Vertex := ⟨a, hai⟩
    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [F.ambientIsomorphismGraph_restrict G P triple i]
    refine ⟨z, ?_⟩
    apply Prod.ext
    · simp [z, a, sourcePieceEmbedding, concreteCopyToAmbientCopy,
        pieceToParentCopy]
      change triple.source.1.coeCopy
          ((chosenIso triple.source) ((chosenIso triple.source).symm x)) = (x : V)
      rw [RelIso.apply_symm_apply]
      rfl
    · simp [z, a, targetPieceEmbedding, transportedConcreteCopyToAmbientCopy,
        pieceToParentCopy, tripleIsomorphism]
      change triple.target.1.coeCopy
          (tripleIsomorphism triple
            ((chosenIso triple.source) ((chosenIso triple.source).symm x))) =
        (tripleIsomorphism triple x : V)
      rw [RelIso.apply_symm_apply]
      rfl

/-- A concrete triple is determined by its two concrete subgraphs and the
ambient graph of its isomorphism. -/
theorem isomorphismTriple_eq_of_source_target_ambientGraph
    {V : Type v} [Fintype V] {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    {left right : F.IsomorphismTripleIn G}
    (hsource : left.source = right.source)
    (htarget : left.target = right.target)
    (hgraph : ambientIsomorphismGraph left = ambientIsomorphismGraph right) :
    left = right := by
  rcases left with ⟨leftSource, leftTarget, leftHom⟩
  rcases right with ⟨rightSource, rightTarget, rightHom⟩
  dsimp only [IsomorphismTriple.source] at hsource
  subst rightSource
  dsimp only [IsomorphismTriple.target] at htarget
  subst rightTarget
  congr 1
  apply RelIso.ext
  intro x
  apply Subtype.ext
  have hx :
      ((x : V), (tripleIsomorphism
        (⟨leftSource, leftTarget, leftHom⟩ : F.IsomorphismTripleIn G) x : V)) ∈
        ambientIsomorphismGraph
          (⟨leftSource, leftTarget, leftHom⟩ : F.IsomorphismTripleIn G) :=
    ⟨x, rfl⟩
  rw [hgraph] at hx
  rcases hx with ⟨y, hy⟩
  have hyx : y = x := by
    apply Subtype.ext
    exact congrArg Prod.fst hy
  subst y
  exact (congrArg Prod.snd hy).symm

/-- **Paper Lemma 4.2 (concrete graph form).**  Restricting and transporting
an isomorphism triple along a support-stripped ordered edge decomposition is
injective. -/
theorem restrictIsomorphismTriple_injective {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m) :
    Function.Injective (F.restrictIsomorphismTriple G P) := by
  intro left right hrestrict
  have hpiece (i : Fin m) :
      F.restrictIsomorphismTriple G P left i =
        F.restrictIsomorphismTriple G P right i :=
    congrFun hrestrict i
  have hsourcePieces :
      (fun i ↦ (F.sourcePiece G P left i).1) =
        (fun i ↦ (F.sourcePiece G P right i).1) := by
    funext i
    exact congrArg Subtype.val
      (congrArg (fun triple : (F.pieceShape P i).IsomorphismTripleIn G ↦
        triple.source) (hpiece i))
  have htargetPieces :
      (fun i ↦ (F.targetPiece G P left i).1) =
        (fun i ↦ (F.targetPiece G P right i).1) := by
    funext i
    exact congrArg Subtype.val
      (congrArg (fun triple : (F.pieceShape P i).IsomorphismTripleIn G ↦
        triple.target) (hpiece i))
  have hsourceVal : left.source.1 = right.source.1 := by
    calc
      left.source.1 = ⨆ i, (F.sourcePiece G P left i).1 :=
        (F.iSup_sourcePieceEmbedding_toSubgraph G P left).symm
      _ = ⨆ i, (F.sourcePiece G P right i).1 :=
        congrArg (fun pieces : Fin m → G.Subgraph ↦ ⨆ i, pieces i) hsourcePieces
      _ = right.source.1 := F.iSup_sourcePieceEmbedding_toSubgraph G P right
  have htargetVal : left.target.1 = right.target.1 := by
    calc
      left.target.1 = ⨆ i, (F.targetPiece G P left i).1 :=
        (F.iSup_targetPieceEmbedding_toSubgraph G P left).symm
      _ = ⨆ i, (F.targetPiece G P right i).1 :=
        congrArg (fun pieces : Fin m → G.Subgraph ↦ ⨆ i, pieces i) htargetPieces
      _ = right.target.1 := F.iSup_targetPieceEmbedding_toSubgraph G P right
  have hsource : left.source = right.source := Subtype.ext hsourceVal
  have htarget : left.target = right.target := Subtype.ext htargetVal
  have hgraphPieces :
      (fun i ↦ ambientIsomorphismGraph
        (F.restrictIsomorphismTriple G P left i)) =
      (fun i ↦ ambientIsomorphismGraph
        (F.restrictIsomorphismTriple G P right i)) := by
    funext i
    exact congrArg
      (fun triple : (F.pieceShape P i).IsomorphismTripleIn G ↦
        ambientIsomorphismGraph triple) (hpiece i)
  have hgraph : ambientIsomorphismGraph left = ambientIsomorphismGraph right := by
    calc
      ambientIsomorphismGraph left =
          ⋃ i, ambientIsomorphismGraph (F.restrictIsomorphismTriple G P left i) :=
        (F.iUnion_ambientIsomorphismGraph_restrict G P left).symm
      _ = ⋃ i, ambientIsomorphismGraph
          (F.restrictIsomorphismTriple G P right i) :=
        congrArg (fun graphs : Fin m → Set (V × V) ↦ ⋃ i, graphs i) hgraphPieces
      _ = ambientIsomorphismGraph right :=
        F.iUnion_ambientIsomorphismGraph_restrict G P right
  exact isomorphismTriple_eq_of_source_target_ambientGraph hsource htarget hgraph

/-- Cardinality consequence of the concrete restriction injection. -/
theorem card_isomorphismTriplesIn_le_prod {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m) :
    Fintype.card (F.IsomorphismTripleIn G) ≤
      ∏ i, Fintype.card ((F.pieceShape P i).IsomorphismTripleIn G) := by
  classical
  calc
    Fintype.card (F.IsomorphismTripleIn G) ≤
        Fintype.card (∀ i, (F.pieceShape P i).IsomorphismTripleIn G) :=
      Fintype.card_le_of_injective (F.restrictIsomorphismTriple G P)
        (F.restrictIsomorphismTriple_injective G P)
    _ = ∏ i, Fintype.card ((F.pieceShape P i).IsomorphismTripleIn G) :=
      Fintype.card_pi

/-- Lemma 4.2's product bound with every triple cardinality expanded as
`N_G(T)² |Aut(T)|`. -/
theorem copyCount_sq_mul_aut_le_prod {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m) :
    G.copyCount F.graph ^ 2 * Fintype.card F.Automorphism ≤
      ∏ i, (G.copyCount (F.pieceShape P i).graph ^ 2 *
        Fintype.card (F.pieceShape P i).Automorphism) := by
  simpa only [card_isomorphismTriplesIn_eq_copyCount] using
    F.card_isomorphismTriplesIn_le_prod G P

/-- **Equation (4.4), concrete graph form.**  The actual restriction map of
Lemma 4.2, together with the edge-partition and vertex-overlap identities,
gives the paper's product bound for graph-specialized `β` weights. -/
theorem graphBetaWeight_le_overlap_mul_prod
    {V : Type v} [Fintype V]
    (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n)
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V)
    (P : OrderedEdgeDecomposition F.graph m) :
    F.graphBetaWeight c n G ≤
      (n : ℝ) ^ P.overlap *
        ∏ i, (F.pieceShape P i).graphBetaWeight c n G := by
  classical
  have hedgeFinset (H : SimpleGraph F.Vertex) :
      H.edgeSet.ncard = H.edgeFinset.card := by
    exact Set.ncard_eq_toFinset_card' H.edgeSet
  have hedges : F.edgeCount = ∑ i, (F.pieceShape P i).edgeCount := by
    calc
      F.edgeCount = F.graph.edgeFinset.card := by
        rw [edgeCount_eq_ncard]
        exact hedgeFinset F.graph
      _ = ∑ i, (P.piece i).edgeFinset.card := P.card_edges_eq_sum
      _ = ∑ i, (F.pieceShape P i).edgeCount := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [F.pieceShape_edgeCount P i]
        exact (hedgeFinset (P.piece i)).symm
  have hvertices :
      (∑ i, (F.pieceShape P i).vertexCount) =
        F.vertexCount + P.overlap := by
    calc
      (∑ i, (F.pieceShape P i).vertexCount) =
          ∑ i, (P.vertexFinset i).card := by
        simp only [F.pieceShape_vertexCount]
      _ = P.overlap + P.graphVertexFinset.card :=
        P.overlap_add_graphVertex_card.symm
      _ = F.vertexCount + P.overlap := by
        rw [← F.vertexCount_eq_graphVertexFinset_card P]
        omega
  have htriple :
      (Fintype.card (F.IsomorphismTripleIn G) : ℝ) ≤
        ∏ i, (Fintype.card
          ((F.pieceShape P i).IsomorphismTripleIn G) : ℝ) := by
    exact_mod_cast F.card_isomorphismTriplesIn_le_prod G P
  rw [F.graphBetaWeight_eq_betaFromTriple]
  simp_rw [graphBetaWeight_eq_betaFromTriple]
  exact beta_le_overlap_mul_prod
    (n := (n : ℝ)) (c := c)
    (edgeCount := F.edgeCount) (vertexCount := F.vertexCount)
    (overlap := P.overlap)
    (pieceEdges := fun i ↦ (F.pieceShape P i).edgeCount)
    (pieceVertices := fun i ↦ (F.pieceShape P i).vertexCount)
    (tripleCount := (Fintype.card (F.IsomorphismTripleIn G) : ℝ))
    (pieceTripleCount := fun i ↦
      (Fintype.card ((F.pieceShape P i).IsomorphismTripleIn G) : ℝ))
    (by exact_mod_cast hn) hc hedges hvertices
    (by positivity) (fun _i ↦ by positivity) htriple

end Restriction

end FiniteGraphShape

end LowDegree
