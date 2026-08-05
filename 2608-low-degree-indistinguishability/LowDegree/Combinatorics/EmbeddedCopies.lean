import LowDegree.Combinatorics.GraphCopies
import LowDegree.PlantedModel
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

/-!
# Labelled and unlabelled embedded graph copies

This file proves the finite orbit-counting identities used when regrouping
the labelled-support Parseval sum by abstract graph isomorphism class.
-/

namespace LowDegree

open scoped SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace FiniteGraphShape

universe u v

/-- A graph copy in the complete graph is exactly an injection of its vertex
set into the ambient vertex set. -/
noncomputable def copyTopEquivEmbedding
    (F : FiniteGraphShape.{u}) (V : Type v) [Fintype V] :
    SimpleGraph.Copy F.graph (⊤ : SimpleGraph V) ≃ (F.Vertex ↪ V) where
  toFun f := f.toEmbedding
  invFun f :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro a b hab
            rw [SimpleGraph.top_adj]
            exact f.injective.ne hab.ne }
      injective' := f.injective }
  left_inv f := by
    apply SimpleGraph.Copy.ext
    intro a
    rfl
  right_inv f := by
    apply Function.Embedding.ext
    intro a
    rfl

/-- Number of labelled embeddings of `F` in the complete graph on `V`. -/
theorem card_copy_top (F : FiniteGraphShape.{u})
    (V : Type v) [Fintype V] :
    Fintype.card (SimpleGraph.Copy F.graph (⊤ : SimpleGraph V)) =
      (Fintype.card V).descFactorial F.vertexCount := by
  rw [Fintype.card_congr (F.copyTopEquivEmbedding V),
    Fintype.card_embedding_eq]
  rfl

private theorem sigmaConcreteIso_ext
    {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    {source target : F.ConcreteCopy G}
    {f : F.graph ≃g source.1.coe} {g : F.graph ≃g target.1.coe}
    (hcopy : source = target)
    (hval : ∀ a : F.Vertex, (f a).1 = (g a).1) :
    (⟨source, f⟩ : Σ copy : F.ConcreteCopy G,
      F.graph ≃g copy.1.coe) = ⟨target, g⟩ := by
  subst target
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  apply RelIso.ext
  intro a
  apply Subtype.ext
  exact hval a

/-- A labelled graph copy is equivalently an unlabelled concrete copy
together with one isomorphism from the abstract shape onto that copy. -/
noncomputable def copyEquivConcreteCopySigmaIso
    {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    SimpleGraph.Copy F.graph G ≃
      Σ copy : F.ConcreteCopy G, F.graph ≃g copy.1.coe where
  toFun f :=
    ⟨⟨f.toSubgraph, ⟨f.isoToSubgraph⟩⟩, f.isoToSubgraph⟩
  invFun x := x.1.1.coeCopy.comp x.2.toCopy
  left_inv f := by
    apply SimpleGraph.Copy.ext
    intro a
    rfl
  right_inv x := by
    rcases x with ⟨copy, e⟩
    let f : SimpleGraph.Copy F.graph G := copy.1.coeCopy.comp e.toCopy
    have hsub : f.toSubgraph = copy.1 :=
      isoToAmbientCopy_toSubgraph copy e
    have hcopy :
        (⟨f.toSubgraph, ⟨f.isoToSubgraph⟩⟩ : F.ConcreteCopy G) = copy := by
      apply Subtype.ext
      exact hsub
    apply sigmaConcreteIso_ext hcopy
    intro a
    rfl

/-- The possible labellings of one fixed concrete copy form a torsor for the
automorphism group of the abstract shape. -/
noncomputable def isoToConcreteCopyEquivAutomorphism
    {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (copy : F.ConcreteCopy G) :
    (F.graph ≃g copy.1.coe) ≃ F.Automorphism where
  toFun e := (chosenIso copy).symm.comp e
  invFun a := (chosenIso copy).comp a
  left_inv e := by
    apply RelIso.ext
    intro v
    exact (chosenIso copy).apply_symm_apply (e v)
  right_inv a := by
    apply RelIso.ext
    intro v
    exact (chosenIso copy).symm_apply_apply (a v)

noncomputable instance instFintypeIsoToConcreteCopy
    {V : Type v} [Fintype V]
    {F : FiniteGraphShape.{u}} {G : SimpleGraph V}
    (copy : F.ConcreteCopy G) :
    Fintype (F.graph ≃g copy.1.coe) := by
  letI : Finite (F.graph ≃g copy.1.coe) :=
    DFunLike.finite (F.graph ≃g copy.1.coe)
  exact Fintype.ofFinite (F.graph ≃g copy.1.coe)

/-- The number of labelled copies is the number of unlabelled copies times
the automorphism-group cardinality. -/
theorem labelledCopyCount_eq_nonInducedCopyCount_mul_aut
    {V : Type v} [Fintype V]
    (F : FiniteGraphShape.{u}) (G : SimpleGraph V) :
    Fintype.card (SimpleGraph.Copy F.graph G) =
      F.nonInducedCopyCount G * Fintype.card F.Automorphism := by
  rw [Fintype.card_congr (F.copyEquivConcreteCopySigmaIso G),
    Fintype.card_sigma]
  calc
    (∑ copy : F.ConcreteCopy G,
        Fintype.card (F.graph ≃g copy.1.coe)) =
        ∑ _copy : F.ConcreteCopy G, Fintype.card F.Automorphism := by
          apply Finset.sum_congr rfl
          intro copy _
          exact Fintype.card_congr
            (isoToConcreteCopyEquivAutomorphism (F := F) copy)
    _ = F.nonInducedCopyCount G * Fintype.card F.Automorphism := by
          simp [nonInducedCopyCount]

/-- The orbit-counting identity for embeddings into a complete graph. -/
theorem nonInducedCopyCount_top_mul_aut
    (F : FiniteGraphShape.{u}) (V : Type v) [Fintype V] :
    F.nonInducedCopyCount (⊤ : SimpleGraph V) *
        Fintype.card F.Automorphism =
      (Fintype.card V).descFactorial F.vertexCount := by
  rw [nonInducedCopyCount]
  calc
    Fintype.card (F.ConcreteCopy (⊤ : SimpleGraph V)) *
        Fintype.card F.Automorphism =
        ∑ _copy : F.ConcreteCopy (⊤ : SimpleGraph V),
          Fintype.card F.Automorphism := by simp
    _ = ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph V),
          Fintype.card (F.graph ≃g copy.1.coe) := by
      apply Finset.sum_congr rfl
      intro copy _
      exact (Fintype.card_congr
        (isoToConcreteCopyEquivAutomorphism (F := F) copy)).symm
    _ = Fintype.card
        (Σ copy : F.ConcreteCopy (⊤ : SimpleGraph V),
          F.graph ≃g copy.1.coe) := Fintype.card_sigma.symm
    _ = Fintype.card
        (SimpleGraph.Copy F.graph (⊤ : SimpleGraph V)) :=
      (Fintype.card_congr
        (F.copyEquivConcreteCopySigmaIso (⊤ : SimpleGraph V))).symm
    _ = (Fintype.card V).descFactorial F.vertexCount :=
      F.card_copy_top V

/-- **Embedded-copy formula used before Equation (3.5).**

The number of unlabelled embedded copies of `F` in a complete graph is
`(n)_v / |Aut(F)|`, stated over the reals to match the paper's weights. -/
theorem nonInducedCopyCount_top_eq_fallingFactorial_div_aut
    (F : FiniteGraphShape.{u}) (V : Type v) [Fintype V] :
    (F.nonInducedCopyCount (⊤ : SimpleGraph V) : ℝ) =
      fallingFactorial (Fintype.card V) F.vertexCount /
        (Fintype.card F.Automorphism : ℝ) := by
  have haut : (Fintype.card F.Automorphism : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨(SimpleGraph.Iso.refl : F.graph ≃g F.graph)⟩).ne'
  apply (eq_div_iff haut).2
  rw [← Nat.cast_mul, F.nonInducedCopyCount_top_mul_aut]
  rfl

section CopyMonotonicity

variable {W : Type v} [Fintype W]
    (F : FiniteGraphShape.{u}) {H G : SimpleGraph W}

/-- Regard a concrete copy in a subgraph as the same concrete copy in a
larger graph. -/
noncomputable def liftConcreteCopy (hHG : H ≤ G)
    (copy : F.ConcreteCopy H) : F.ConcreteCopy G := by
  let lifted : G.Subgraph :=
    { verts := copy.1.verts
      Adj := copy.1.Adj
      adj_sub := fun {_ _} h ↦ hHG (copy.1.adj_sub h)
      edge_vert := copy.1.edge_vert
      symm := copy.1.symm }
  refine ⟨lifted, ?_⟩
  simpa only [lifted] using copy.2

@[simp]
theorem liftConcreteCopy_verts (hHG : H ≤ G)
    (copy : F.ConcreteCopy H) :
    (F.liftConcreteCopy hHG copy).1.verts = copy.1.verts := rfl

@[simp]
theorem liftConcreteCopy_adj (hHG : H ≤ G)
    (copy : F.ConcreteCopy H) (u w : W) :
    (F.liftConcreteCopy hHG copy).1.Adj u w ↔ copy.1.Adj u w :=
  Iff.rfl

/-- Restrict a concrete copy to a smaller ambient graph when all of its
edges lie in that graph. -/
noncomputable def restrictConcreteCopy
    (copy : F.ConcreteCopy G) (hedges : copy.1.edgeSet ⊆ H.edgeSet) :
    F.ConcreteCopy H := by
  let restricted : H.Subgraph :=
    { verts := copy.1.verts
      Adj := copy.1.Adj
      adj_sub := by
        intro u w huw
        have he : s(u, w) ∈ copy.1.edgeSet := huw
        exact hedges he
      edge_vert := copy.1.edge_vert
      symm := copy.1.symm }
  refine ⟨restricted, ?_⟩
  simpa only [restricted] using copy.2

/-- Concrete copies in `H` are exactly concrete copies in `G` whose edge
sets lie in `H`. -/
noncomputable def concreteCopyEquivOfLE (hHG : H ≤ G) :
    F.ConcreteCopy H ≃
      {copy : F.ConcreteCopy G // copy.1.edgeSet ⊆ H.edgeSet} where
  toFun copy :=
    ⟨F.liftConcreteCopy hHG copy, fun _e he ↦ copy.1.edgeSet_subset he⟩
  invFun copy := F.restrictConcreteCopy copy.1 copy.2
  left_inv copy := by
    apply Subtype.ext
    apply SimpleGraph.Subgraph.ext <;> rfl
  right_inv copy := by
    apply Subtype.ext
    apply Subtype.ext
    apply SimpleGraph.Subgraph.ext <;> rfl

theorem card_concreteCopies_with_edges_subset (hHG : H ≤ G) :
    Fintype.card {copy : F.ConcreteCopy G //
        copy.1.edgeSet ⊆ H.edgeSet} =
      F.nonInducedCopyCount H := by
  rw [← Fintype.card_congr (F.concreteCopyEquivOfLE hHG)]
  rfl

end CopyMonotonicity

section CopyIsomorphismInvariance

variable {W : Type v} {X : Type*} [Fintype W] [Fintype X]
    (F : FiniteGraphShape.{u}) {G : SimpleGraph W} {H : SimpleGraph X}

/-- Transport an unlabelled concrete copy along an isomorphism of ambient
graphs.  The definition uses a labelled representative internally, but its
underlying subgraph is simply the image of the original concrete copy. -/
noncomputable def mapConcreteCopy (e : G ≃g H)
    (copy : F.ConcreteCopy G) : F.ConcreteCopy H :=
  let f : SimpleGraph.Copy F.graph H :=
    e.toCopy.comp (concreteCopyToAmbientCopy copy)
  ⟨f.toSubgraph, ⟨f.isoToSubgraph⟩⟩

theorem mapConcreteCopy_subgraph (e : G ≃g H)
    (copy : F.ConcreteCopy G) :
    (F.mapConcreteCopy e copy).1 = copy.1.map e.toHom := by
  change
    (SimpleGraph.Subgraph.map
        (e.toHom.comp (concreteCopyToAmbientCopy copy).toHom) ⊤) =
      copy.1.map e.toHom
  rw [SimpleGraph.Subgraph.map_comp]
  change
    (concreteCopyToAmbientCopy copy).toSubgraph.map e.toHom =
      copy.1.map e.toHom
  rw [concreteCopyToAmbientCopy_toSubgraph]

/-- Ambient graph isomorphisms induce equivalences between the corresponding
types of unlabelled concrete copies. -/
noncomputable def concreteCopyEquivIso (e : G ≃g H) :
    F.ConcreteCopy G ≃ F.ConcreteCopy H where
  toFun := F.mapConcreteCopy e
  invFun := F.mapConcreteCopy e.symm
  left_inv copy := by
    apply Subtype.ext
    rw [F.mapConcreteCopy_subgraph, F.mapConcreteCopy_subgraph,
      ← SimpleGraph.Subgraph.map_comp]
    convert SimpleGraph.Subgraph.map_id copy.1 using 2
    apply DFunLike.ext _ _
    intro w
    exact e.symm_apply_apply w
  right_inv copy := by
    apply Subtype.ext
    rw [F.mapConcreteCopy_subgraph, F.mapConcreteCopy_subgraph,
      ← SimpleGraph.Subgraph.map_comp]
    convert SimpleGraph.Subgraph.map_id copy.1 using 2
    apply DFunLike.ext _ _
    intro x
    exact e.apply_symm_apply x

/-- The unlabelled non-induced copy count is invariant under an isomorphism
of ambient graphs. -/
theorem nonInducedCopyCount_congr (e : G ≃g H) :
    F.nonInducedCopyCount G = F.nonInducedCopyCount H := by
  exact Fintype.card_congr (F.concreteCopyEquivIso e)

end CopyIsomorphismInvariance

section AmbientSupports

variable {n : ℕ} (F : FiniteGraphShape.{u})

/-- The ambient edge support of one unlabelled copy in the complete graph. -/
noncomputable def concreteCopyEdges
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    Finset (AmbientEdge n) :=
  Finset.univ.filter fun e : AmbientEdge n ↦
    (e : Sym2 (Fin n)) ∈ copy.1.edgeSet

@[simp]
theorem mem_concreteCopyEdges
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (e : AmbientEdge n) :
    e ∈ F.concreteCopyEdges copy ↔
      (e : Sym2 (Fin n)) ∈ copy.1.edgeSet := by
  simp [concreteCopyEdges]

/-- The edge set of a subgraph's subtype coercion is canonically equivalent
to the ambient edge set recorded by the subgraph. -/
noncomputable def subgraphCoeEdgeEquiv
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) : H.coe.edgeSet ≃ H.edgeSet where
  toFun e := ⟨Sym2.map Subtype.val e.1, by
    have he : e.1 ∈ Sym2.map Subtype.val ⁻¹' H.edgeSet :=
      (Set.ext_iff.mp SimpleGraph.Subgraph.edgeSet_coe e.1).mp e.2
    exact he⟩
  invFun e := by
    let hverts : ∀ v ∈ e.1, v ∈ H.verts :=
      fun _v hv ↦ H.mem_verts_of_mem_edge e.2 hv
    refine ⟨e.1.attachWith hverts, ?_⟩
    apply (Set.ext_iff.mp SimpleGraph.Subgraph.edgeSet_coe _).mpr
    simpa only [Set.mem_preimage, Sym2.attachWith_map_subtypeVal] using e.2
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [Sym2.attachWith_map_subtypeVal]
  right_inv e := by
    apply Subtype.ext
    change Sym2.map Subtype.val (e.1.attachWith _) = e.1
    exact Sym2.attachWith_map_subtypeVal _

/-- A complete-graph concrete copy has exactly as many ambient support edges
as the abstract shape. -/
theorem card_concreteCopyEdges
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (F.concreteCopyEdges copy).card = F.edgeCount := by
  let selected := {e : AmbientEdge n //
    (e : Sym2 (Fin n)) ∈ copy.1.edgeSet}
  let forgetTop : selected ≃ copy.1.edgeSet :=
    { toFun := fun e ↦ ⟨(e.1 : Sym2 (Fin n)), e.2⟩
      invFun := fun e ↦
        ⟨⟨(e.1 : Sym2 (Fin n)), copy.1.edgeSet_subset e.2⟩, e.2⟩
      left_inv := fun e ↦ by cases e; rfl
      right_inv := fun e ↦ by cases e; rfl }
  calc
    (F.concreteCopyEdges copy).card = Fintype.card selected := by
      symm
      apply Fintype.card_of_subtype
      intro e
      rw [F.mem_concreteCopyEdges]
    _ = Fintype.card copy.1.edgeSet := Fintype.card_congr forgetTop
    _ = Fintype.card copy.1.coe.edgeSet :=
      (Fintype.card_congr (subgraphCoeEdgeEquiv copy.1)).symm
    _ = Fintype.card F.graph.edgeSet :=
      (Fintype.card_congr (chosenIso copy).mapEdgeSet).symm
    _ = F.edgeCount := by
      rw [edgeCount_eq_ncard, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card]

/-- A vertex permutation is an automorphism of the complete ambient graph. -/
noncomputable def completeGraphIsoOfPerm (τ : Equiv.Perm (Fin n)) :
    (⊤ : SimpleGraph (Fin n)) ≃g (⊤ : SimpleGraph (Fin n)) where
  toEquiv := τ
  map_rel_iff' := by
    intro u v
    simp only [SimpleGraph.top_adj]
    exact τ.injective.eq_iff.not

/-- The canonical isomorphism between the vertex subtypes of two concrete
copies of the same abstract shape. -/
noncomputable def concreteCopyVertexIso
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    source.1.coe ≃g target.1.coe :=
  (chosenIso target).comp (chosenIso source).symm

/-- Extend the canonical vertex-subtype isomorphism between two copies to a
permutation of the whole ambient vertex set. -/
noncomputable def concreteCopyTransportPerm
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    Equiv.Perm (Fin n) :=
  (F.concreteCopyVertexIso source target).toEquiv.extendSubtype

theorem concreteCopyTransportPerm_apply_of_mem
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (v : Fin n) (hv : v ∈ source.1.verts) :
    F.concreteCopyTransportPerm source target v =
      (F.concreteCopyVertexIso source target ⟨v, hv⟩).1 := by
  exact Equiv.extendSubtype_apply_of_mem
    (F.concreteCopyVertexIso source target).toEquiv v hv

/-- The extended ambient permutation preserves precisely the adjacency
relation of the two concrete copies, including outside their vertex sets
where both spanning coercions have no edges. -/
theorem concreteCopyTransportPerm_adj_iff
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))
    (u v : Fin n) :
    target.1.Adj (F.concreteCopyTransportPerm source target u)
        (F.concreteCopyTransportPerm source target v) ↔
      source.1.Adj u v := by
  let e := F.concreteCopyVertexIso source target
  let τ := F.concreteCopyTransportPerm source target
  constructor
  · intro htarget
    have htu : τ u ∈ target.1.verts := target.1.edge_vert htarget
    have htv : τ v ∈ target.1.verts :=
      target.1.edge_vert (target.1.symm htarget)
    have hu : u ∈ source.1.verts := by
      by_contra hnot
      exact (Equiv.extendSubtype_not_mem e.toEquiv u hnot) htu
    have hv : v ∈ source.1.verts := by
      by_contra hnot
      exact (Equiv.extendSubtype_not_mem e.toEquiv v hnot) htv
    have hiso := e.map_adj_iff (v := ⟨u, hu⟩) (w := ⟨v, hv⟩)
    apply hiso.mp
    change target.1.Adj
      (F.concreteCopyVertexIso source target ⟨u, hu⟩).1
      (F.concreteCopyVertexIso source target ⟨v, hv⟩).1
    rw [← F.concreteCopyTransportPerm_apply_of_mem source target u hu,
      ← F.concreteCopyTransportPerm_apply_of_mem source target v hv]
    exact htarget
  · intro hsource
    have hu : u ∈ source.1.verts := source.1.edge_vert hsource
    have hv : v ∈ source.1.verts :=
      source.1.edge_vert (source.1.symm hsource)
    have hiso := e.map_adj_iff (v := ⟨u, hu⟩) (w := ⟨v, hv⟩)
    have := hiso.mpr hsource
    rw [F.concreteCopyTransportPerm_apply_of_mem source target u hu,
      F.concreteCopyTransportPerm_apply_of_mem source target v hv]
    exact this

/-- The transport permutation is an isomorphism between the spanning
coercions of the two concrete copies. -/
noncomputable def concreteCopySpanningIso
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    source.1.spanningCoe ≃g target.1.spanningCoe where
  toEquiv := F.concreteCopyTransportPerm source target
  map_rel_iff' := by
    intro u v
    exact F.concreteCopyTransportPerm_adj_iff source target u v

/-- The edge-coordinate permutation induced by a permutation of ambient
vertices. -/
noncomputable def ambientEdgeEquivOfPerm (τ : Equiv.Perm (Fin n)) :
    AmbientEdge n ≃ AmbientEdge n :=
  (completeGraphIsoOfPerm τ).mapEdgeSet

/-- Apply a vertex permutation to every edge in an ambient finite support. -/
noncomputable def permuteAmbientSupport (τ : Equiv.Perm (Fin n))
    (S : Finset (AmbientEdge n)) : Finset (AmbientEdge n) :=
  S.map (ambientEdgeEquivOfPerm τ).toEmbedding

/-- The canonical transport permutation sends the complete-graph support of
the source copy exactly onto the support of the target copy. -/
theorem permuteAmbientSupport_concreteCopyTransportPerm
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    permuteAmbientSupport (F.concreteCopyTransportPerm source target)
        (F.concreteCopyEdges source) =
      F.concreteCopyEdges target := by
  classical
  let τ := F.concreteCopyTransportPerm source target
  let ambientIso := completeGraphIsoOfPerm τ
  let copyIso := F.concreteCopySpanningIso source target
  ext e
  constructor
  · intro he
    rw [permuteAmbientSupport, Finset.mem_map] at he
    rcases he with ⟨a, ha, rfl⟩
    rw [F.mem_concreteCopyEdges] at ha ⊢
    exact copyIso.map_mem_edgeSet_iff.mpr ha
  · intro he
    rw [F.mem_concreteCopyEdges] at he
    let a : AmbientEdge n := (ambientEdgeEquivOfPerm τ).symm e
    have haValue : Sym2.map τ (a : Sym2 (Fin n)) =
        (e : Sym2 (Fin n)) := by
      exact congrArg Subtype.val
        ((ambientEdgeEquivOfPerm τ).apply_symm_apply e)
    have ha : (a : Sym2 (Fin n)) ∈ source.1.edgeSet := by
      apply copyIso.map_mem_edgeSet_iff.mp
      change Sym2.map τ (a : Sym2 (Fin n)) ∈ target.1.edgeSet
      rwa [haValue]
    rw [permuteAmbientSupport, Finset.mem_map]
    refine ⟨a, ?_, ?_⟩
    · rwa [F.mem_concreteCopyEdges]
    · exact (ambientEdgeEquivOfPerm τ).apply_symm_apply e

theorem permutedPlant_trans
    (plant : SimpleGraph (Fin n))
    (σ τ : Equiv.Perm (Fin n)) :
    permutedPlant plant (σ.trans τ) =
      (permutedPlant plant σ).map τ.toEmbedding := by
  simp only [permutedPlant, SimpleGraph.map_map]
  rfl

/-- Relabelling an already permuted plant relabels its finite ambient edge
support in the same way. -/
theorem permuteAmbientSupport_permutedPlantEdges
    (plant : SimpleGraph (Fin n))
    (σ τ : Equiv.Perm (Fin n)) :
    permuteAmbientSupport τ (permutedPlantEdges plant σ) =
      permutedPlantEdges plant (σ.trans τ) := by
  classical
  ext e
  constructor
  · intro he
    rw [permuteAmbientSupport, Finset.mem_map] at he
    rcases he with ⟨a, ha, rfl⟩
    rw [mem_permutedPlantEdges_iff] at ha ⊢
    rw [permutedPlant_trans]
    exact (SimpleGraph.Iso.map τ (permutedPlant plant σ)).map_mem_edgeSet_iff.mpr ha
  · intro he
    rw [mem_permutedPlantEdges_iff, permutedPlant_trans] at he
    let a : AmbientEdge n := (ambientEdgeEquivOfPerm τ).symm e
    have haValue : Sym2.map τ (a : Sym2 (Fin n)) =
        (e : Sym2 (Fin n)) := by
      exact congrArg Subtype.val
        ((ambientEdgeEquivOfPerm τ).apply_symm_apply e)
    have ha : (a : Sym2 (Fin n)) ∈ (permutedPlant plant σ).edgeSet := by
      apply (SimpleGraph.Iso.map τ
        (permutedPlant plant σ)).map_mem_edgeSet_iff.mp
      change Sym2.map τ (a : Sym2 (Fin n)) ∈
        ((permutedPlant plant σ).map τ.toEmbedding).edgeSet
      rwa [haValue]
    rw [permuteAmbientSupport, Finset.mem_map]
    refine ⟨a, ?_, ?_⟩
    · rwa [mem_permutedPlantEdges_iff]
    · exact (ambientEdgeEquivOfPerm τ).apply_symm_apply e

/-- Right-composition by a fixed ambient permutation is a permutation of
the finite type of all ambient permutations. -/
noncomputable def rightTransPermEquiv (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ.trans τ
  invFun ρ := ρ.trans τ.symm
  left_inv σ := by
    ext v
    simp
  right_inv ρ := by
    ext v
    simp

theorem permuteAmbientSupport_subset_permutedPlantEdges_trans_iff
    (plant : SimpleGraph (Fin n))
    (S : Finset (AmbientEdge n))
    (σ τ : Equiv.Perm (Fin n)) :
    permuteAmbientSupport τ S ⊆
        permutedPlantEdges plant (σ.trans τ) ↔
      S ⊆ permutedPlantEdges plant σ := by
  rw [← permuteAmbientSupport_permutedPlantEdges plant σ τ]
  exact Finset.map_subset_map

/-- The number of relabellings of a plant containing a support is invariant
under an ambient relabelling of that support. -/
theorem permutationContainmentCount_permuteAmbientSupport
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n))
    (τ : Equiv.Perm (Fin n)) :
    permutationContainmentCount plant (permuteAmbientSupport τ S) =
      permutationContainmentCount plant S := by
  classical
  let source := { σ : Equiv.Perm (Fin n) //
    S ⊆ permutedPlantEdges plant σ }
  let target := { ρ : Equiv.Perm (Fin n) //
    permuteAmbientSupport τ S ⊆ permutedPlantEdges plant ρ }
  let e : source ≃ target :=
  {
    toFun σ := ⟨σ.1.trans τ,
      (permuteAmbientSupport_subset_permutedPlantEdges_trans_iff
        plant S σ.1 τ).mpr σ.2⟩
    invFun ρ := ⟨ρ.1.trans τ.symm, by
      have h := ρ.2
      have hrewrite :
          (ρ.1.trans τ.symm).trans τ = ρ.1 := by
        ext v
        simp
      rw [← hrewrite] at h
      exact (permuteAmbientSupport_subset_permutedPlantEdges_trans_iff
        plant S (ρ.1.trans τ.symm) τ).mp h⟩
    left_inv σ := by
      apply Subtype.ext
      ext v
      simp
    right_inv ρ := by
      apply Subtype.ext
      ext v
      simp }
  rw [permutationContainmentCount, permutationContainmentCount]
  calc
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun ρ ↦ permuteAmbientSupport τ S ⊆
          permutedPlantEdges plant ρ)).card = Fintype.card target := by
      symm
      apply Fintype.card_of_subtype
      intro ρ
      simp
    _ = Fintype.card source := (Fintype.card_congr e).symm
    _ = ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ ↦ S ⊆ permutedPlantEdges plant σ)).card := by
      apply Fintype.card_of_subtype
      intro σ
      simp

/-- All complete-graph embeddings of one abstract shape have the same
permutation-containment count against a fixed plant. -/
theorem permutationContainmentCount_concreteCopyEdges_eq
    (plant : SimpleGraph (Fin n))
    (source target : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    permutationContainmentCount plant (F.concreteCopyEdges source) =
      permutationContainmentCount plant (F.concreteCopyEdges target) := by
  calc
    permutationContainmentCount plant (F.concreteCopyEdges source) =
        permutationContainmentCount plant
          (permuteAmbientSupport
            (F.concreteCopyTransportPerm source target)
            (F.concreteCopyEdges source)) :=
      (permutationContainmentCount_permuteAmbientSupport plant
        (F.concreteCopyEdges source)
        (F.concreteCopyTransportPerm source target)).symm
    _ = permutationContainmentCount plant
        (F.concreteCopyEdges target) := by
      rw [F.permuteAmbientSupport_concreteCopyTransportPerm source target]

/-- A concrete copy has no isolated vertices, so its ambient edge support
determines the entire subgraph and hence the concrete copy. -/
theorem concreteCopyEdges_injective :
    Function.Injective
      (F.concreteCopyEdges :
        F.ConcreteCopy (⊤ : SimpleGraph (Fin n)) → Finset (AmbientEdge n)) := by
  intro source target hedge
  apply Subtype.ext
  apply SimpleGraph.Subgraph.ext
  · rw [← F.concreteCopy_support_eq_verts source,
      ← F.concreteCopy_support_eq_verts target]
    ext v
    simp only [SimpleGraph.Subgraph.mem_support]
    constructor
    · rintro ⟨w, hvw⟩
      have htop : s(v, w) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
        SimpleGraph.Subgraph.edgeSet_subset source.1 hvw
      let e : AmbientEdge n := ⟨s(v, w), htop⟩
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heTarget : e ∈ F.concreteCopyEdges target := by
        rw [← hedge]
        exact heSource
      rw [F.mem_concreteCopyEdges] at heTarget
      exact ⟨w, heTarget⟩
    · rintro ⟨w, hvw⟩
      have htop : s(v, w) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
        SimpleGraph.Subgraph.edgeSet_subset target.1 hvw
      let e : AmbientEdge n := ⟨s(v, w), htop⟩
      have heTarget : e ∈ F.concreteCopyEdges target := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [hedge]
        exact heTarget
      rw [F.mem_concreteCopyEdges] at heSource
      exact ⟨w, heSource⟩
  · funext v w
    apply propext
    have htop : s(v, w) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet ↔ v ≠ w :=
      SimpleGraph.top_adj v w
    constructor
    · intro hvw
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset source.1 hvw⟩
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heTarget : e ∈ F.concreteCopyEdges target := by
        rw [← hedge]
        exact heSource
      rw [F.mem_concreteCopyEdges] at heTarget
      exact heTarget
    · intro hvw
      let e : AmbientEdge n :=
        ⟨s(v, w), SimpleGraph.Subgraph.edgeSet_subset target.1 hvw⟩
      have heTarget : e ∈ F.concreteCopyEdges target := by
        rw [F.mem_concreteCopyEdges]
        exact hvw
      have heSource : e ∈ F.concreteCopyEdges source := by
        rw [hedge]
        exact heTarget
      rw [F.mem_concreteCopyEdges] at heSource
      exact heSource

/-- Finite family of ambient supports carrying an unlabelled copy of `F`. -/
noncomputable def ambientCopySupports : Finset (Finset (AmbientEdge n)) :=
  Finset.univ.image F.concreteCopyEdges

theorem card_ambientCopySupports :
    (F.ambientCopySupports (n := n)).card =
      F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) := by
  rw [ambientCopySupports, Finset.card_image_of_injective _
    F.concreteCopyEdges_injective]
  simp [nonInducedCopyCount]

/-- Relabelling the ambient vertices does not change the number of copies of
an abstract graph shape. -/
theorem nonInducedCopyCount_permutedPlant
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    F.nonInducedCopyCount (permutedPlant plant σ) =
      F.nonInducedCopyCount plant := by
  symm
  exact F.nonInducedCopyCount_congr (SimpleGraph.Iso.map σ plant)

/-- The finite ambient support of a complete-graph copy is contained in a
permuted plant exactly when the copy's graph-theoretic edge set is. -/
theorem concreteCopyEdges_subset_permutedPlantEdges_iff
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    F.concreteCopyEdges copy ⊆ permutedPlantEdges plant σ ↔
      copy.1.edgeSet ⊆ (permutedPlant plant σ).edgeSet := by
  constructor
  · intro h e he
    have htop : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
      copy.1.edgeSet_subset he
    let ambient : AmbientEdge n := ⟨e, htop⟩
    have hambient : ambient ∈ F.concreteCopyEdges copy := by
      rw [F.mem_concreteCopyEdges]
      exact he
    have := h hambient
    rw [mem_permutedPlantEdges_iff] at this
    exact this
  · intro h e he
    rw [mem_permutedPlantEdges_iff]
    apply h
    rwa [← F.mem_concreteCopyEdges]

/-- For each relabelling of the plant, the number of complete-graph copy
supports contained in it is the intrinsic unlabelled copy count of the
original plant. -/
theorem card_completeCopies_contained_in_permutedPlant
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    ((Finset.univ : Finset (F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))).filter
      (fun copy ↦ F.concreteCopyEdges copy ⊆
        permutedPlantEdges plant σ)).card =
      F.nonInducedCopyCount plant := by
  let supportCopies :=
    {copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)) //
      F.concreteCopyEdges copy ⊆ permutedPlantEdges plant σ}
  let edgeCopies :=
    {copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)) //
      copy.1.edgeSet ⊆ (permutedPlant plant σ).edgeSet}
  let e : supportCopies ≃ edgeCopies :=
    Equiv.subtypeEquiv (Equiv.refl _)
      (fun copy ↦ F.concreteCopyEdges_subset_permutedPlantEdges_iff
        plant σ copy)
  calc
    ((Finset.univ : Finset (F.ConcreteCopy
        (⊤ : SimpleGraph (Fin n)))).filter
        (fun copy ↦ F.concreteCopyEdges copy ⊆
          permutedPlantEdges plant σ)).card =
        Fintype.card supportCopies := by
          symm
          apply Fintype.card_of_subtype
          intro copy
          simp
    _ = Fintype.card edgeCopies := Fintype.card_congr e
    _ = F.nonInducedCopyCount (permutedPlant plant σ) := by
          exact F.card_concreteCopies_with_edges_subset le_top
    _ = F.nonInducedCopyCount plant :=
          F.nonInducedCopyCount_permutedPlant plant σ

/-- Double-count pairs `(ambient copy, permutation)` for which the permuted
plant contains that copy.  This is the exact finite orbit-counting identity
behind the classwise Fourier regrouping in Equation (3.5). -/
theorem sum_permutationContainmentCount_completeCopies
    (plant : SimpleGraph (Fin n)) :
    (∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        permutationContainmentCount plant (F.concreteCopyEdges copy)) =
      Fintype.card (Equiv.Perm (Fin n)) *
        F.nonInducedCopyCount plant := by
  classical
  calc
    (∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        permutationContainmentCount plant (F.concreteCopyEdges copy)) =
        ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          ∑ σ : Equiv.Perm (Fin n),
            if F.concreteCopyEdges copy ⊆ permutedPlantEdges plant σ
            then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro copy _
              simp [permutationContainmentCount]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
            if F.concreteCopyEdges copy ⊆ permutedPlantEdges plant σ
            then 1 else 0 := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin n),
          ((Finset.univ : Finset
              (F.ConcreteCopy (⊤ : SimpleGraph (Fin n)))).filter
            (fun copy ↦ F.concreteCopyEdges copy ⊆
              permutedPlantEdges plant σ)).card := by
              apply Finset.sum_congr rfl
              intro σ _
              simp
    _ = ∑ _σ : Equiv.Perm (Fin n),
          F.nonInducedCopyCount plant := by
            apply Finset.sum_congr rfl
            intro σ _
            exact F.card_completeCopies_contained_in_permutedPlant plant σ
    _ = Fintype.card (Equiv.Perm (Fin n)) *
          F.nonInducedCopyCount plant := by simp

/-- Exact natural-number orbit identity for any one embedded copy: the
number of ambient copies times its containment count equals the total number
of `(permutation, copy-in-the-plant)` pairs. -/
theorem nonInducedCopyCount_top_mul_permutationContainmentCount
    (plant : SimpleGraph (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) *
        permutationContainmentCount plant (F.concreteCopyEdges copy) =
      Fintype.card (Equiv.Perm (Fin n)) *
        F.nonInducedCopyCount plant := by
  calc
    F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) *
        permutationContainmentCount plant (F.concreteCopyEdges copy) =
        ∑ _other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          permutationContainmentCount plant
            (F.concreteCopyEdges copy) := by
              simp [nonInducedCopyCount]
    _ = ∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          permutationContainmentCount plant
            (F.concreteCopyEdges other) := by
              apply Finset.sum_congr rfl
              intro other _
              exact F.permutationContainmentCount_concreteCopyEdges_eq
                plant copy other
    _ = Fintype.card (Equiv.Perm (Fin n)) *
          F.nonInducedCopyCount plant :=
      F.sum_permutationContainmentCount_completeCopies plant

/-- Exact real-valued version of the per-copy orbit formula appearing in
Equation (3.5): a fixed embedded support is contained with probability
`N(F,G)|Aut(F)|/(n)_{v(F)}` under a uniform relabelling of the plant. -/
theorem permutationContainmentProbability_concreteCopyEdges
    (plant : SimpleGraph (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (permutationContainmentCount plant (F.concreteCopyEdges copy) : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      (F.nonInducedCopyCount plant : ℝ) *
        (Fintype.card F.Automorphism : ℝ) /
          fallingFactorial n F.vertexCount := by
  have hcopyPos : 0 < F.nonInducedCopyCount
      (⊤ : SimpleGraph (Fin n)) := by
    rw [nonInducedCopyCount]
    exact Fintype.card_pos_iff.mpr ⟨copy⟩
  have hpermPos : 0 < Fintype.card (Equiv.Perm (Fin n)) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hautPos : 0 < Fintype.card F.Automorphism :=
    Fintype.card_pos_iff.mpr
      ⟨(SimpleGraph.Iso.refl : F.graph ≃g F.graph)⟩
  have hdouble :=
    F.nonInducedCopyCount_top_mul_permutationContainmentCount plant copy
  have horbit := F.nonInducedCopyCount_top_mul_aut (Fin n)
  have hdoubleReal :
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (permutationContainmentCount plant
            (F.concreteCopyEdges copy) : ℝ) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (F.nonInducedCopyCount plant : ℝ) := by
    exact_mod_cast hdouble
  have horbitReal :
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (Fintype.card F.Automorphism : ℝ) =
        fallingFactorial n F.vertexCount := by
    calc
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (Fintype.card F.Automorphism : ℝ) =
          (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) *
            Fintype.card F.Automorphism : ℕ) := by norm_num
      _ = ((Fintype.card (Fin n)).descFactorial F.vertexCount : ℕ) :=
        by exact_mod_cast horbit
      _ = fallingFactorial n F.vertexCount := by
        simp [fallingFactorial]
  have hcopyNe :
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast hcopyPos.ne'
  have hpermNe :
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast hpermPos.ne'
  have hautNe : (Fintype.card F.Automorphism : ℝ) ≠ 0 := by
    exact_mod_cast hautPos.ne'
  have hfallingNe : fallingFactorial n F.vertexCount ≠ 0 := by
    rw [← horbitReal]
    exact mul_ne_zero hcopyNe hautNe
  apply (div_eq_div_iff hpermNe hfallingNe).2
  rw [← horbitReal]
  calc
    (permutationContainmentCount plant
          (F.concreteCopyEdges copy) : ℝ) *
        ((F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (Fintype.card F.Automorphism : ℝ)) =
        ((F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (permutationContainmentCount plant
            (F.concreteCopyEdges copy) : ℝ)) *
          (Fintype.card F.Automorphism : ℝ) := by ring
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (F.nonInducedCopyCount plant : ℝ)) *
        (Fintype.card F.Automorphism : ℝ) := by rw [hdoubleReal]
    _ = (F.nonInducedCopyCount plant : ℝ) *
        (Fintype.card F.Automorphism : ℝ) *
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by ring

/-- **Equation (3.5), one exact isomorphism-class summand.**

Summing squared Fourier coefficients over every embedded support isomorphic
to `F` gives the paper's exact class weight.  The explicit `copy` witness is
the natural domain guard `(v(F) ≤ n)`; classes with no ambient embedding do
not occur in the regrouped support sum. -/
theorem sum_fourierCoeff_sq_over_concreteCopies
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (plantedLikelihood θ plant)
          (F.concreteCopyEdges other)) ^ 2) =
      ((1 - θ.p) / θ.p) ^ F.edgeCount *
        ((F.nonInducedCopyCount plant : ℝ) ^ 2 *
          (Fintype.card F.Automorphism : ℝ)) /
            fallingFactorial n F.vertexCount := by
  have hcopyPos : 0 < F.nonInducedCopyCount
      (⊤ : SimpleGraph (Fin n)) := by
    rw [nonInducedCopyCount]
    exact Fintype.card_pos_iff.mpr ⟨copy⟩
  have hautPos : 0 < Fintype.card F.Automorphism :=
    Fintype.card_pos_iff.mpr
      ⟨(SimpleGraph.Iso.refl : F.graph ≃g F.graph)⟩
  have hcopyNe :
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast hcopyPos.ne'
  have hautNe : (Fintype.card F.Automorphism : ℝ) ≠ 0 := by
    exact_mod_cast hautPos.ne'
  have horbitReal :
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (Fintype.card F.Automorphism : ℝ) =
        fallingFactorial n F.vertexCount := by
    calc
      (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          (Fintype.card F.Automorphism : ℝ) =
          (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) *
            Fintype.card F.Automorphism : ℕ) := by norm_num
      _ = ((Fintype.card (Fin n)).descFactorial F.vertexCount : ℕ) := by
        exact_mod_cast F.nonInducedCopyCount_top_mul_aut (Fin n)
      _ = fallingFactorial n F.vertexCount := by
        simp [fallingFactorial]
  have hfallingNe : fallingFactorial n F.vertexCount ≠ 0 := by
    rw [← horbitReal]
    exact mul_ne_zero hcopyNe hautNe
  have hweightSq : (θ.forcedWeight ^ F.edgeCount) ^ 2 =
      ((1 - θ.p) / θ.p) ^ F.edgeCount := by
    calc
      (θ.forcedWeight ^ F.edgeCount) ^ 2 =
          (θ.forcedWeight ^ 2) ^ F.edgeCount := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
      _ = ((1 - θ.p) / θ.p) ^ F.edgeCount := by
        rw [θ.forcedWeight_sq]
  have hterm (other : F.ConcreteCopy
      (⊤ : SimpleGraph (Fin n))) :
      (fourierCoeff θ (plantedLikelihood θ plant)
          (F.concreteCopyEdges other)) ^ 2 =
        (((F.nonInducedCopyCount plant : ℝ) *
            (Fintype.card F.Automorphism : ℝ) /
              fallingFactorial n F.vertexCount) *
          θ.forcedWeight ^ F.edgeCount) ^ 2 := by
    rw [fourierCoeff_plantedLikelihood,
      F.permutationContainmentProbability_concreteCopyEdges plant other,
      F.card_concreteCopyEdges]
  calc
    (∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (plantedLikelihood θ plant)
          (F.concreteCopyEdges other)) ^ 2) =
        (F.nonInducedCopyCount (⊤ : SimpleGraph (Fin n)) : ℝ) *
          ((((F.nonInducedCopyCount plant : ℝ) *
              (Fintype.card F.Automorphism : ℝ) /
                fallingFactorial n F.vertexCount) *
            θ.forcedWeight ^ F.edgeCount) ^ 2) := by
      simp_rw [hterm]
      simp [nonInducedCopyCount]
    _ = ((1 - θ.p) / θ.p) ^ F.edgeCount *
        ((F.nonInducedCopyCount plant : ℝ) ^ 2 *
          (Fintype.card F.Automorphism : ℝ)) /
            fallingFactorial n F.vertexCount := by
      rw [← horbitReal]
      field_simp [hcopyNe, hautNe]
      rw [hweightSq]

/-- Sparse-parameter specialization of the preceding theorem, literally the
`alphaWeight` summand used in Equation (3.5). -/
theorem sum_fourierCoeff_sq_over_concreteCopies_eq_alphaWeight
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (c : ℝ) (hp : θ.p = c / (n : ℝ))
    (copy : F.ConcreteCopy (⊤ : SimpleGraph (Fin n))) :
    (∑ other : F.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
        (fourierCoeff θ (plantedLikelihood θ plant)
          (F.concreteCopyEdges other)) ^ 2) =
      alphaWeight c n F.edgeCount F.vertexCount
        (F.nonInducedCopyCount plant)
        (Fintype.card F.Automorphism) := by
  rw [F.sum_fourierCoeff_sq_over_concreteCopies θ plant copy,
    alphaWeight, hp]

end AmbientSupports

end FiniteGraphShape

end

end LowDegree
