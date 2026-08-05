import LowDegree.Asymptotics.ClusterExpansion
import LowDegree.Asymptotics.ConnectedBetaMass
import LowDegree.Combinatorics.AggregateGraphRestriction
import LowDegree.Combinatorics.ConnectedComponentDecomposition

/-!
# Graph-specific connected-component expansion

This module specializes the abstract finite component expansion to the
tagged isomorphism triples occurring in the paper.  The tag is an
`AmbientSupportClass`; the components of a tagged triple are obtained by
restricting it to the canonically ordered connected components of its shape,
then reindexing every restricted triple to the canonical representative of
its ambient support orbit.

The component list remembers its length.  Consequently its injectivity proof
also covers two parent shapes with different numbers of components: equality
of the lists first forces equality of the component counts, after which the
ambient source subgraphs recover the parent class and the restricted triples
recover the parent triple.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph
open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

open TreeDecomposition
open AggregateGraphRestriction

namespace GraphComponentExpansion

variable {n : ℕ}

/-- All isomorphism triples in a plant, tagged by their duplicate-free
ambient support class. -/
abbrev TaggedTriple (plant : SimpleGraph (Fin n)) :=
  Σ C : AmbientSupportClass n, C.shape.IsomorphismTripleIn plant

/-- The `i`th connected-component restriction of a tagged triple, reindexed
to the canonical shape of that component's ambient support class. -/
noncomputable def componentTriple (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) (i : Fin z.1.shape.componentCount) :
    TaggedTriple plant :=
  ⟨pieceClass z.1 z.1.shape.connectedComponentDecomposition i,
    FiniteGraphShape.reindexIsomorphismTriple
      (pieceShapeIso z.1 z.1.shape.connectedComponentDecomposition i)
      (z.1.shape.restrictIsomorphismTriple plant
        z.1.shape.connectedComponentDecomposition z.2 i)⟩

/-- The ordered list of connected-component restrictions. -/
noncomputable def componentTriples (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) : List (TaggedTriple plant) :=
  List.ofFn (componentTriple plant z)

@[simp]
theorem componentTriples_length (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) :
    (componentTriples plant z).length = z.1.shape.componentCount := by
  simp [componentTriples]

/-- A nonempty graph shape has at least one connected component. -/
theorem componentCount_pos_of_edgeCount_pos
    (F : FiniteGraphShape) (hF : 0 < F.edgeCount) :
    0 < F.componentCount := by
  have hedge : F.graph.edgeSet.Nonempty := by
    rw [← Set.ncard_pos]
    exact hF
  rcases hedge with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      exact Fintype.card_pos_iff.mpr ⟨F.graph.connectedComponentMk u⟩

/-- Every ambient support class is represented by a genuinely nonempty
shape. -/
theorem ambientSupportClass_edgeCount_pos (C : AmbientSupportClass n) :
    0 < C.shape.edgeCount := by
  rw [C.shape_edgeCount_eq_representative_card]
  exact C.representative.2.card_pos

/-- An ambient support class can exist only in a positive-size ambient
complete graph. -/
theorem ambientSize_pos (C : AmbientSupportClass n) : 0 < n := by
  obtain ⟨e, he⟩ := C.representative.2
  let v : Fin n := e.1.out.1
  have hcard : 0 < Fintype.card (Fin n) :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  simpa using hcard

/-- Each component restriction is connected after its shape is changed to
the canonical ambient-orbit representative. -/
theorem componentTriple_connected (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) (i : Fin z.1.shape.componentCount) :
    (componentTriple plant z i).1.shape.graph.Connected := by
  exact
    (pieceShapeIso z.1 z.1.shape.connectedComponentDecomposition i).connected_iff.mp
      (z.1.shape.pieceShape_connected_connectedComponentDecomposition i)

/-- The tagged component list is injective.  In particular, its length
prevents collisions between shapes having different component counts. -/
theorem componentTriples_injective (plant : SimpleGraph (Fin n)) :
    Function.Injective (componentTriples plant) := by
  rintro ⟨C, left⟩ ⟨D, right⟩ hlist
  have htuple :
      (⟨C.shape.componentCount,
          componentTriple plant ⟨C, left⟩⟩ :
        Σ m : ℕ, Fin m → TaggedTriple plant) =
      ⟨D.shape.componentCount,
          componentTriple plant ⟨D, right⟩⟩ := by
    exact List.ofFn_inj'.mp hlist
  rcases Fin.sigma_eq_iff_eq_comp_cast.mp htuple with ⟨hcount, hfun⟩
  have hsourcePiece (i : Fin C.shape.componentCount) :
      (C.shape.sourcePiece plant C.shape.connectedComponentDecomposition
          left i).1 =
        (D.shape.sourcePiece plant D.shape.connectedComponentDecomposition
          right (Fin.cast hcount i)).1 := by
    have hi := congrFun hfun i
    have hval := congrArg
      (fun z : TaggedTriple plant ↦ z.2.source.1) hi
    simpa only [componentTriple,
      FiniteGraphShape.reindexIsomorphismTriple_source_val] using hval
  have hsource : left.source.1 = right.source.1 := by
    calc
      left.source.1 =
          ⨆ i, (C.shape.sourcePiece plant
            C.shape.connectedComponentDecomposition left i).1 :=
        (C.shape.iSup_sourcePieceEmbedding_toSubgraph plant
          C.shape.connectedComponentDecomposition left).symm
      _ = ⨆ i, (D.shape.sourcePiece plant
            D.shape.connectedComponentDecomposition right
              (Fin.cast hcount i)).1 := by
        exact congrArg (⨆ i, · i) (funext hsourcePiece)
      _ = ⨆ i, (D.shape.sourcePiece plant
            D.shape.connectedComponentDecomposition right i).1 := by
        exact (Fin.castOrderIso hcount).toEquiv.iSup_comp
          (g := fun i ↦ (D.shape.sourcePiece plant
            D.shape.connectedComponentDecomposition right i).1)
      _ = right.source.1 :=
        D.shape.iSup_sourcePieceEmbedding_toSubgraph plant
          D.shape.connectedComponentDecomposition right
  have hCD : C = D :=
    class_eq_of_triple_source_subgraph_eq plant left right hsource
  subst D
  rw [show hcount = rfl from Subsingleton.elim _ _] at hfun
  simp only [Fin.cast_refl, Function.comp_id] at hfun
  have hreindexed (i : Fin C.shape.componentCount) :
      FiniteGraphShape.reindexIsomorphismTriple
          (pieceShapeIso C C.shape.connectedComponentDecomposition i)
          (C.shape.restrictIsomorphismTriple plant
            C.shape.connectedComponentDecomposition left i) =
        FiniteGraphShape.reindexIsomorphismTriple
          (pieceShapeIso C C.shape.connectedComponentDecomposition i)
          (C.shape.restrictIsomorphismTriple plant
            C.shape.connectedComponentDecomposition right i) := by
    have hi := congrFun hfun i
    exact eq_of_heq (Sigma.mk.inj_iff.mp hi).2
  have hrestricted :
      C.shape.restrictIsomorphismTriple plant
          C.shape.connectedComponentDecomposition left =
        C.shape.restrictIsomorphismTriple plant
          C.shape.connectedComponentDecomposition right := by
    funext i
    exact
      (FiniteGraphShape.reindexIsomorphismTripleEquiv
        (pieceShapeIso C C.shape.connectedComponentDecomposition i)).injective
        (hreindexed i)
  have hlr : left = right :=
    C.shape.restrictIsomorphismTriple_injective plant
      C.shape.connectedComponentDecomposition hrestricted
  exact Sigma.ext rfl (by simpa using hlr)

/-- The concrete `ComponentEncoding` used in Lemma 4.4.  Every tagged
triple is active, while connected objects are exactly those whose tagged
shape is connected. -/
noncomputable def encoding (plant : SimpleGraph (Fin n)) :
    ComponentEncoding (TaggedTriple plant) where
  active := fun _ ↦ True
  connected := fun z ↦ z.1.shape.graph.Connected
  components := componentTriples plant
  components_nonempty := by
    rintro ⟨z, hz⟩
    rw [List.ne_nil_iff_length_pos, componentTriples_length]
    exact componentCount_pos_of_edgeCount_pos z.1.shape
      (ambientSupportClass_edgeCount_pos z.1)
  component_connected := by
    rintro ⟨z, hz⟩ b hb
    rw [componentTriples, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩
    exact componentTriple_connected plant z i
  components_injective := by
    intro left _hleft right _hright
    intro hcomponents
    exact componentTriples_injective plant hcomponents

/-! ### Per-triple beta weights and component factorization -/

/-- Edge counts add across the connected-component decomposition. -/
theorem edgeCount_eq_sum_connectedComponent_edgeCount
    (F : FiniteGraphShape) :
    F.edgeCount =
      ∑ i : Fin F.componentCount,
        (F.pieceShape F.connectedComponentDecomposition i).edgeCount := by
  calc
    F.edgeCount = F.graph.edgeFinset.card := by
      rw [FiniteGraphShape.edgeCount_eq_ncard]
      exact Set.ncard_eq_toFinset_card' _
    _ = ∑ i : Fin F.componentCount,
        (F.connectedComponentDecomposition.piece i).edgeFinset.card :=
      F.connectedComponentDecomposition.card_edges_eq_sum
    _ = ∑ i : Fin F.componentCount,
        (F.pieceShape F.connectedComponentDecomposition i).edgeCount := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [F.pieceShape_edgeCount F.connectedComponentDecomposition i]
      exact (Set.ncard_eq_toFinset_card' _).symm

/-- Connected components have disjoint vertex sets, so their vertex counts
sum exactly to the parent vertex count. -/
theorem sum_connectedComponent_vertexCount_eq (F : FiniteGraphShape) :
    (∑ i : Fin F.componentCount,
      (F.pieceShape F.connectedComponentDecomposition i).vertexCount) =
      F.vertexCount := by
  calc
    (∑ i : Fin F.componentCount,
        (F.pieceShape F.connectedComponentDecomposition i).vertexCount) =
        ∑ i : Fin F.componentCount,
          (F.connectedComponentDecomposition.vertexFinset i).card := by
      simp only [FiniteGraphShape.pieceShape_vertexCount]
    _ = F.connectedComponentDecomposition.overlap +
        F.connectedComponentDecomposition.graphVertexFinset.card :=
      F.connectedComponentDecomposition.overlap_add_graphVertex_card.symm
    _ = F.vertexCount := by
      rw [F.connectedComponentDecomposition_overlap, zero_add,
        ← F.vertexCount_eq_graphVertexFinset_card
          F.connectedComponentDecomposition]

/-- The beta scale of one triple is submultiplicative over connected
components.  Here the overlap factor is exactly one. -/
theorem tripleBetaScale_le_prod_connectedComponents
    (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n)
    (F : FiniteGraphShape) :
    tripleBetaScale c n F ≤
      ∏ i : Fin F.componentCount,
        tripleBetaScale c n
          (F.pieceShape F.connectedComponentDecomposition i) := by
  have h := beta_le_overlap_mul_prod
    (n := (n : ℝ)) (c := c)
    (edgeCount := F.edgeCount) (vertexCount := F.vertexCount)
    (overlap := 0)
    (pieceEdges := fun i : Fin F.componentCount ↦
      (F.pieceShape F.connectedComponentDecomposition i).edgeCount)
    (pieceVertices := fun i : Fin F.componentCount ↦
      (F.pieceShape F.connectedComponentDecomposition i).vertexCount)
    (tripleCount := 1) (pieceTripleCount := fun _ ↦ 1)
    (by exact_mod_cast hn) hc
    (edgeCount_eq_sum_connectedComponent_edgeCount F)
    (by simpa using sum_connectedComponent_vertexCount_eq F)
    (by norm_num) (fun _ ↦ by norm_num) (by simp)
  simpa only [tripleBetaScale, pow_zero, one_mul] using h

/-- A multiplicative edge factor splits exactly across connected
components. -/
theorem edgeFactor_eq_prod_connectedComponents (q : ℝ)
    (F : FiniteGraphShape) :
    q ^ (2 * F.edgeCount) =
      ∏ i : Fin F.componentCount,
        q ^ (2 *
          (F.pieceShape F.connectedComponentDecomposition i).edgeCount) := by
  have hexponent :
      2 * F.edgeCount =
        ∑ i : Fin F.componentCount,
          2 * (F.pieceShape F.connectedComponentDecomposition i).edgeCount := by
    rw [edgeCount_eq_sum_connectedComponent_edgeCount F,
      Finset.mul_sum]
  rw [hexponent]
  exact (Finset.prod_pow_eq_pow_sum Finset.univ
    (fun i : Fin F.componentCount ↦
      2 * (F.pieceShape F.connectedComponentDecomposition i).edgeCount) q).symm

/-- The noised beta contribution assigned to one concrete tagged triple. -/
noncomputable def noisedTripleBetaScale (c : ℝ) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) (z : TaggedTriple plant) : ℝ :=
  (1 - (noise : ℝ)) ^ (2 * z.1.shape.edgeCount) *
    tripleBetaScale c n z.1.shape

theorem noisedTripleBetaScale_nonneg {c : ℝ} (hc : 0 < c)
    (noise : NoiseRate) (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) :
    0 ≤ noisedTripleBetaScale c noise plant z := by
  exact mul_nonneg
    (pow_nonneg (sub_nonneg.mpr noise.2.2.le) _)
    (tripleBetaScale_nonneg hc n z.1.shape)

/-- Reindexing a restricted component by its ambient support class preserves
its complete per-triple noised beta scale. -/
theorem noisedTripleBetaScale_componentTriple
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n))
    (z : TaggedTriple plant) (i : Fin z.1.shape.componentCount) :
    noisedTripleBetaScale c noise plant (componentTriple plant z i) =
      (1 - (noise : ℝ)) ^
          (2 * (z.1.shape.pieceShape
            z.1.shape.connectedComponentDecomposition i).edgeCount) *
        tripleBetaScale c n
          (z.1.shape.pieceShape
            z.1.shape.connectedComponentDecomposition i) := by
  unfold noisedTripleBetaScale componentTriple
  rw [pieceClass_shape_edgeCount]
  exact congrArg
    ((1 - (noise : ℝ)) ^
      (2 * (z.1.shape.pieceShape
        z.1.shape.connectedComponentDecomposition i).edgeCount) * ·)
    (tripleBetaScale_eq_of_iso
      (pieceShapeIso z.1 z.1.shape.connectedComponentDecomposition i)).symm

/-- Pointwise product bound for the concrete component tuple. -/
theorem noisedTripleBetaScale_le_prod_componentTriple
    (c : ℝ) (hc : 0 < c) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) (z : TaggedTriple plant) :
    noisedTripleBetaScale c noise plant z ≤
      ∏ i : Fin z.1.shape.componentCount,
        noisedTripleBetaScale c noise plant (componentTriple plant z i) := by
  let q : ℝ := 1 - (noise : ℝ)
  have hscale := tripleBetaScale_le_prod_connectedComponents
    c hc n (ambientSize_pos z.1) z.1.shape
  have hnoise : 0 ≤ q ^ (2 * z.1.shape.edgeCount) :=
    pow_nonneg (sub_nonneg.mpr noise.2.2.le) _
  calc
    noisedTripleBetaScale c noise plant z =
        q ^ (2 * z.1.shape.edgeCount) *
          tripleBetaScale c n z.1.shape := rfl
    _ ≤ q ^ (2 * z.1.shape.edgeCount) *
        ∏ i : Fin z.1.shape.componentCount,
          tripleBetaScale c n
            (z.1.shape.pieceShape
              z.1.shape.connectedComponentDecomposition i) :=
      mul_le_mul_of_nonneg_left hscale hnoise
    _ = (∏ i : Fin z.1.shape.componentCount,
          q ^ (2 * (z.1.shape.pieceShape
            z.1.shape.connectedComponentDecomposition i).edgeCount)) *
        (∏ i : Fin z.1.shape.componentCount,
          tripleBetaScale c n
            (z.1.shape.pieceShape
              z.1.shape.connectedComponentDecomposition i)) := by
      rw [edgeFactor_eq_prod_connectedComponents q z.1.shape]
    _ = ∏ i : Fin z.1.shape.componentCount,
        (q ^ (2 * (z.1.shape.pieceShape
            z.1.shape.connectedComponentDecomposition i).edgeCount) *
          tripleBetaScale c n
            (z.1.shape.pieceShape
              z.1.shape.connectedComponentDecomposition i)) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ i : Fin z.1.shape.componentCount,
        noisedTripleBetaScale c noise plant (componentTriple plant z i) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact (noisedTripleBetaScale_componentTriple c noise plant z i).symm

/-- The preceding bound in the list-indexed form required by
`ComponentEncoding`. -/
theorem noisedTripleBetaScale_le_prod_components
    (c : ℝ) (hc : 0 < c) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (z : (encoding plant).ActiveObject) :
    noisedTripleBetaScale c noise plant z.1 ≤
      ∏ i : Fin ((encoding plant).components z.1).length,
        noisedTripleBetaScale c noise plant
          (((encoding plant).components z.1).get i) := by
  change noisedTripleBetaScale c noise plant z.1 ≤
    ∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
      noisedTripleBetaScale c noise plant
        ((List.ofFn (componentTriple plant z.1)).get i)
  have hprod :
      (∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
        noisedTripleBetaScale c noise plant
          ((List.ofFn (componentTriple plant z.1)).get i)) =
        ∏ i : Fin z.1.1.shape.componentCount,
          noisedTripleBetaScale c noise plant
            (componentTriple plant z.1 i) := by
    refine Fintype.prod_equiv
      (Fin.castOrderIso (List.length_ofFn)).toEquiv _ _ ?_
    intro i
    simp only [List.get_ofFn]
    apply congrArg (fun j ↦ noisedTripleBetaScale c noise plant
      (componentTriple plant z.1 j))
    apply Fin.ext
    rfl
  rw [hprod]
  exact noisedTripleBetaScale_le_prod_componentTriple
    c hc noise plant z.1

/-! ### Exact recovery of the paper's masses -/

/-- Summing the constant per-triple scale over all tagged triples gives the
full noised graph-beta mass, with no duplicate class factor. -/
theorem sum_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (∑ z : TaggedTriple plant,
      noisedTripleBetaScale c noise plant z) =
      ∑ C : AmbientSupportClass n,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _hC
  simp only [noisedTripleBetaScale]
  rw [← Finset.mul_sum,
    sum_tripleBetaScale_eq_graphBetaWeight]

/-- The active-object sum of the concrete encoding is the same full noised
graph-beta mass. -/
theorem sum_active_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (∑ z : (encoding plant).ActiveObject,
      noisedTripleBetaScale c noise plant z.1) =
      ∑ C : AmbientSupportClass n,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  calc
    (∑ z : (encoding plant).ActiveObject,
        noisedTripleBetaScale c noise plant z.1) =
        ∑ z : TaggedTriple plant,
          noisedTripleBetaScale c noise plant z := by
      symm
      simpa [encoding] using
        (Finset.sum_subtype
          (Finset.univ : Finset (TaggedTriple plant))
          (by intro z; simp)
          (noisedTripleBetaScale c noise plant))
    _ = _ := sum_noisedTripleBetaScale_eq c noise plant

/-- The connected-object sum of the concrete encoding is exactly the
connected noised graph-beta mass. -/
theorem connectedMass_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (encoding plant).connectedMass
        (noisedTripleBetaScale c noise plant) =
      ∑ C : AmbientSupportClass n with C.shape.graph.Connected,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  unfold ComponentEncoding.connectedMass
  calc
    (∑ z : (encoding plant).ConnectedObject,
        noisedTripleBetaScale c noise plant z.1) =
        ∑ z : TaggedTriple plant with z.1.shape.graph.Connected,
          noisedTripleBetaScale c noise plant z := by
      symm
      simpa [encoding] using (Finset.sum_subtype
        ((Finset.univ : Finset (TaggedTriple plant)).filter
          fun z ↦ z.1.shape.graph.Connected)
        (by intro z; simp) (noisedTripleBetaScale c noise plant)
        )
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _hC
      by_cases hconnected : C.shape.graph.Connected
      · simp only [hconnected, if_true, noisedTripleBetaScale]
        rw [← Finset.mul_sum,
          sum_tripleBetaScale_eq_graphBetaWeight]
      · simp only [hconnected, if_false, Finset.sum_const_zero]

end GraphComponentExpansion

namespace BoundedTreewidthPlantModel

open GraphComponentExpansion

/-- The concrete per-triple scale sums exactly to `noisedBetaMass`. -/
theorem sum_noisedTripleBetaScale_eq_noisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    (∑ z : TaggedTriple (M.plant n),
      noisedTripleBetaScale M.backgroundDensity noise (M.plant n) z) =
      M.noisedBetaMass noise n := by
  simpa only [noisedBetaMass] using
    sum_noisedTripleBetaScale_eq
      M.backgroundDensity noise (M.plant n)

/-- The active-object sum in the graph component encoding is exactly
`noisedBetaMass`. -/
theorem sum_active_noisedTripleBetaScale_eq_noisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    (∑ z : (encoding (M.plant n)).ActiveObject,
      noisedTripleBetaScale M.backgroundDensity noise (M.plant n) z.1) =
      M.noisedBetaMass noise n := by
  simpa only [noisedBetaMass] using
    sum_active_noisedTripleBetaScale_eq
      M.backgroundDensity noise (M.plant n)

/-- The connected-object sum in the graph component encoding is exactly
`connectedNoisedBetaMass`. -/
theorem connectedMass_noisedTripleBetaScale_eq_connectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    (encoding (M.plant n)).connectedMass
        (noisedTripleBetaScale M.backgroundDensity noise (M.plant n)) =
      M.connectedNoisedBetaMass noise n := by
  unfold connectedNoisedBetaMass noisedBetaClassWeight
  rw [connectedMass_noisedTripleBetaScale_eq]
  apply Finset.sum_congr
  · ext C
    simp
  · intro C _hC
    rfl

/-- **Concrete geometric majorant in paper Lemma 4.4.**

The full noised beta mass is bounded by the nonempty geometric series in the
connected noised beta mass. -/
theorem noisedBetaMass_le_geometric_connectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ)
    (hmass : M.connectedNoisedBetaMass noise n < 1) :
    M.noisedBetaMass noise n ≤
      M.connectedNoisedBetaMass noise n /
        (1 - M.connectedNoisedBetaMass noise n) := by
  let E := encoding (M.plant n)
  let weight : TaggedTriple (M.plant n) → ℝ :=
    noisedTripleBetaScale M.backgroundDensity noise (M.plant n)
  have hmass' : E.connectedMass weight < 1 := by
    change (encoding (M.plant n)).connectedMass
        (noisedTripleBetaScale M.backgroundDensity noise (M.plant n)) < 1
    rw [M.connectedMass_noisedTripleBetaScale_eq_connectedNoisedBetaMass]
    exact hmass
  have hmajor := E.sum_active_le_geometric_connectedMass
    weight
    (fun z ↦ noisedTripleBetaScale_nonneg
      M.backgroundDensity_pos noise (M.plant n) z)
    (fun z ↦ noisedTripleBetaScale_le_prod_components
      M.backgroundDensity M.backgroundDensity_pos noise (M.plant n) z)
    hmass'
  change
    (∑ z : (encoding (M.plant n)).ActiveObject,
      noisedTripleBetaScale M.backgroundDensity noise (M.plant n) z.1) ≤
      (encoding (M.plant n)).connectedMass
          (noisedTripleBetaScale M.backgroundDensity noise (M.plant n)) /
        (1 - (encoding (M.plant n)).connectedMass
          (noisedTripleBetaScale M.backgroundDensity noise (M.plant n)))
      at hmajor
  rw [M.sum_active_noisedTripleBetaScale_eq_noisedBetaMass,
    M.connectedMass_noisedTripleBetaScale_eq_connectedNoisedBetaMass] at hmajor
  exact hmajor

/-- **Paper Lemma 4.4, specialized to the actual graph masses.**

The printed low-degree premise is retained, though—as in the paper's
component argument—it is not otherwise consumed.  Vanishing connected
noised beta mass implies vanishing full noised beta mass. -/
theorem noisedBetaMass_vanishes_of_connectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate)
    (hconnected : Vanishes (M.connectedNoisedBetaMass noise)) :
    Vanishes (M.noisedBetaMass noise) := by
  let C := fun n ↦ encoding (M.plant n)
  let weight := fun n ↦
    noisedTripleBetaScale M.backgroundDensity noise (M.plant n)
  have hconnected' :
      Vanishes fun n ↦ (C n).connectedMass (weight n) := by
    have heq :
        (fun n ↦ (C n).connectedMass (weight n)) =
          M.connectedNoisedBetaMass noise := by
      funext n
      exact M.connectedMass_noisedTripleBetaScale_eq_connectedNoisedBetaMass
        noise n
    rw [heq]
    exact hconnected
  have hexpansion := clusterExpansion_vanishes
    C weight M.lowDegreeNormSq hlow
    (fun n z ↦ noisedTripleBetaScale_nonneg
      M.backgroundDensity_pos noise (M.plant n) z)
    (fun n z ↦ noisedTripleBetaScale_le_prod_components
      M.backgroundDensity M.backgroundDensity_pos noise (M.plant n) z)
    hconnected'
  have htotal :
      (fun n ↦ ∑ z : (C n).ActiveObject, weight n z.1) =
        M.noisedBetaMass noise := by
    funext n
    exact M.sum_active_noisedTripleBetaScale_eq_noisedBetaMass noise n
  rw [htotal] at hexpansion
  exact hexpansion

end BoundedTreewidthPlantModel

end

end LowDegree
