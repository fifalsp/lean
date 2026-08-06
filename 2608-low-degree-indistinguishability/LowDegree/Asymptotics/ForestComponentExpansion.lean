import LowDegree.Asymptotics.ForestBetaMass
import LowDegree.Combinatorics.GraphComponentExpansion

/-!
# Connected-component expansion restricted to forests

This is the acyclic specialization of the graph component encoding.  Since
acyclicity is inherited by connected components, the component restriction
of an acyclic tagged triple remains in the restricted type.  The resulting
geometric expansion bounds `forestNoisedBetaMass` by the corresponding mass
of connected acyclic classes.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph
open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

open TreeDecomposition
open AggregateGraphRestriction
open GraphComponentExpansion

namespace ForestComponentExpansion

variable {n : ℕ}

/-- Tagged triples whose parent support shape is acyclic. -/
abbrev ForestTaggedTriple (plant : SimpleGraph (Fin n)) :=
  {z : TaggedTriple plant // z.1.shape.graph.IsAcyclic}

/-- A connected-component piece of an acyclic shape is acyclic after
isolated vertices are stripped. -/
theorem pieceShape_isAcyclic_of_isAcyclic (F : FiniteGraphShape)
    (hF : F.graph.IsAcyclic) (i : Fin F.componentCount) :
    (F.pieceShape F.connectedComponentDecomposition i).graph.IsAcyclic := by
  have hpiece :
      (F.connectedComponentDecomposition.piece i).IsAcyclic :=
    hF.anti (F.connectedComponentDecomposition.piece_le i)
  exact hpiece.induce _

/-- The base component restriction of a forest-tagged triple remains
acyclic. -/
theorem componentTriple_isAcyclic (plant : SimpleGraph (Fin n))
    (z : ForestTaggedTriple plant) (i : Fin z.1.1.shape.componentCount) :
    (componentTriple plant z.1 i).1.shape.graph.IsAcyclic := by
  exact
    (pieceShapeIso z.1.1 z.1.1.shape.connectedComponentDecomposition i).isAcyclic_iff.mp
      (pieceShape_isAcyclic_of_isAcyclic z.1.1.shape z.2 i)

/-- The `i`th component as a forest-tagged triple. -/
noncomputable def componentTriple (plant : SimpleGraph (Fin n))
    (z : ForestTaggedTriple plant) (i : Fin z.1.1.shape.componentCount) :
    ForestTaggedTriple plant :=
  ⟨GraphComponentExpansion.componentTriple plant z.1 i,
    componentTriple_isAcyclic plant z i⟩

/-- Ordered connected-component restrictions inside the acyclic subtype. -/
noncomputable def componentTriples (plant : SimpleGraph (Fin n))
    (z : ForestTaggedTriple plant) : List (ForestTaggedTriple plant) :=
  List.ofFn (componentTriple plant z)

@[simp]
theorem componentTriples_length (plant : SimpleGraph (Fin n))
    (z : ForestTaggedTriple plant) :
    (componentTriples plant z).length = z.1.1.shape.componentCount := by
  simp [componentTriples]

/-- Restricting the already-injective base component list to acyclic tagged
triples preserves injectivity, including recovery of the tuple length. -/
theorem componentTriples_injective (plant : SimpleGraph (Fin n)) :
    Function.Injective (componentTriples plant) := by
  intro left right hcomponents
  apply Subtype.ext
  apply GraphComponentExpansion.componentTriples_injective plant
  have hmap := congrArg
    (List.map fun z : ForestTaggedTriple plant ↦ z.1) hcomponents
  simpa only [componentTriples, componentTriple,
    GraphComponentExpansion.componentTriples, List.map_ofFn,
    Function.comp_apply] using hmap

/-- The component encoding restricted to acyclic parent shapes. -/
noncomputable def encoding (plant : SimpleGraph (Fin n)) :
    ComponentEncoding (ForestTaggedTriple plant) where
  active := fun _ ↦ True
  connected := fun z ↦ z.1.1.shape.graph.Connected
  components := componentTriples plant
  components_nonempty := by
    rintro ⟨z, hz⟩
    rw [List.ne_nil_iff_length_pos, componentTriples_length]
    exact GraphComponentExpansion.componentCount_pos_of_edgeCount_pos z.1.1.shape
      (GraphComponentExpansion.ambientSupportClass_edgeCount_pos z.1.1)
  component_connected := by
    rintro ⟨z, hz⟩ b hb
    rw [componentTriples, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩
    exact GraphComponentExpansion.componentTriple_connected plant z.1 i
  components_injective := by
    intro left _hleft right _hright hcomponents
    exact componentTriples_injective plant hcomponents

/-- Restriction to forest-tagged triples does not alter the per-triple
weight. -/
noncomputable def noisedTripleBetaScale (c : ℝ) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n)) (z : ForestTaggedTriple plant) : ℝ :=
  GraphComponentExpansion.noisedTripleBetaScale c noise plant z.1

theorem noisedTripleBetaScale_nonneg {c : ℝ} (hc : 0 < c)
    (noise : NoiseRate) (plant : SimpleGraph (Fin n))
    (z : ForestTaggedTriple plant) :
    0 ≤ noisedTripleBetaScale c noise plant z :=
  GraphComponentExpansion.noisedTripleBetaScale_nonneg hc noise plant z.1

/-- The forest component list satisfies the same pointwise product bound. -/
theorem noisedTripleBetaScale_le_prod_components
    (c : ℝ) (hc : 0 < c) (noise : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (z : (encoding plant).ActiveObject) :
    noisedTripleBetaScale c noise plant z.1 ≤
      ∏ i : Fin ((encoding plant).components z.1).length,
        noisedTripleBetaScale c noise plant
          (((encoding plant).components z.1).get i) := by
  change GraphComponentExpansion.noisedTripleBetaScale c noise plant z.1.1 ≤
    ∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
      GraphComponentExpansion.noisedTripleBetaScale c noise plant
        ((List.ofFn (componentTriple plant z.1)).get i).1
  have hprod :
      (∏ i : Fin (List.ofFn (componentTriple plant z.1)).length,
        GraphComponentExpansion.noisedTripleBetaScale c noise plant
          ((List.ofFn (componentTriple plant z.1)).get i).1) =
        ∏ i : Fin z.1.1.1.shape.componentCount,
          GraphComponentExpansion.noisedTripleBetaScale c noise plant
            (GraphComponentExpansion.componentTriple plant z.1.1 i) := by
    refine Fintype.prod_equiv
      (Fin.castOrderIso (List.length_ofFn)).toEquiv _ _ ?_
    intro i
    simp only [List.get_ofFn, componentTriple]
    apply congrArg (fun j ↦
      GraphComponentExpansion.noisedTripleBetaScale c noise plant
        (GraphComponentExpansion.componentTriple plant z.1.1 j))
    apply Fin.ext
    rfl
  rw [hprod]
  exact GraphComponentExpansion.noisedTripleBetaScale_le_prod_componentTriple
    c hc noise plant z.1.1

/-! ### Exact forest and connected-forest masses -/

/-- Summing over forest-tagged triples gives exactly the noised beta mass
restricted to acyclic ambient support classes. -/
theorem sum_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (∑ z : ForestTaggedTriple plant,
      noisedTripleBetaScale c noise plant z) =
      ∑ C : AmbientSupportClass n with C.shape.graph.IsAcyclic,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  calc
    (∑ z : ForestTaggedTriple plant,
        noisedTripleBetaScale c noise plant z) =
        ∑ z : TaggedTriple plant with z.1.shape.graph.IsAcyclic,
          GraphComponentExpansion.noisedTripleBetaScale c noise plant z := by
      symm
      exact Finset.sum_subtype
        (p := fun z : TaggedTriple plant ↦ z.1.shape.graph.IsAcyclic)
        ((Finset.univ : Finset (TaggedTriple plant)).filter
          fun z ↦ z.1.shape.graph.IsAcyclic)
        (by intro z; simp)
        (GraphComponentExpansion.noisedTripleBetaScale c noise plant)
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _hC
      by_cases hacyclic : C.shape.graph.IsAcyclic
      · simp only [hacyclic, if_true,
          GraphComponentExpansion.noisedTripleBetaScale]
        rw [← Finset.mul_sum,
          sum_tripleBetaScale_eq_graphBetaWeight]
      · simp only [hacyclic, if_false, Finset.sum_const_zero]

/-- The active-object sum of the forest encoding is the same forest beta
mass. -/
theorem sum_active_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (∑ z : (encoding plant).ActiveObject,
      noisedTripleBetaScale c noise plant z.1) =
      ∑ C : AmbientSupportClass n with C.shape.graph.IsAcyclic,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  calc
    (∑ z : (encoding plant).ActiveObject,
        noisedTripleBetaScale c noise plant z.1) =
        ∑ z : ForestTaggedTriple plant,
          noisedTripleBetaScale c noise plant z := by
      symm
      simpa [encoding] using
        (Finset.sum_subtype
          (Finset.univ : Finset (ForestTaggedTriple plant))
          (by intro z; simp)
          (noisedTripleBetaScale c noise plant))
    _ = _ := sum_noisedTripleBetaScale_eq c noise plant

/-- The connected mass of the forest encoding is exactly the noised beta
mass over connected acyclic classes. -/
theorem connectedMass_noisedTripleBetaScale_eq
    (c : ℝ) (noise : NoiseRate) (plant : SimpleGraph (Fin n)) :
    (encoding plant).connectedMass
        (noisedTripleBetaScale c noise plant) =
      ∑ C : AmbientSupportClass n with
          C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic,
        (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
          C.shape.graphBetaWeight c n plant := by
  unfold ComponentEncoding.connectedMass
  calc
    (∑ z : (encoding plant).ConnectedObject,
        noisedTripleBetaScale c noise plant z.1) =
        ∑ z : ForestTaggedTriple plant with
          z.1.1.shape.graph.Connected,
          noisedTripleBetaScale c noise plant z := by
      symm
      simpa [encoding] using (Finset.sum_subtype
        ((Finset.univ : Finset (ForestTaggedTriple plant)).filter
          fun z ↦ z.1.1.shape.graph.Connected)
        (by intro z; simp) (noisedTripleBetaScale c noise plant))
    _ = ∑ z : ForestTaggedTriple plant,
        if z.1.1.shape.graph.Connected then
          noisedTripleBetaScale c noise plant z else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ z : TaggedTriple plant with z.1.shape.graph.IsAcyclic,
        if z.1.shape.graph.Connected then
          GraphComponentExpansion.noisedTripleBetaScale c noise plant z
        else 0 := by
      symm
      exact Finset.sum_subtype
        (p := fun z : TaggedTriple plant ↦ z.1.shape.graph.IsAcyclic)
        ((Finset.univ : Finset (TaggedTriple plant)).filter
          fun z ↦ z.1.shape.graph.IsAcyclic)
        (by intro z; simp)
        (fun z ↦ if z.1.shape.graph.Connected then
          GraphComponentExpansion.noisedTripleBetaScale c noise plant z
        else 0)
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _hC
      by_cases hconnected : C.shape.graph.Connected
      · by_cases hacyclic : C.shape.graph.IsAcyclic
        · simp only [hconnected, hacyclic, and_self, if_true,
            GraphComponentExpansion.noisedTripleBetaScale]
          rw [← Finset.mul_sum,
            sum_tripleBetaScale_eq_graphBetaWeight]
        · simp only [hconnected, hacyclic, and_false, if_false,
            Finset.sum_const_zero]
      · by_cases hacyclic : C.shape.graph.IsAcyclic <;>
          simp [hconnected, hacyclic]

end ForestComponentExpansion

namespace BoundedTreewidthPlantModel

open ForestComponentExpansion

/-- Connected-and-acyclic contribution to the noised leading beta mass. -/
noncomputable def connectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic,
    (1 - (noise : ℝ)) ^ (2 * C.shape.edgeCount) *
      C.shape.graphBetaWeight M.backgroundDensity n (M.plant n)

/-- The active forest-triple sum is exactly `forestNoisedBetaMass`. -/
theorem sum_active_forestTripleBetaScale_eq_forestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    (∑ z : (ForestComponentExpansion.encoding (M.plant n)).ActiveObject,
      ForestComponentExpansion.noisedTripleBetaScale
        M.backgroundDensity noise (M.plant n) z.1) =
      M.forestNoisedBetaMass noise n := by
  unfold forestNoisedBetaMass
  rw [ForestComponentExpansion.sum_active_noisedTripleBetaScale_eq]

/-- The connected mass of the forest encoding is exactly
`connectedForestNoisedBetaMass`. -/
theorem connectedMass_forestTripleBetaScale_eq_connectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ) :
    (ForestComponentExpansion.encoding (M.plant n)).connectedMass
        (ForestComponentExpansion.noisedTripleBetaScale
          M.backgroundDensity noise (M.plant n)) =
      M.connectedForestNoisedBetaMass noise n := by
  unfold connectedForestNoisedBetaMass
  rw [ForestComponentExpansion.connectedMass_noisedTripleBetaScale_eq]

/-- Forest analogue of the concrete geometric majorant in Lemma 4.4. -/
theorem forestNoisedBetaMass_le_geometric_connectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) (n : ℕ)
    (hmass : M.connectedForestNoisedBetaMass noise n < 1) :
    M.forestNoisedBetaMass noise n ≤
      M.connectedForestNoisedBetaMass noise n /
        (1 - M.connectedForestNoisedBetaMass noise n) := by
  let E := ForestComponentExpansion.encoding (M.plant n)
  let weight : ForestTaggedTriple (M.plant n) → ℝ :=
    ForestComponentExpansion.noisedTripleBetaScale
      M.backgroundDensity noise (M.plant n)
  have hmass' : E.connectedMass weight < 1 := by
    change (ForestComponentExpansion.encoding (M.plant n)).connectedMass
      (ForestComponentExpansion.noisedTripleBetaScale
        M.backgroundDensity noise (M.plant n)) < 1
    rw [M.connectedMass_forestTripleBetaScale_eq_connectedForestNoisedBetaMass]
    exact hmass
  have hmajor := E.sum_active_le_geometric_connectedMass
    weight
    (fun z ↦ ForestComponentExpansion.noisedTripleBetaScale_nonneg
      M.backgroundDensity_pos noise (M.plant n) z)
    (fun z ↦ ForestComponentExpansion.noisedTripleBetaScale_le_prod_components
      M.backgroundDensity M.backgroundDensity_pos noise (M.plant n) z)
    hmass'
  change
    (∑ z : (ForestComponentExpansion.encoding (M.plant n)).ActiveObject,
      ForestComponentExpansion.noisedTripleBetaScale
        M.backgroundDensity noise (M.plant n) z.1) ≤
      (ForestComponentExpansion.encoding (M.plant n)).connectedMass
          (ForestComponentExpansion.noisedTripleBetaScale
            M.backgroundDensity noise (M.plant n)) /
        (1 - (ForestComponentExpansion.encoding (M.plant n)).connectedMass
          (ForestComponentExpansion.noisedTripleBetaScale
            M.backgroundDensity noise (M.plant n))) at hmajor
  rw [M.sum_active_forestTripleBetaScale_eq_forestNoisedBetaMass,
    M.connectedMass_forestTripleBetaScale_eq_connectedForestNoisedBetaMass]
    at hmajor
  exact hmajor

/-- Vanishing of the connected acyclic beta mass implies vanishing of the
full forest beta mass.  The low-degree premise is retained for the same
paper-facing quantifier structure as Lemma 4.4. -/
theorem forestNoisedBetaMass_vanishes_of_connectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq)
    (noise : NoiseRate)
    (hconnected : Vanishes (M.connectedForestNoisedBetaMass noise)) :
    Vanishes (M.forestNoisedBetaMass noise) := by
  let C := fun n ↦ ForestComponentExpansion.encoding (M.plant n)
  let weight := fun n ↦ ForestComponentExpansion.noisedTripleBetaScale
    M.backgroundDensity noise (M.plant n)
  have hconnected' :
      Vanishes fun n ↦ (C n).connectedMass (weight n) := by
    have heq :
        (fun n ↦ (C n).connectedMass (weight n)) =
          M.connectedForestNoisedBetaMass noise := by
      funext n
      exact
        M.connectedMass_forestTripleBetaScale_eq_connectedForestNoisedBetaMass
          noise n
    rw [heq]
    exact hconnected
  have hexpansion := clusterExpansion_vanishes
    C weight M.lowDegreeNormSq hlow
    (fun n z ↦ ForestComponentExpansion.noisedTripleBetaScale_nonneg
      M.backgroundDensity_pos noise (M.plant n) z)
    (fun n z ↦ ForestComponentExpansion.noisedTripleBetaScale_le_prod_components
      M.backgroundDensity M.backgroundDensity_pos noise (M.plant n) z)
    hconnected'
  have htotal :
      (fun n ↦ ∑ z : (C n).ActiveObject, weight n z.1) =
        M.forestNoisedBetaMass noise := by
    funext n
    exact M.sum_active_forestTripleBetaScale_eq_forestNoisedBetaMass noise n
  rw [htotal] at hexpansion
  exact hexpansion

end BoundedTreewidthPlantModel

end

end LowDegree
