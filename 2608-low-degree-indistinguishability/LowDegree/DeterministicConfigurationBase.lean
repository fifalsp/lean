import LowDegree.SupercriticalStatistical
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Deterministic supercritical plant certificates

This module records the paper-facing interface for the deterministic graph
sequence constructed in the current Appendix.  The configuration-model
construction and its probabilistic estimates are deliberately kept in
separate downstream modules.

The manuscript writes the local-sparsity estimate with the denominator
`log n` for every `n ≥ 1`.  Since that expression is undefined at `n = 1`,
the exact formal interface includes the harmless guard `2 ≤ n`.  All uses of
the estimate are asymptotic and therefore lie in this range.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Number of edges in the subgraph induced by a finite vertex set. -/
noncomputable def deterministicInducedEdgeCount
    {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (G.induce (U : Set V)).edgeFinset.card

/-- A real-valued lower bound on girth, with the paper's convention that an
acyclic graph has infinite girth.  Stating the property directly for every
cycle avoids Mathlib's natural-valued `SimpleGraph.girth`, whose value on an
acyclic graph is the junk value zero. -/
def HasRealGirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℝ) : Prop :=
  ∀ v (w : G.Walk v v), w.IsCycle → g ≤ (w.length : ℝ)

/-! ## Exact transport along an injective vertex map -/

/-- The vertices of `G.map f` adjacent to an image vertex are exactly the
images of the corresponding vertices adjacent in `G`. -/
noncomputable def mapNeighborSetEquiv
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    G.neighborSet v ≃ (G.map f).neighborSet (f v) := by
  let e := (SimpleGraph.Embedding.map f G).mapNeighborSet v
  refine Equiv.ofBijective e ⟨e.injective, ?_⟩
  rintro ⟨w, hw⟩
  change (G.map f).Adj (f v) w at hw
  rw [SimpleGraph.map_adj] at hw
  rcases hw with ⟨a, b, hab, ha, hb⟩
  have hav : a = v := f.injective ha
  subst a
  refine ⟨⟨b, hab⟩, ?_⟩
  apply Subtype.ext
  exact hb

/-- Mapping a finite graph along an injection preserves the degree of every
source vertex. -/
@[simp] theorem degree_map_apply
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    (G.map f).degree (f v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (mapNeighborSetEquiv f G v).symm

/-- A degree can be read without retaining any particular decidable-adjacency
instance.  This bridge is useful when a mapped graph has two propositionally
equal finite-set instances. -/
theorem degree_eq_ncard_neighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    G.degree v = (G.neighborSet v).ncard := by
  unfold SimpleGraph.degree SimpleGraph.neighborFinset
  exact (Set.ncard_eq_toFinset_card' _).symm

/-- A maximum-degree bound survives injective padding; every vertex outside
the range of the embedding is isolated. -/
theorem degree_map_le
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (w : W) :
    (G.map f).degree w ≤ D := by
  classical
  by_cases hw : w ∈ Set.range f
  · rcases hw with ⟨v, rfl⟩
    simpa using hD v
  · have hws : w ∉ (G.map f).support := by
      rw [SimpleGraph.support_map]
      rintro ⟨v, -, rfl⟩
      exact hw ⟨v, rfl⟩
    rw [((G.map f).degree_eq_zero_iff_notMem_support w).mpr hws]
    exact Nat.zero_le D

/-- Mapping a finite graph along an injection preserves the number of support
vertices. -/
@[simp] theorem ncard_support_map
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).support.ncard = G.support.ncard := by
  rw [SimpleGraph.support_map, Set.ncard_image_of_injective _ f.injective]

/-- The finite preimage of `U` under an embedding. -/
noncomputable def embeddingPreimageFinset
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (U : Finset W) : Finset V :=
  Finset.univ.filter fun v ↦ f v ∈ U

@[simp] theorem mem_embeddingPreimageFinset
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (U : Finset W) (v : V) :
    v ∈ embeddingPreimageFinset f U ↔ f v ∈ U := by
  simp [embeddingPreimageFinset]

/-- The embedding from the preimage of `U` into `U`. -/
noncomputable def embeddingPreimageSubtype
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (U : Finset W) :
    {v // v ∈ embeddingPreimageFinset f U} ↪ {w // w ∈ U} where
  toFun v := ⟨f v, (mem_embeddingPreimageFinset f U v).mp v.property⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val hab)

/-- Inducing a mapped graph on `U` is the mapped induced graph on the finite
preimage of `U`; vertices of `U` outside the range are simply isolated. -/
theorem induce_map_eq_map_induce_preimage
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph V) (U : Finset W) :
    (G.map f).induce (U : Set W) =
      (G.induce (embeddingPreimageFinset f U : Set V)).map
        (embeddingPreimageSubtype f U) := by
  ext x y
  constructor
  · intro hxy
    rw [SimpleGraph.comap_adj, SimpleGraph.map_adj] at hxy
    rcases hxy with ⟨a, b, hab, ha, hb⟩
    let a' : {v // v ∈ embeddingPreimageFinset f U} :=
      ⟨a, (mem_embeddingPreimageFinset f U a).mpr (by
        rw [ha]
        exact x.property)⟩
    let b' : {v // v ∈ embeddingPreimageFinset f U} :=
      ⟨b, (mem_embeddingPreimageFinset f U b).mpr (by
        rw [hb]
        exact y.property)⟩
    refine ⟨a', b', hab, ?_, ?_⟩
    · apply Subtype.ext
      exact ha
    · apply Subtype.ext
      exact hb
  · rintro ⟨a, b, hab, ha, hb⟩
    rw [SimpleGraph.comap_adj, SimpleGraph.map_adj]
    refine ⟨a, b, hab, ?_, ?_⟩
    · exact congrArg Subtype.val ha
    · exact congrArg Subtype.val hb

/-- Pulling back a finite set along an injection cannot increase its
cardinality. -/
theorem card_embeddingPreimageFinset_le
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (U : Finset W) :
    (embeddingPreimageFinset f U).card ≤ U.card := by
  classical
  let e : {v // v ∈ embeddingPreimageFinset f U} ↪ {w // w ∈ U} :=
    embeddingPreimageSubtype f U
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e e.injective

/-- The four deterministic properties in the current Appendix construction
lemma.  The graph at index `n` is genuinely carried by `Fin mₙ`, rather than
being silently padded by isolated ambient vertices. -/
structure DeterministicPlantWitness (D : ℕ) (r gamma : ℝ) where
  A : ℝ
  kappa : ℝ
  A_pos : 0 < A
  kappa_pos : 0 < kappa
  graph : (n : ℕ) → SimpleGraph (Fin (appendixPlantSize r n))
  maxDegree : ∀ n v, (graph n).degree v ≤ D
  localSparsity : ∀ n, 2 ≤ n →
    ∀ U : Finset (Fin (appendixPlantSize r n)),
      2 ≤ U.card →
      (U.card : ℝ) ≤ (appendixPlantSize r n : ℝ) ^ gamma →
      (deterministicInducedEdgeCount (graph n) U : ℝ) ≤
        (1 + A / Real.log (n : ℝ)) * (U.card : ℝ)
  girth : ∀ n,
    HasRealGirthAtLeast (graph n) (kappa * Real.log (n : ℝ))
  edgeDensity : Tendsto
    (fun n ↦ ((graph n).edgeFinset.card : ℝ) /
      (appendixPlantSize r n : ℝ))
    atTop (nhds ((D : ℝ) / 2))

namespace DeterministicPlantWitness

/-- The canonical inclusion of the `mₙ` plant vertices into `[n]`.  Naming
this embedding keeps all downstream transport statements definitionally
aligned. -/
def ambientEmbedding
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    Fin (appendixPlantSize r n) ↪ Fin n :=
  Fin.castLEEmb (appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)

/-- Pad the `mₙ`-vertex deterministic graph by isolated vertices in the
ambient `n`-vertex graph. -/
noncomputable def ambientGraph
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    SimpleGraph (Fin n) :=
  (W.graph n).map (ambientEmbedding hr n)

/-- Padding the deterministic plant by isolated vertices preserves its exact
edge count. -/
@[simp] theorem ambientGraph_edgeFinset_card
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).edgeFinset.card = (W.graph n).edgeFinset.card := by
  classical
  unfold ambientGraph
  rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card',
    SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ (ambientEmbedding hr n).sym2Map.injective]

/-- Padding preserves the number of non-isolated vertices. -/
@[simp] theorem ambientGraph_support_ncard
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).support.ncard = (W.graph n).support.ncard := by
  unfold ambientGraph
  exact ncard_support_map (ambientEmbedding hr n) (W.graph n)

/-- In particular, the ambient plant uses at most `mₙ` vertices. -/
theorem ambientGraph_support_ncard_le
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).support.ncard ≤ appendixPlantSize r n := by
  rw [ambientGraph_support_ncard]
  simpa using (W.graph n).support.ncard_le_card

/-- The paper's maximum-degree bound is unchanged after placing the plant on
the first `mₙ` ambient vertices. -/
theorem ambientGraph_maxDegree
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) (v : Fin n) :
    (W.ambientGraph hr n).degree v ≤ D := by
  classical
  rw [degree_eq_ncard_neighborSet]
  let f := ambientEmbedding hr n
  by_cases hv : v ∈ Set.range f
  · rcases hv with ⟨u, rfl⟩
    calc
      ((W.ambientGraph hr n).neighborSet (f u)).ncard =
          ((W.graph n).neighborSet u).ncard := by
        unfold ambientGraph
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact Nat.card_congr (mapNeighborSetEquiv f (W.graph n) u).symm
      _ = (W.graph n).degree u := (degree_eq_ncard_neighborSet _ _).symm
      _ ≤ D := W.maxDegree n u
  · have hempty : (W.ambientGraph hr n).neighborSet v = ∅ := by
      ext w
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hvw
      change ((W.graph n).map f).Adj v w at hvw
      rcases (SimpleGraph.map_adj f (W.graph n) v w).mp hvw with
        ⟨u, -, -, hu, -⟩
      exact hv ⟨u, hu⟩
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le D

/-- The edge-density limit is literally unchanged by padding. -/
theorem ambientGraph_edgeDensity
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    Tendsto
      (fun n ↦ ((W.ambientGraph hr n).edgeFinset.card : ℝ) /
        (appendixPlantSize r n : ℝ))
      atTop (nhds ((D : ℝ) / 2)) := by
  simpa only [ambientGraph_edgeFinset_card] using W.edgeDensity

end DeterministicPlantWitness

end

end LowDegree
