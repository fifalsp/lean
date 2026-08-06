import LowDegree.DeterministicConnectedCount
import LowDegree.DeterministicConfigurationBase
import LowDegree.SupercriticalShapeRestrictions

/-!
# Adapters for deterministic appendix witnesses

This module transports the graph sequence supplied by
`DeterministicPlantWitness` from its natural vertex set `Fin mₙ` to the
ambient vertex set `Fin n`.  It also converts occurrence of an abstract
support shape in the padded graph back to an honest copy in the source
graph.  The latter is the bridge needed to apply the witness's local
sparsity and girth hypotheses.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

/-! ## Pulling graph copies through an injective map -/

namespace FiniteGraphShape

/-- Every vertex of a support-stripped graph copy in `G.map f` lies in the
range of `f`. -/
theorem mappedCopy_vertex_mem_range
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (G : SimpleGraph (Fin m))
    (copy : SimpleGraph.Copy F.graph (G.map f)) (v : F.Vertex) :
    copy v ∈ Set.range f := by
  have hvSupport : v ∈ F.graph.support := by
    rw [F.support_eq_univ]
    exact Set.mem_univ v
  rw [SimpleGraph.mem_support] at hvSupport
  rcases hvSupport with ⟨w, hvw⟩
  have hmap := copy.toHom.map_rel' hvw
  rw [SimpleGraph.map_adj] at hmap
  rcases hmap with ⟨u, _u', _huu', hu, _hu'⟩
  exact ⟨u, hu⟩

/-- The source vertex underlying a vertex of a copy in an injectively mapped
graph. -/
noncomputable def mappedCopySourceVertex
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (G : SimpleGraph (Fin m))
    (copy : SimpleGraph.Copy F.graph (G.map f)) (v : F.Vertex) : Fin m :=
  Classical.choose (F.mappedCopy_vertex_mem_range f G copy v)

@[simp] theorem map_mappedCopySourceVertex
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (G : SimpleGraph (Fin m))
    (copy : SimpleGraph.Copy F.graph (G.map f)) (v : F.Vertex) :
    f (F.mappedCopySourceVertex f G copy v) = copy v :=
  Classical.choose_spec (F.mappedCopy_vertex_mem_range f G copy v)

/-- A copy in an injectively mapped graph pulls back to a copy in the source
graph.  This is valid because finite graph shapes have no isolated vertices,
so every copied vertex is forced to lie in the range of the injection. -/
noncomputable def pullbackMappedCopy
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (G : SimpleGraph (Fin m))
    (copy : SimpleGraph.Copy F.graph (G.map f)) :
    SimpleGraph.Copy F.graph G where
  toHom :=
    { toFun := F.mappedCopySourceVertex f G copy
      map_rel' := by
        intro u v huv
        have hmap : (G.map f).Adj (copy u) (copy v) :=
          copy.toHom.map_rel' huv
        rw [SimpleGraph.map_adj] at hmap
        rcases hmap with ⟨a, b, hab, ha, hb⟩
        have hau : a = F.mappedCopySourceVertex f G copy u := by
          apply f.injective
          rw [ha, F.map_mappedCopySourceVertex f G copy u]
        have hbv : b = F.mappedCopySourceVertex f G copy v := by
          apply f.injective
          rw [hb, F.map_mappedCopySourceVertex f G copy v]
        simpa only [hau, hbv] using hab }
  injective' := by
    intro u v huv
    change F.mappedCopySourceVertex f G copy u =
      F.mappedCopySourceVertex f G copy v at huv
    apply copy.injective
    change copy u = copy v
    rw [← F.map_mappedCopySourceVertex f G copy u,
      ← F.map_mappedCopySourceVertex f G copy v]
    exact congrArg f huv

@[simp] theorem map_pullbackMappedCopy_apply
    {m n : ℕ} (F : FiniteGraphShape) (f : Fin m ↪ Fin n)
    (G : SimpleGraph (Fin m))
    (copy : SimpleGraph.Copy F.graph (G.map f)) (v : F.Vertex) :
    f (F.pullbackMappedCopy f G copy v) = copy v :=
  F.map_mappedCopySourceVertex f G copy v

end FiniteGraphShape

/-! ## Labelled-copy vertex sets and induced edge counts -/

namespace FiniteGraphShape

/-- The vertices occupied by a labelled copy. -/
noncomputable def labelledCopyVertexFinset
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    {G : SimpleGraph V} (copy : SimpleGraph.Copy F.graph G) : Finset V :=
  Finset.univ.map copy.toEmbedding

@[simp] theorem card_labelledCopyVertexFinset
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    {G : SimpleGraph V} (copy : SimpleGraph.Copy F.graph G) :
    (F.labelledCopyVertexFinset copy).card = F.vertexCount := by
  unfold labelledCopyVertexFinset vertexCount
  rw [Finset.card_map, Finset.card_univ]

/-- A labelled copy remains a copy after restricting the target graph to
the vertices that it occupies. -/
noncomputable def copyIntoInduce
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    {G : SimpleGraph V} (copy : SimpleGraph.Copy F.graph G) :
    SimpleGraph.Copy F.graph
      (G.induce (F.labelledCopyVertexFinset copy : Set V)) where
  toHom :=
    { toFun := fun v ↦ ⟨copy v, by
          change copy v ∈ F.labelledCopyVertexFinset copy
          rw [labelledCopyVertexFinset, Finset.mem_map]
          exact ⟨v, Finset.mem_univ v, rfl⟩⟩
      map_rel' := by
        intro u v huv
        change G.Adj (copy u) (copy v)
        exact copy.toHom.map_rel' huv }
  injective' := by
    intro u v huv
    apply copy.injective
    exact congrArg Subtype.val huv

/-- The induced graph on the occupied vertices contains all abstract copy
edges. -/
theorem edgeCount_le_inducedEdgeCount
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    {G : SimpleGraph V} (copy : SimpleGraph.Copy F.graph G) :
    F.edgeCount ≤ deterministicInducedEdgeCount G
      (F.labelledCopyVertexFinset copy) := by
  let inducedCopy := F.copyIntoInduce copy
  calc
    F.edgeCount = Fintype.card F.graph.edgeSet := by
      rw [F.edgeCount_eq_ncard, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card]
    _ ≤ Fintype.card
        (G.induce (F.labelledCopyVertexFinset copy : Set V)).edgeSet :=
      Fintype.card_le_of_embedding inducedCopy.mapEdgeSet
    _ = deterministicInducedEdgeCount G
        (F.labelledCopyVertexFinset copy) := by
      unfold deterministicInducedEdgeCount
      exact SimpleGraph.edgeFinset_card.symm

private theorem two_le_card_labelledCopyVertexFinset_of_edgeCount_pos
    {V : Type*} [Fintype V] (F : FiniteGraphShape)
    {G : SimpleGraph V} (copy : SimpleGraph.Copy F.graph G)
    (hedge : 0 < F.edgeCount) :
    2 ≤ (F.labelledCopyVertexFinset copy).card := by
  have hedge' : 0 < F.graph.edgeSet.ncard := by
    simpa only [F.edgeCount_eq_ncard] using hedge
  obtain ⟨e, he⟩ :=
    (Set.ncard_pos (s := F.graph.edgeSet)).mp hedge'
  let u := e.out.1
  let v := e.out.2
  have huv : u ≠ v := by
    intro huv
    have hdiag : e.IsDiag := by
      rw [← e.out_eq, Sym2.mk_isDiag_iff]
      exact huv
    exact F.graph.not_isDiag_of_mem_edgeSet he hdiag
  have hu : copy u ∈ F.labelledCopyVertexFinset copy := by
    simp only [labelledCopyVertexFinset, Finset.mem_map,
      Finset.mem_univ, true_and]
    exact ⟨u, rfl⟩
  have hv : copy v ∈ F.labelledCopyVertexFinset copy := by
    simp only [labelledCopyVertexFinset, Finset.mem_map,
      Finset.mem_univ, true_and]
    exact ⟨v, rfl⟩
  exact (Finset.one_lt_card.mpr
    ⟨copy u, hu, copy v, hv, fun h ↦ huv (copy.injective h)⟩)

private theorem vertexCount_le_edgeCount_of_connected_cyclic
    (F : FiniteGraphShape) (hconn : F.graph.Connected)
    (hcyclic : ¬F.graph.IsAcyclic) :
    F.vertexCount ≤ F.edgeCount := by
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hcard
  change F.vertexCount ≤ F.graph.edgeFinset.card + 1 at hcard
  have hedge : F.graph.edgeFinset.card = F.edgeCount := by
    rw [F.edgeCount_eq_ncard]
    exact (Set.ncard_eq_toFinset_card' F.graph.edgeSet).symm
  rw [hedge] at hcard
  by_contra hnot
  have heq : F.edgeCount + 1 = F.vertexCount := by omega
  have htree : F.graph.IsTree :=
    SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ← SimpleGraph.edgeFinset_card, hedge]
      exact heq⟩
  exact hcyclic htree.2

end FiniteGraphShape

namespace DeterministicPlantWitness

/-! ## Paper-facing structural properties of the padded plant -/

/-- Alias exposing exact edge-cardinality preservation from the adapter
module. -/
theorem ambientGraph_edgeCard_preserved
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).edgeFinset.card = (W.graph n).edgeFinset.card :=
  W.ambientGraph_edgeFinset_card hr n

/-- The padded plant uses at most its natural `mₙ` source vertices. -/
theorem ambientGraph_hasSupportCardAtMost
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).HasSupportCardAtMost (appendixPlantSize r n) := by
  unfold SimpleGraph.HasSupportCardAtMost
  rw [← Set.ncard_eq_toFinset_card']
  exact W.ambientGraph_support_ncard_le hr n

/-- The padded plant retains the witness's maximum-degree bound. -/
theorem ambientGraph_hasMaximumDegreeAtMost
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (W.ambientGraph hr n).HasMaximumDegreeAtMost D := by
  intro v
  exact W.ambientGraph_maxDegree hr n v

/-- Pull an unlabelled occurrence in the padded graph back to a labelled
copy in the source graph. -/
noncomputable def sourceCopyOfAmbientConcreteCopy
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (W.ambientGraph hr n)) :
    SimpleGraph.Copy F.graph (W.graph n) := by
  let target : SimpleGraph.Copy F.graph
      ((W.graph n).map (ambientEmbedding hr n)) := by
    simpa only [ambientGraph] using F.concreteCopyToAmbientCopy copy
  exact F.pullbackMappedCopy (ambientEmbedding hr n) (W.graph n) target

/-- The edge support of an ambient concrete copy lies in the image of the
source complete graph.  This is the edge-set counterpart of
`sourceCopyOfAmbientConcreteCopy`. -/
theorem ambientConcreteCopyEdges_subset_embeddedTop
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (W.ambientGraph hr n)) :
    F.concreteCopyEdges (F.liftConcreteCopy (by exact le_top) copy) ⊆
      embedAmbientEdgeSet (ambientEmbedding hr n)
        (Finset.univ : Finset (AmbientEdge (appendixPlantSize r n))) := by
  intro e he
  let copyTop := F.liftConcreteCopy (by exact le_top) copy
  have htopEdge : (e : Sym2 (Fin n)) ∈ copyTop.1.edgeSet := by
    exact (F.mem_concreteCopyEdges copyTop e).mp (by simpa only [copyTop] using he)
  have htopAdj : copyTop.1.Adj e.1.out.1 e.1.out.2 := by
    change s(e.1.out.1, e.1.out.2) ∈ copyTop.1.edgeSet
    simpa only [e.1.out_eq] using htopEdge
  have hcopyAdj : copy.1.Adj e.1.out.1 e.1.out.2 := by
    exact (F.liftConcreteCopy_adj (by exact le_top) copy _ _).mp htopAdj
  have hambientAdj : (W.ambientGraph hr n).Adj e.1.out.1 e.1.out.2 :=
    copy.1.adj_sub hcopyAdj
  change ((W.graph n).map (ambientEmbedding hr n)).Adj
    e.1.out.1 e.1.out.2 at hambientAdj
  rw [SimpleGraph.map_adj] at hambientAdj
  rcases hambientAdj with ⟨a, b, hab, ha, hb⟩
  let sourceEdge : AmbientEdge (appendixPlantSize r n) :=
    ⟨s(a, b), hab.ne⟩
  rw [embedAmbientEdgeSet, Finset.mem_map]
  refine ⟨sourceEdge, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  change Sym2.map (ambientEmbedding hr n) s(a, b) = e.1
  rw [Sym2.map_pair_eq, ha, hb]
  exact e.1.out_eq

/-- Pulling an ambient occurrence edge-by-edge back through the padding
embedding preserves its exact abstract edge count. -/
theorem card_pullback_ambientConcreteCopyEdges
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (F : FiniteGraphShape)
    (copy : F.ConcreteCopy (W.ambientGraph hr n)) :
    (pullbackAmbientEdgeSet (ambientEmbedding hr n)
      (F.concreteCopyEdges
        (F.liftConcreteCopy (by exact le_top) copy))).card = F.edgeCount := by
  let copyTop := F.liftConcreteCopy (by exact le_top) copy
  have hsub : F.concreteCopyEdges copyTop ⊆
      embedAmbientEdgeSet (ambientEmbedding hr n)
        (Finset.univ : Finset (AmbientEdge (appendixPlantSize r n))) := by
    simpa only [copyTop] using
      W.ambientConcreteCopyEdges_subset_embeddedTop hr n F copy
  calc
    (pullbackAmbientEdgeSet (ambientEmbedding hr n)
        (F.concreteCopyEdges copyTop)).card =
        (F.concreteCopyEdges copyTop).card :=
      card_pullbackAmbientEdgeSet (ambientEmbedding hr n) hsub
    _ = F.edgeCount := F.card_concreteCopyEdges copyTop

/-! ## Restrictions on every shape occurring in the deterministic plant -/

/-- Choose a concrete ambient occurrence from a positive non-induced copy
count. -/
noncomputable def ambientConcreteCopyOfOccurrence
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (F : FiniteGraphShape)
    (hocc : 0 < F.nonInducedCopyCount (W.ambientGraph hr n)) :
    F.ConcreteCopy (W.ambientGraph hr n) :=
  Classical.choice (Fintype.card_pos_iff.mp hocc)

/-- Fixed-index local-sparsity restriction for an abstract shape that occurs
in the padded deterministic plant. -/
theorem occurringShape_localSparsity_of_scale
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (n : ℕ) (hn : 2 ≤ n)
    (hscale : (((2 * appendixDegreeCutoff n : ℕ) : ℝ)) ≤
      (appendixPlantSize r n : ℝ) ^ gamma)
    (F : FiniteGraphShape)
    (hocc : 0 < F.nonInducedCopyCount (W.ambientGraph hr n))
    (hcutoff : F.edgeCount ≤ appendixDegreeCutoff n) :
    (F.edgeCount : ℝ) ≤
      (1 + W.A / Real.log (n : ℝ)) * (F.vertexCount : ℝ) := by
  by_cases hedgeZero : F.edgeCount = 0
  · have hlog : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hfactor : 0 ≤ 1 + W.A / Real.log (n : ℝ) := by
      have hdiv : 0 ≤ W.A / Real.log (n : ℝ) :=
        div_nonneg W.A_pos.le hlog.le
      linarith
    rw [hedgeZero, Nat.cast_zero]
    exact mul_nonneg hfactor (Nat.cast_nonneg F.vertexCount)
  · have hedgePos : 0 < F.edgeCount := Nat.pos_of_ne_zero hedgeZero
    let copy := W.ambientConcreteCopyOfOccurrence hr n F hocc
    let sourceCopy := W.sourceCopyOfAmbientConcreteCopy hr n F copy
    let U := F.labelledCopyVertexFinset sourceCopy
    let T := pullbackAmbientEdgeSet (ambientEmbedding hr n)
      (F.concreteCopyEdges
        (F.liftConcreteCopy (by exact le_top) copy))
    have hUcard : U.card = F.vertexCount := by
      exact F.card_labelledCopyVertexFinset sourceCopy
    have hU2 : 2 ≤ U.card := by
      exact FiniteGraphShape.two_le_card_labelledCopyVertexFinset_of_edgeCount_pos
        F sourceCopy hedgePos
    have hTcard : T.card = F.edgeCount := by
      exact W.card_pullback_ambientConcreteCopyEdges hr n F copy
    have hUscale : (U.card : ℝ) ≤
        (appendixPlantSize r n : ℝ) ^ gamma := by
      calc
        (U.card : ℝ) = (F.vertexCount : ℝ) := by rw [hUcard]
        _ ≤ ((2 * F.edgeCount : ℕ) : ℝ) := by
          exact_mod_cast F.vertexCount_le_twice_edgeCount
        _ = ((2 * T.card : ℕ) : ℝ) := by rw [hTcard]
        _ ≤ ((2 * appendixDegreeCutoff n : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left 2 (hTcard.trans_le hcutoff)
        _ ≤ (appendixPlantSize r n : ℝ) ^ gamma := hscale
    have hcount : F.edgeCount ≤ deterministicInducedEdgeCount (W.graph n) U := by
      exact F.edgeCount_le_inducedEdgeCount sourceCopy
    have hlocal := W.localSparsity n hn U hU2 hUscale
    calc
      (F.edgeCount : ℝ) ≤
          (deterministicInducedEdgeCount (W.graph n) U : ℝ) := by
        exact_mod_cast hcount
      _ ≤ (1 + W.A / Real.log (n : ℝ)) * (U.card : ℝ) := hlocal
      _ = (1 + W.A / Real.log (n : ℝ)) * (F.vertexCount : ℝ) := by
        rw [hUcard]

/-- Every connected cyclic shape occurring in the ambient deterministic
plant has at least the witness's logarithmic girth many edges. -/
theorem occurringConnectedCyclicShape_girth
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (F : FiniteGraphShape) (hconn : F.graph.Connected)
    (hcyclic : ¬F.graph.IsAcyclic)
    (hocc : 0 < F.nonInducedCopyCount (W.ambientGraph hr n)) :
    W.kappa * Real.log (n : ℝ) ≤ (F.edgeCount : ℝ) := by
  let copy := W.ambientConcreteCopyOfOccurrence hr n F hocc
  let sourceCopy := W.sourceCopyOfAmbientConcreteCopy hr n F copy
  obtain ⟨v, cycle, hcycle, _hgirth⟩ :=
    SimpleGraph.exists_girth_eq_length.mpr hcyclic
  let sourceCycle := cycle.map sourceCopy.toHom
  have hsourceCycle : sourceCycle.IsCycle := by
    exact hcycle.map sourceCopy.injective
  have hwitness : W.kappa * Real.log (n : ℝ) ≤
      (sourceCycle.length : ℝ) :=
    W.girth n (sourceCopy v) sourceCycle hsourceCycle
  have htailLength : cycle.support.tail.length = cycle.length := by
    rw [List.length_tail, cycle.length_support]
    omega
  have hlengthVertex : cycle.length ≤ F.vertexCount := by
    rw [← htailLength]
    change cycle.support.tail.length ≤ Fintype.card F.Vertex
    exact hcycle.2.length_le_card
  have hvertexEdge : F.vertexCount ≤ F.edgeCount :=
    FiniteGraphShape.vertexCount_le_edgeCount_of_connected_cyclic
      F hconn hcyclic
  calc
    W.kappa * Real.log (n : ℝ) ≤ (sourceCycle.length : ℝ) := hwitness
    _ = (cycle.length : ℝ) := by
      rw [SimpleGraph.Walk.length_map]
    _ ≤ (F.vertexCount : ℝ) := by exact_mod_cast hlengthVertex
    _ ≤ (F.edgeCount : ℝ) := by exact_mod_cast hvertexEdge

/-- Eventually every shape occurring below the canonical degree cutoff
satisfies the deterministic Appendix's local-sparsity restriction. -/
theorem eventually_occurringShape_localSparsity
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F : FiniteGraphShape,
      0 < F.nonInducedCopyCount (W.ambientGraph hr n) →
      F.edgeCount ≤ appendixDegreeCutoff n →
      (F.edgeCount : ℝ) ≤
        (1 + W.A / Real.log (n : ℝ)) * (F.vertexCount : ℝ) := by
  filter_upwards
      [eventually_two_appendixDegreeCutoff_le_appendixPlantSize_rpow
        hr.1 hgamma.1,
       Filter.eventually_ge_atTop 2] with n hscale hn
  intro F hocc hcutoff
  exact W.occurringShape_localSparsity_of_scale hr n hn hscale F hocc hcutoff

/-- Combined occurrence-shape restriction used by the deterministic
low-degree argument: local sparsity for every connected low-degree shape,
and logarithmic girth whenever that shape is cyclic. -/
theorem eventually_occurringConnectedShape_restrictions
    {D : ℕ} {r gamma : ℝ} (W : DeterministicPlantWitness D r gamma)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F : FiniteGraphShape,
      F.graph.Connected →
      0 < F.nonInducedCopyCount (W.ambientGraph hr n) →
      F.edgeCount ≤ appendixDegreeCutoff n →
      ((F.edgeCount : ℝ) ≤
          (1 + W.A / Real.log (n : ℝ)) * (F.vertexCount : ℝ)) ∧
        (¬F.graph.IsAcyclic →
          W.kappa * Real.log (n : ℝ) ≤ (F.edgeCount : ℝ)) := by
  filter_upwards [W.eventually_occurringShape_localSparsity hr hgamma]
      with n hlocal
  intro F hconn hocc hcutoff
  exact ⟨hlocal F hocc hcutoff,
    fun hcyclic ↦ W.occurringConnectedCyclicShape_girth
      hr n F hconn hcyclic hocc⟩

end DeterministicPlantWitness

end

end LowDegree
