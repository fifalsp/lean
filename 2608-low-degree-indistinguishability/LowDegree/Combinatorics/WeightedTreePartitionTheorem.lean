import LowDegree.Combinatorics.IndexedWeightedTreePartition

/-!
# Label-preserving weighted partitions of finite subcubic trees

This module packages the intrinsic packing theorem and its indexed lift into
the statement of paper Lemma 5.4.  Unlike the intrinsic quotient, the witness
below retains the original tree vertices, so its fibers are literal connected
clusters and its quotient adjacency is the contraction adjacency of those
fibers.
-/

namespace LowDegree

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

open scoped BigOperators

universe u

namespace WeightedTreePartitionTheorem

open WeightedTreePartition
open WeightedTreePartitionAdapter
open IndexedWeightedTreePartition

variable {X : Type u} [Fintype X]

/-- Total weight of one fiber of a finite cluster assignment. -/
def fiberWeight (w : X → ℕ) {m : ℕ} (clusterOf : X → Fin m)
    (i : Fin m) : ℕ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ clusterOf x = i), w x

/-- A label-preserving partition of a finite tree into connected weighted
clusters, together with the exact contraction quotient. -/
structure VertexPartitionWitness (Q : SimpleGraph X) (w : X → ℕ)
    (m lower upper : ℕ) where
  clusterOf : X → Fin m
  cluster_surjective : Function.Surjective clusterOf
  cluster_connected : ∀ i : Fin m,
    (Q.induce {x : X | clusterOf x = i}).Connected
  quotient : SimpleGraph (Fin m)
  quotient_adj : ∀ ⦃i j : Fin m⦄, quotient.Adj i j ↔
    i ≠ j ∧ ∃ x y : X,
      Q.Adj x y ∧ clusterOf x = i ∧ clusterOf y = j
  quotient_isTree : quotient.IsTree
  cluster_lower : ∀ i : Fin m, lower ≤ fiberWeight w clusterOf i
  cluster_upper : ∀ i : Fin m, fiberWeight w clusterOf i ≤ upper

omit [Fintype X] in
private theorem sum_toFinset_eq_map_sum (w : X → ℕ) {l : List X}
    (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, w x) = (l.map w).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

private theorem finiteClusterOf_fiberWeight_eq
    {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (ht : (vertices t).Nodup)
    (hcover : ∀ x : X, x ∈ vertices t) (w : X → ℕ)
    (i : Fin (Fintype.card (Node q))) :
    fiberWeight w (finiteClusterOf h hcover) i =
      clusterWeight w (Node.label ((occurrenceEquiv q).symm i)) := by
  classical
  let n : Node q := (occurrenceEquiv q).symm i
  have hfilter :
      Finset.univ.filter (fun x ↦ finiteClusterOf h hcover x = i) =
        (Node.label n).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, finiteClusterOf]
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    exact clusterNode_eq_iff_mem h ht x (hcover x) n
  rw [fiberWeight, hfilter]
  have hnNodup : (Node.label n).Nodup :=
    (List.nodup_flatten.mp (h.flattenClusters_nodup ht)).1 _
      (Node.label_mem_vertices n)
  exact (sum_toFinset_eq_map_sum w hnNodup).trans rfl

/-- **Paper Lemma 5.4, label-preserving finite-tree form.**

Let `Q` be a finite tree of maximum degree at most three, let every node
have natural weight at most one, and suppose the total weight is at least a
positive integer `ℓ`.  Then the original vertex set admits a surjective
cluster assignment whose fibers are connected, whose contraction quotient
is a tree, and whose fiber weights all lie in `[ℓ, 3ℓ]`. -/
theorem exists_vertexPartitionWitness
    (Q : SimpleGraph X) (hQ : Q.IsTree)
    (hdeg : ∀ x, Q.degree x ≤ 3) (w : X → ℕ)
    (hw : ∀ x, w x ≤ 1) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (htotal : ℓ ≤ ∑ x : X, w x) :
    ∃ m : ℕ, Nonempty (VertexPartitionWitness Q w m ℓ (3 * ℓ)) := by
  classical
  obtain ⟨r, erasedQ, _hroot, _hsubcubic, herasedPartition,
      herasedBounds⟩ :=
    WeightedTreePartitionAdapter.exists_intrinsic_partition
      hQ hdeg w hw hℓ htotal
  let source : RTree X := labeledTree hQ r r
  have herasedPartition' :
      WeightedTreePartition.IsPartition
        (withWeights w source) erasedQ := by
    simpa [source] using herasedPartition
  obtain ⟨indexedQ, hpartition, hweigh⟩ :=
    liftPartition w hw herasedPartition'
  have hsourceNodup : (vertices source).Nodup := by
    simpa [source] using vertices_labeledTree_nodup hQ r r
  have hsourceCover : ∀ x : X, x ∈ vertices source := by
    intro x
    simpa [source] using mem_vertices_labeledTree_root hQ r x
  have hsourceRespects : Respects Q source := by
    simpa [source] using labeledTree_respects hQ r r
  have hgood : Good Q source indexedQ :=
    hpartition.good hsourceRespects
  have hindexedBounds : WeightsIn w ℓ (3 * ℓ) indexedQ := by
    apply weightsIn_of_labelsIn w
    rw [hweigh]
    exact herasedBounds
  let m := Fintype.card (Node indexedQ)
  refine ⟨m, ⟨{
    clusterOf := finiteClusterOf hpartition hsourceCover
    cluster_surjective := ?_
    cluster_connected := ?_
    quotient := finiteQuotient indexedQ
    quotient_adj := ?_
    quotient_isTree := ?_
    cluster_lower := ?_
    cluster_upper := ?_ }⟩⟩
  · exact finiteClusterOf_surjective hpartition hsourceNodup hsourceCover
  · intro i
    exact finiteClusterOf_connected hpartition hsourceNodup hsourceCover
      hgood i
  · intro i j
    exact finiteQuotient_adj_iff hQ hpartition hsourceNodup
      hsourceCover hgood
  · exact finiteQuotient_isTree indexedQ
  · intro i
    rw [finiteClusterOf_fiberWeight_eq
      hpartition hsourceNodup hsourceCover w i]
    exact (Node.weight_bounds_of_weightsIn hindexedBounds _).1
  · intro i
    rw [finiteClusterOf_fiberWeight_eq
      hpartition hsourceNodup hsourceCover w i]
    exact (Node.weight_bounds_of_weightsIn hindexedBounds _).2

end WeightedTreePartitionTheorem

end

end LowDegree
