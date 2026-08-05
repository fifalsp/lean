import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Perm.Basic
import LowDegree.Combinatorics.WeightedTreePartitionAdapter

/-!
# Label-preserving partitions of weighted subcubic trees

This module refines `WeightedTreePartition.IsPartition` by retaining the
original vertex labels in every quotient cluster.  The intrinsic packing
theorem can then be lifted without rerunning its numerical argument.
-/

namespace LowDegree
namespace IndexedWeightedTreePartition

open scoped BigOperators List
open WeightedTreePartition
open WeightedTreePartitionAdapter

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

variable {X : Type*}

abbrev IndexedQuotient (X : Type*) := RTree (List X)

/-- Natural weight of a retained cluster list. -/
def clusterWeight (w : X → ℕ) (s : List X) : ℕ :=
  (s.map w).sum

/-- Forget labels from an indexed quotient, retaining cluster weights. -/
def weighQuotient (w : X → ℕ) : IndexedQuotient X → QuotientTree
  | .node s children => .node (clusterWeight w s) (children.map (weighQuotient w))

mutual

/-- Label-preserving analogue of `RootSplit`. -/
inductive RootSplit : RTree X → List X → List (RTree X) → Prop where
  | node (x : X) {children : List (RTree X)} {cluster : List X}
      {boundary : List (RTree X)} :
      SplitChildren children cluster boundary →
      RootSplit (.node x children) (x :: cluster) boundary

/-- Label-preserving analogue of `SplitChildren`. -/
inductive SplitChildren : List (RTree X) → List X → List (RTree X) → Prop where
  | nil : SplitChildren [] [] []
  | cut {t : RTree X} {ts : List (RTree X)} {cluster : List X}
      {boundary : List (RTree X)} :
      SplitChildren ts cluster boundary →
      SplitChildren (t :: ts) cluster (t :: boundary)
  | merge {t : RTree X} {ts : List (RTree X)} {cluster₁ cluster₂ : List X}
      {boundary₁ boundary₂ : List (RTree X)} :
      RootSplit t cluster₁ boundary₁ →
      SplitChildren ts cluster₂ boundary₂ →
      SplitChildren (t :: ts) (cluster₁ ++ cluster₂) (boundary₁ ++ boundary₂)

end


mutual

/-- A structural partition whose quotient nodes retain their original labels. -/
inductive IsPartition : RTree X → IndexedQuotient X → Prop where
  | node {t : RTree X} {cluster : List X} {boundary : List (RTree X)}
      {children : List (IndexedQuotient X)} :
      RootSplit t cluster boundary → PartitionList boundary children →
      IsPartition t (.node cluster children)
  | contractFirst {t : RTree X} {cluster₁ cluster₂ : List X}
      {grandchildren siblings : List (IndexedQuotient X)} :
      IsPartition t (.node cluster₁ (.node cluster₂ grandchildren :: siblings)) →
      IsPartition t (.node (cluster₁ ++ cluster₂) (grandchildren ++ siblings))

/-- Forest version of `IsPartition`. -/
inductive PartitionList : List (RTree X) → List (IndexedQuotient X) → Prop where
  | nil : PartitionList [] []
  | cons {t : RTree X} {q : IndexedQuotient X}
      {ts : List (RTree X)} {qs : List (IndexedQuotient X)} :
      IsPartition t q → PartitionList ts qs → PartitionList (t :: ts) (q :: qs)

end


/-! ### Lifting the intrinsic structural proof -/

mutual

/-- Lift an intrinsic root split while recovering the exact original labels. -/
theorem liftRootSplit (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {t : RTree X} {n : ℕ} {boundary : List WeightedTree}
    (h : WeightedTreePartition.RootSplit (withWeights w t) n boundary) :
    ∃ cluster : List X, ∃ indexedBoundary : List (RTree X),
      RootSplit t cluster indexedBoundary ∧
      boundary = indexedBoundary.map (withWeights w) ∧
      n = clusterWeight w cluster := by
  cases t with
  | node x children =>
      rw [withWeights] at h
      cases h with
      | node _ hchildren =>
          obtain ⟨cluster, indexedBoundary, hindexed, hboundary, hweight⟩ :=
            liftSplitChildren w hw hchildren
          refine ⟨x :: cluster, indexedBoundary, .node x hindexed, hboundary, ?_⟩
          simp only [clusterWeight] at hweight
          simp only [clusterWeight, List.map_cons, List.sum_cons]
          rw [hweight, nodeWeight_boolWeight w hw]

/-- Lift the child-list part of an intrinsic root split. -/
theorem liftSplitChildren (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {ts : List (RTree X)} {n : ℕ} {boundary : List WeightedTree}
    (h : WeightedTreePartition.SplitChildren (ts.map (withWeights w)) n boundary) :
    ∃ cluster : List X, ∃ indexedBoundary : List (RTree X),
      SplitChildren ts cluster indexedBoundary ∧
      boundary = indexedBoundary.map (withWeights w) ∧
      n = clusterWeight w cluster := by
  cases ts with
  | nil =>
      cases h
      exact ⟨[], [], .nil, rfl, rfl⟩
  | cons t ts =>
      cases h with
      | cut hrest =>
          obtain ⟨cluster, indexedBoundary, hindexed, hboundary, hweight⟩ :=
            liftSplitChildren w hw hrest
          refine ⟨cluster, t :: indexedBoundary, .cut hindexed, ?_, hweight⟩
          simp [hboundary]
      | merge hroot hrest =>
          obtain ⟨cluster₁, boundary₁, hindexed₁, hboundary₁, hweight₁⟩ :=
            liftRootSplit w hw hroot
          obtain ⟨cluster₂, boundary₂, hindexed₂, hboundary₂, hweight₂⟩ :=
            liftSplitChildren w hw hrest
          refine ⟨cluster₁ ++ cluster₂, boundary₁ ++ boundary₂,
            .merge hindexed₁ hindexed₂, ?_, ?_⟩
          · simp [hboundary₁, hboundary₂]
          · simp only [clusterWeight] at hweight₁ hweight₂ ⊢
            simp only [List.map_append, List.sum_append]
            omega

end

private def LiftPartitionMotive (w : X → ℕ) {weightedT : WeightedTree}
    {q : QuotientTree} (_h : WeightedTreePartition.IsPartition weightedT q) : Prop :=
  ∀ t : RTree X, withWeights w t = weightedT →
    ∃ indexedQ : IndexedQuotient X,
      IsPartition t indexedQ ∧ weighQuotient w indexedQ = q

private def LiftPartitionListMotive (w : X → ℕ)
    {weightedTs : List WeightedTree} {qs : List QuotientTree}
    (_h : WeightedTreePartition.PartitionList weightedTs qs) : Prop :=
  ∀ ts : List (RTree X), ts.map (withWeights w) = weightedTs →
    ∃ indexedQs : List (IndexedQuotient X),
      PartitionList ts indexedQs ∧ indexedQs.map (weighQuotient w) = qs

private theorem liftPartition_node (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {weightedT : WeightedTree} {n : ℕ} {boundary : List WeightedTree}
    {children : List QuotientTree}
    (hsplit : WeightedTreePartition.RootSplit weightedT n boundary)
    (hparts : WeightedTreePartition.PartitionList boundary children)
    (ihparts : LiftPartitionListMotive w hparts) :
    LiftPartitionMotive w (WeightedTreePartition.IsPartition.node hsplit hparts) := by
  intro t ht
  subst weightedT
  obtain ⟨cluster, indexedBoundary, hindexedSplit, hboundary, hweight⟩ :=
    liftRootSplit w hw hsplit
  obtain ⟨indexedChildren, hindexedParts, hchildren⟩ :=
    ihparts indexedBoundary hboundary.symm
  refine ⟨.node cluster indexedChildren, .node hindexedSplit hindexedParts, ?_⟩
  simp only [weighQuotient, RTree.node.injEq]
  exact ⟨hweight.symm, hchildren⟩

private theorem liftPartition_contractFirst (w : X → ℕ)
    {weightedT : WeightedTree} {n₁ n₂ : ℕ}
    {grandchildren siblings : List QuotientTree}
    (hprev : WeightedTreePartition.IsPartition weightedT
      (.node n₁ (.node n₂ grandchildren :: siblings)))
    (ihprev : LiftPartitionMotive w hprev) :
    LiftPartitionMotive w (WeightedTreePartition.IsPartition.contractFirst hprev) := by
  intro t ht
  obtain ⟨indexedQ, hindexed, hweigh⟩ := ihprev t ht
  cases indexedQ with
  | node cluster₁ indexedChildren =>
      simp only [weighQuotient, RTree.node.injEq] at hweigh
      rcases hweigh with ⟨hweight₁, hchildren⟩
      cases indexedChildren with
      | nil => simp at hchildren
      | cons indexedFirst indexedSiblings =>
          cases indexedFirst with
          | node cluster₂ indexedGrandchildren =>
              simp only [List.map_cons, List.cons.injEq, weighQuotient,
                RTree.node.injEq] at hchildren
              rcases hchildren with ⟨hfirst, hsiblings⟩
              rcases hfirst with ⟨hweight₂, hgrandchildren⟩
              refine ⟨.node (cluster₁ ++ cluster₂)
                (indexedGrandchildren ++ indexedSiblings),
                .contractFirst hindexed, ?_⟩
              simp only [weighQuotient, clusterWeight, List.map_append,
                List.sum_append, RTree.node.injEq]
              constructor
              · simpa only [clusterWeight] using
                  congrArg₂ (fun a b : ℕ ↦ a + b) hweight₁ hweight₂
              · simp [hgrandchildren, hsiblings]

private theorem liftPartition_nil (w : X → ℕ) :
    LiftPartitionListMotive w WeightedTreePartition.PartitionList.nil := by
  intro ts hts
  cases ts with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons t ts => simp at hts

private theorem liftPartition_cons (w : X → ℕ)
    {weightedT : WeightedTree} {q : QuotientTree}
    {weightedTs : List WeightedTree} {qs : List QuotientTree}
    (hfirst : WeightedTreePartition.IsPartition weightedT q)
    (hrest : WeightedTreePartition.PartitionList weightedTs qs)
    (ihfirst : LiftPartitionMotive w hfirst)
    (ihrest : LiftPartitionListMotive w hrest) :
    LiftPartitionListMotive w (WeightedTreePartition.PartitionList.cons hfirst hrest) := by
  intro ts hts
  cases ts with
  | nil => simp at hts
  | cons t ts =>
      simp only [List.map_cons, List.cons.injEq] at hts
      rcases hts with ⟨ht, hts⟩
      obtain ⟨indexedFirst, hindexedFirst, hfirstWeight⟩ := ihfirst t ht
      obtain ⟨indexedRest, hindexedRest, hrestWeight⟩ := ihrest ts hts
      exact ⟨indexedFirst :: indexedRest, .cons hindexedFirst hindexedRest,
        by simp [hfirstWeight, hrestWeight]⟩

/-- Lift an intrinsic partition proof to a label-preserving partition. -/
theorem liftPartition (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {t : RTree X} {q : QuotientTree}
    (h : WeightedTreePartition.IsPartition (withWeights w t) q) :
    ∃ indexedQ : IndexedQuotient X,
      IsPartition t indexedQ ∧ weighQuotient w indexedQ = q :=
  (WeightedTreePartition.IsPartition.rec
    (motive_1 := fun _ _ h ↦ LiftPartitionMotive w h)
    (motive_2 := fun _ _ h ↦ LiftPartitionListMotive w h)
    (liftPartition_node w hw) (liftPartition_contractFirst w)
    (liftPartition_nil w) (liftPartition_cons w) h) t rfl

/-- Lift a forest of intrinsic partitions. -/
theorem liftPartitionList (w : X → ℕ) (hw : ∀ x, w x ≤ 1)
    {ts : List (RTree X)} {qs : List QuotientTree}
    (h : WeightedTreePartition.PartitionList (ts.map (withWeights w)) qs) :
    ∃ indexedQs : List (IndexedQuotient X),
      PartitionList ts indexedQs ∧ indexedQs.map (weighQuotient w) = qs :=
  (WeightedTreePartition.PartitionList.rec
    (motive_1 := fun _ _ h ↦ LiftPartitionMotive w h)
    (motive_2 := fun _ _ h ↦ LiftPartitionListMotive w h)
    (liftPartition_node w hw) (liftPartition_contractFirst w)
    (liftPartition_nil w) (liftPartition_cons w) h) ts rfl

/-! ### The indexed clusters cover the input labels -/

/-- Preorder concatenation of all labels in a forest. -/
def forestVertices (ts : List (RTree X)) : List X :=
  (ts.map vertices).flatten

/-- Preorder list of clusters in an indexed quotient. -/
def clusterLists (q : IndexedQuotient X) : List (List X) :=
  vertices q

/-- Concatenation of all cluster-label lists. -/
def flattenClusters (q : IndexedQuotient X) : List X :=
  (clusterLists q).flatten

mutual

/-- A root split accounts for every input label, up to reordering. -/
theorem RootSplit.perm_vertices {t : RTree X} {cluster : List X}
    {boundary : List (RTree X)} (h : RootSplit t cluster boundary) :
    (cluster ++ forestVertices boundary).Perm (vertices t) := by
  cases h with
  | node x hchildren =>
      simpa [forestVertices, vertices] using
        (SplitChildren.perm_vertices hchildren).cons x

/-- Forest version of `RootSplit.perm_vertices`. -/
theorem SplitChildren.perm_vertices {ts : List (RTree X)} {cluster : List X}
    {boundary : List (RTree X)} (h : SplitChildren ts cluster boundary) :
    (cluster ++ forestVertices boundary).Perm (forestVertices ts) := by
  cases h with
  | nil => rfl
  | @cut t ts cluster boundary hrest =>
      have ih := SplitChildren.perm_vertices hrest
      simp only [forestVertices, List.map_cons, List.flatten_cons]
      calc
        cluster ++ (vertices t ++ (boundary.map vertices).flatten) ~
            vertices t ++ (cluster ++ (boundary.map vertices).flatten) := by
              rw [← List.append_assoc, ← List.append_assoc]
              exact (List.perm_append_comm (l₁ := cluster) (l₂ := vertices t)).append_right _
        _ ~ vertices t ++ (ts.map vertices).flatten := ih.append_left _
  | @merge t ts cluster₁ cluster₂ boundary₁ boundary₂ hroot hrest =>
      have ihroot := RootSplit.perm_vertices hroot
      have ihrest := SplitChildren.perm_vertices hrest
      simp only [forestVertices, List.map_cons, List.flatten_cons, List.map_append,
        List.flatten_append]
      calc
        (cluster₁ ++ cluster₂) ++
            ((boundary₁.map vertices).flatten ++ (boundary₂.map vertices).flatten) ~
          (cluster₁ ++ (boundary₁.map vertices).flatten) ++
            (cluster₂ ++ (boundary₂.map vertices).flatten) := by
              simpa only [List.append_assoc] using
                ((List.perm_append_comm (l₁ := cluster₂)
                  (l₂ := (boundary₁.map vertices).flatten)).append_left
                    cluster₁).append_right (boundary₂.map vertices).flatten
        _ ~ vertices t ++ (ts.map vertices).flatten := ihroot.append ihrest

end

private theorem partition_perm_node {t : RTree X} {cluster : List X}
    {boundary : List (RTree X)} {children : List (IndexedQuotient X)}
    (hsplit : RootSplit t cluster boundary) (_hparts : PartitionList boundary children)
    (ihparts : ((children.map flattenClusters).flatten).Perm
      (forestVertices boundary)) :
    (flattenClusters (.node cluster children)).Perm (vertices t) := by
  simpa [flattenClusters, clusterLists, vertices, List.flatten_flatten,
    List.map_map, Function.comp_def] using
    (List.Perm.append_left cluster ihparts).trans hsplit.perm_vertices

private theorem partition_perm_contractFirst {t : RTree X}
    {cluster₁ cluster₂ : List X}
    {grandchildren siblings : List (IndexedQuotient X)}
    (_hprev : IsPartition t (.node cluster₁ (.node cluster₂ grandchildren :: siblings)))
    (ih : (flattenClusters
      (.node cluster₁ (.node cluster₂ grandchildren :: siblings))).Perm (vertices t)) :
    (flattenClusters (.node (cluster₁ ++ cluster₂)
      (grandchildren ++ siblings))).Perm (vertices t) := by
  simpa [flattenClusters, clusterLists, vertices, List.map_append,
    List.flatten_append, List.append_assoc] using ih

private theorem partition_perm_cons {t : RTree X} {q : IndexedQuotient X}
    {ts : List (RTree X)} {qs : List (IndexedQuotient X)}
    (_hfirst : IsPartition t q) (_hrest : PartitionList ts qs)
    (ihfirst : (flattenClusters q).Perm (vertices t))
    (ihrest : ((qs.map flattenClusters).flatten).Perm (forestVertices ts)) :
    (((q :: qs).map flattenClusters).flatten).Perm (forestVertices (t :: ts)) := by
  simpa [forestVertices] using ihfirst.append ihrest

/-- The quotient clusters form a label partition of the input tree. -/
theorem IsPartition.perm_vertices {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) : (flattenClusters q).Perm (vertices t) :=
  IsPartition.rec
    (motive_1 := fun t q _ ↦ (flattenClusters q).Perm (vertices t))
    (motive_2 := fun ts qs _ ↦
      ((qs.map flattenClusters).flatten).Perm (forestVertices ts))
    partition_perm_node partition_perm_contractFirst (List.Perm.refl [])
      partition_perm_cons h

/-- Forest version of `IsPartition.perm_vertices`. -/
theorem PartitionList.perm_vertices {ts : List (RTree X)}
    {qs : List (IndexedQuotient X)} (h : PartitionList ts qs) :
    ((qs.map flattenClusters).flatten).Perm (forestVertices ts) :=
  PartitionList.rec
    (motive_1 := fun t q _ ↦ (flattenClusters q).Perm (vertices t))
    (motive_2 := fun ts qs _ ↦
      ((qs.map flattenClusters).flatten).Perm (forestVertices ts))
    partition_perm_node partition_perm_contractFirst (List.Perm.refl [])
      partition_perm_cons h

/-- If the input labels are unique, indexed clusters are pairwise disjoint and
each cluster itself has no repeated labels. -/
theorem IsPartition.flattenClusters_nodup {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (ht : (vertices t).Nodup) :
    (flattenClusters q).Nodup :=
  (h.perm_vertices.nodup_iff).2 ht

/-! ### Indexed cluster weights -/

mutual

/-- Every retained cluster has weight in a closed interval. -/
inductive WeightsIn (w : X → ℕ) (lower upper : ℕ) :
    IndexedQuotient X → Prop where
  | node {cluster : List X} {children : List (IndexedQuotient X)} :
      lower ≤ clusterWeight w cluster → clusterWeight w cluster ≤ upper →
      WeightsInList w lower upper children →
      WeightsIn w lower upper (.node cluster children)

/-- Forest version of `WeightsIn`. -/
inductive WeightsInList (w : X → ℕ) (lower upper : ℕ) :
    List (IndexedQuotient X) → Prop where
  | nil : WeightsInList w lower upper []
  | cons {q : IndexedQuotient X} {qs : List (IndexedQuotient X)} :
      WeightsIn w lower upper q → WeightsInList w lower upper qs →
      WeightsInList w lower upper (q :: qs)

end


mutual

/-- Bounds on an erased quotient lift to its retained cluster lists. -/
theorem weightsIn_of_labelsIn (w : X → ℕ) {lower upper : ℕ}
    {q : IndexedQuotient X}
    (h : WeightedTreePartition.LabelsIn lower upper (weighQuotient w q)) :
    WeightsIn w lower upper q := by
  cases q with
  | node cluster children =>
      rw [weighQuotient] at h
      cases h with
      | node hl hu hchildren =>
          exact .node hl hu (weightsInList_of_labelsInList w hchildren)

/-- Forest version of `weightsIn_of_labelsIn`. -/
theorem weightsInList_of_labelsInList (w : X → ℕ) {lower upper : ℕ}
    {qs : List (IndexedQuotient X)}
    (h : WeightedTreePartition.LabelsInList lower upper
      (qs.map (weighQuotient w))) :
    WeightsInList w lower upper qs := by
  cases qs with
  | nil => exact .nil
  | cons q qs =>
      cases h with
      | cons hfirst hrest =>
          exact .cons (weightsIn_of_labelsIn w hfirst)
            (weightsInList_of_labelsInList w hrest)

end


/-! ### Connectivity retained by structural contractions -/

/-- Every parent-child edge displayed by a rose tree is an edge of `Q`. -/
def Respects (Q : SimpleGraph X) : RTree X → Prop
  | .node x children =>
      (∀ child ∈ children, Q.Adj x (rootLabel child)) ∧
      ∀ child ∈ children, Respects Q child

mutual

/-- Boundary subtrees inherit the parent tree's edge-respecting property. -/
theorem RootSplit.boundary_respects {Q : SimpleGraph X} {t : RTree X}
    {cluster : List X} {boundary : List (RTree X)}
    (h : RootSplit t cluster boundary) (ht : Respects Q t) :
    ∀ s ∈ boundary, Respects Q s := by
  cases h with
  | @node x children cluster boundary hchildren =>
      rw [Respects] at ht
      exact SplitChildren.boundary_respects hchildren ht.2

/-- Child-list version of `RootSplit.boundary_respects`. -/
theorem SplitChildren.boundary_respects {Q : SimpleGraph X}
    {ts : List (RTree X)} {cluster : List X} {boundary : List (RTree X)}
    (h : SplitChildren ts cluster boundary)
    (hrespect : ∀ child ∈ ts, Respects Q child) :
    ∀ s ∈ boundary, Respects Q s := by
  cases h with
  | nil => simp
  | @cut t ts cluster boundary hrest =>
      intro s hs
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hrespect _ (by simp)
      · exact SplitChildren.boundary_respects hrest
          (fun child hchild ↦ hrespect child (by simp [hchild])) s hs
  | @merge t ts cluster₁ cluster₂ boundary₁ boundary₂ hroot hrest =>
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact RootSplit.boundary_respects hroot (hrespect t (by simp)) s hs
      · exact SplitChildren.boundary_respects hrest
          (fun child hchild ↦ hrespect child (by simp [hchild])) s hs

end

private theorem induce_singleton_connected (Q : SimpleGraph X) (x : X) :
    (Q.induce ({x} : Set X)).Connected := by
  constructor
  · intro u v
    have huv : u = v := by
      apply Subtype.ext
      have hu : u.val = x := Set.mem_singleton_iff.mp u.property
      have hv : v.val = x := Set.mem_singleton_iff.mp v.property
      exact hu.trans hv.symm
    subst v
    exact .rfl

mutual

/-- A retained root cluster induces a connected subgraph. -/
theorem RootSplit.cluster_connected {Q : SimpleGraph X} {t : RTree X}
    {cluster : List X} {boundary : List (RTree X)}
    (h : RootSplit t cluster boundary) (ht : Respects Q t) :
    (Q.induce {x | x ∈ cluster}).Connected := by
  cases h with
  | @node x children cluster boundary hchildren =>
      rw [Respects] at ht
      rcases ht with ⟨hadj, hrespect⟩
      have hconn := SplitChildren.cluster_connected_at x hchildren hadj hrespect
      have hset : {y : X | y ∈ x :: cluster} =
          {y : X | y = x ∨ y ∈ cluster} := by
        ext y
        simp [eq_comm]
      rw [hset]
      exact hconn

/-- While processing children, adjoining the parent to all merged root
clusters stays connected. -/
theorem SplitChildren.cluster_connected_at {Q : SimpleGraph X} (x : X)
    {ts : List (RTree X)} {cluster : List X} {boundary : List (RTree X)}
    (h : SplitChildren ts cluster boundary)
    (hadj : ∀ child ∈ ts, Q.Adj x (rootLabel child))
    (hrespect : ∀ child ∈ ts, Respects Q child) :
    (Q.induce {y | y = x ∨ y ∈ cluster}).Connected := by
  cases h with
  | nil =>
      have hset : {y : X | y = x ∨ y ∈ ([] : List X)} = ({x} : Set X) := by
        ext y
        simp
      rw [hset]
      exact induce_singleton_connected Q x
  | @cut t ts cluster boundary hrest =>
      exact SplitChildren.cluster_connected_at x hrest
        (fun child hchild ↦ hadj child (by simp [hchild]))
        (fun child hchild ↦ hrespect child (by simp [hchild]))
  | @merge t ts cluster₁ cluster₂ boundary₁ boundary₂ hroot hrest =>
      have htconn := RootSplit.cluster_connected hroot (hrespect t (by simp))
      have hrestconn := SplitChildren.cluster_connected_at x hrest
        (fun child hchild ↦ hadj child (by simp [hchild]))
        (fun child hchild ↦ hrespect child (by simp [hchild]))
      have htroot : rootLabel t ∈ cluster₁ := by
        cases hroot
        simp [rootLabel]
      have hunion := SimpleGraph.induce_connected_adj_union hrestconn htconn
        (show x = x ∨ x ∈ cluster₂ from Or.inl rfl) htroot (hadj t (by simp))
      have hset :
          ({y : X | y = x ∨ y ∈ cluster₂} ∪ {y : X | y ∈ cluster₁}) =
            {y : X | y = x ∨ y ∈ cluster₁ ++ cluster₂} := by
        ext y
        simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
        aesop
      rw [hset] at hunion
      exact hunion

end

mutual

/-- Every boundary subtree left by a root split is attached by an edge to the
retained root cluster. -/
theorem RootSplit.boundary_attached {Q : SimpleGraph X} {t : RTree X}
    {cluster : List X} {boundary : List (RTree X)}
    (h : RootSplit t cluster boundary) (ht : Respects Q t) :
    ∀ s ∈ boundary, ∃ u ∈ cluster, Q.Adj u (rootLabel s) := by
  cases h with
  | @node x children cluster boundary hchildren =>
      rw [Respects] at ht
      rcases ht with ⟨hadj, hrespect⟩
      intro s hs
      obtain ⟨u, hu, hua⟩ :=
        SplitChildren.boundary_attached_at x hchildren hadj hrespect s hs
      refine ⟨u, ?_, hua⟩
      simp only [List.mem_cons]
      exact hu

/-- Child-list version of `RootSplit.boundary_attached`. -/
theorem SplitChildren.boundary_attached_at {Q : SimpleGraph X} (x : X)
    {ts : List (RTree X)} {cluster : List X} {boundary : List (RTree X)}
    (h : SplitChildren ts cluster boundary)
    (hadj : ∀ child ∈ ts, Q.Adj x (rootLabel child))
    (hrespect : ∀ child ∈ ts, Respects Q child) :
    ∀ s ∈ boundary, ∃ u, (u = x ∨ u ∈ cluster) ∧ Q.Adj u (rootLabel s) := by
  cases h with
  | nil => simp
  | @cut t ts cluster boundary hrest =>
      intro s hs
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨x, Or.inl rfl, hadj _ (by simp)⟩
      · exact SplitChildren.boundary_attached_at x hrest
          (fun child hchild ↦ hadj child (by simp [hchild]))
          (fun child hchild ↦ hrespect child (by simp [hchild])) s hs
  | @merge t ts cluster₁ cluster₂ boundary₁ boundary₂ hroot hrest =>
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨u, hu, hua⟩ :=
          RootSplit.boundary_attached hroot (hrespect t (by simp)) s hs
        exact ⟨u, Or.inr (List.mem_append_left _ hu), hua⟩
      · obtain ⟨u, hu, hua⟩ := SplitChildren.boundary_attached_at x hrest
          (fun child hchild ↦ hadj child (by simp [hchild]))
          (fun child hchild ↦ hrespect child (by simp [hchild])) s hs
        refine ⟨u, ?_, hua⟩
        rcases hu with hu | hu
        · exact Or.inl hu
        · exact Or.inr (List.mem_append_right _ hu)

end

/-! ### Global connectivity and quotient-edge realization -/

/-- Root cluster of an indexed quotient. -/
def rootCluster : IndexedQuotient X → List X
  | .node cluster _ => cluster

/-- Every cluster in an indexed quotient induces a connected subgraph. -/
def AllConnected (Q : SimpleGraph X) : IndexedQuotient X → Prop
  | .node cluster children =>
      (Q.induce {x | x ∈ cluster}).Connected ∧
      ∀ child ∈ children, AllConnected Q child

/-- Every displayed quotient parent-child edge is realized by an original
edge between the corresponding retained clusters. -/
def QuotientRespects (Q : SimpleGraph X) : IndexedQuotient X → Prop
  | .node cluster children =>
      (∀ child ∈ children,
        ∃ u ∈ cluster, ∃ v ∈ rootCluster child, Q.Adj u v) ∧
      ∀ child ∈ children, QuotientRespects Q child

/-- Structural facts retained by an indexed partition. -/
structure Good (Q : SimpleGraph X) (t : RTree X) (q : IndexedQuotient X) : Prop where
  root_mem : rootLabel t ∈ rootCluster q
  all_connected : AllConnected Q q
  quotient_respects : QuotientRespects Q q

/-- Listwise alignment of `Good` witnesses. -/
inductive GoodList (Q : SimpleGraph X) :
    List (RTree X) → List (IndexedQuotient X) → Prop where
  | nil : GoodList Q [] []
  | cons {t : RTree X} {q : IndexedQuotient X}
      {ts : List (RTree X)} {qs : List (IndexedQuotient X)} :
      Good Q t q → GoodList Q ts qs → GoodList Q (t :: ts) (q :: qs)

namespace GoodList

/-- Look up the aligned input subtree and its structural witness. -/
theorem exists_of_mem_right {Q : SimpleGraph X} {ts : List (RTree X)}
    {qs : List (IndexedQuotient X)} (h : GoodList Q ts qs)
    {q : IndexedQuotient X} (hq : q ∈ qs) :
    ∃ t ∈ ts, Good Q t q := by
  induction h with
  | nil => simp at hq
  | @cons t q₀ ts qs hgood hrest ih =>
      rw [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨t, by simp, hgood⟩
      · obtain ⟨s, hs, hsq⟩ := ih hq
        exact ⟨s, by simp [hs], hsq⟩

end GoodList

private theorem partition_good_node {Q : SimpleGraph X}
    {t : RTree X} {cluster : List X} {boundary : List (RTree X)}
    {children : List (IndexedQuotient X)}
    (hsplit : RootSplit t cluster boundary) (_hparts : PartitionList boundary children)
    (ihparts : (∀ s ∈ boundary, Respects Q s) → GoodList Q boundary children) :
    Respects Q t → Good Q t (.node cluster children) := by
  intro ht
  have hgoodList := ihparts (hsplit.boundary_respects ht)
  refine ⟨?_, ?_, ?_⟩
  · cases hsplit
    simp [rootLabel, rootCluster]
  · rw [AllConnected]
    refine ⟨hsplit.cluster_connected ht, ?_⟩
    intro child hchild
    obtain ⟨s, _hs, hgood⟩ := hgoodList.exists_of_mem_right hchild
    exact hgood.all_connected
  · rw [QuotientRespects]
    constructor
    · intro child hchild
      obtain ⟨s, hs, hgood⟩ := hgoodList.exists_of_mem_right hchild
      obtain ⟨u, hu, hua⟩ := hsplit.boundary_attached ht s hs
      exact ⟨u, hu, rootLabel s, hgood.root_mem, hua⟩
    · intro child hchild
      obtain ⟨s, _hs, hgood⟩ := hgoodList.exists_of_mem_right hchild
      exact hgood.quotient_respects

private theorem partition_good_contractFirst {Q : SimpleGraph X}
    {t : RTree X} {cluster₁ cluster₂ : List X}
    {grandchildren siblings : List (IndexedQuotient X)}
    (_hprev : IsPartition t (.node cluster₁ (.node cluster₂ grandchildren :: siblings)))
    (ihprev : Respects Q t →
      Good Q t (.node cluster₁ (.node cluster₂ grandchildren :: siblings))) :
    Respects Q t →
      Good Q t (.node (cluster₁ ++ cluster₂) (grandchildren ++ siblings)) := by
  intro ht
  have hgood := ihprev ht
  have hall := hgood.all_connected
  rw [AllConnected] at hall
  rcases hall with ⟨hconn₁, hallChildren⟩
  have hgood₂ := hallChildren (.node cluster₂ grandchildren) (by simp)
  rw [AllConnected] at hgood₂
  rcases hgood₂ with ⟨hconn₂, hallGrandchildren⟩
  have hqrespect := hgood.quotient_respects
  rw [QuotientRespects] at hqrespect
  rcases hqrespect with ⟨hedges₁, hrespectChildren⟩
  obtain ⟨u, hu, v, hv, huv⟩ :=
    hedges₁ (.node cluster₂ grandchildren) (by simp)
  have hrespect₂ := hrespectChildren (.node cluster₂ grandchildren) (by simp)
  rw [QuotientRespects] at hrespect₂
  rcases hrespect₂ with ⟨hedges₂, hrespectGrandchildren⟩
  have hmergedConn :=
    SimpleGraph.induce_connected_adj_union hconn₁ hconn₂ hu hv huv
  have hset : ({x : X | x ∈ cluster₁} ∪ {x : X | x ∈ cluster₂}) =
      {x : X | x ∈ cluster₁ ++ cluster₂} := by
    ext x
    simp
  rw [hset] at hmergedConn
  refine ⟨?_, ?_, ?_⟩
  · exact List.mem_append_left _ hgood.root_mem
  · rw [AllConnected]
    refine ⟨hmergedConn, ?_⟩
    intro child hchild
    rw [List.mem_append] at hchild
    rcases hchild with hchild | hchild
    · exact hallGrandchildren child hchild
    · exact hallChildren child (by simp [hchild])
  · rw [QuotientRespects]
    constructor
    · intro child hchild
      rw [List.mem_append] at hchild
      rcases hchild with hchild | hchild
      · obtain ⟨a, ha, b, hb, hab⟩ := hedges₂ child hchild
        exact ⟨a, List.mem_append_right _ ha, b, hb, hab⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := hedges₁ child (by simp [hchild])
        exact ⟨a, List.mem_append_left _ ha, b, hb, hab⟩
    · intro child hchild
      rw [List.mem_append] at hchild
      rcases hchild with hchild | hchild
      · exact hrespectGrandchildren child hchild
      · exact hrespectChildren child (by simp [hchild])

private theorem partition_good_nil {Q : SimpleGraph X} :
    (∀ t ∈ ([] : List (RTree X)), Respects Q t) → GoodList Q [] [] := by
  exact fun _ ↦ .nil

private theorem partition_good_cons {Q : SimpleGraph X}
    {t : RTree X} {q : IndexedQuotient X}
    {ts : List (RTree X)} {qs : List (IndexedQuotient X)}
    (_hfirst : IsPartition t q) (_hrest : PartitionList ts qs)
    (ihfirst : Respects Q t → Good Q t q)
    (ihrest : (∀ s ∈ ts, Respects Q s) → GoodList Q ts qs) :
    (∀ s ∈ t :: ts, Respects Q s) → GoodList Q (t :: ts) (q :: qs) := by
  intro hrespect
  exact .cons (ihfirst (hrespect t (by simp)))
    (ihrest fun s hs ↦ hrespect s (by simp [hs]))

/-- Every indexed partition cluster is connected, and its displayed quotient
edges are realized by original tree edges. -/
theorem IsPartition.good {Q : SimpleGraph X} {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q) (ht : Respects Q t) :
    Good Q t q :=
  (IsPartition.rec
    (motive_1 := fun t q _ ↦ Respects Q t → Good Q t q)
    (motive_2 := fun ts qs _ ↦
      (∀ s ∈ ts, Respects Q s) → GoodList Q ts qs)
    partition_good_node partition_good_contractFirst partition_good_nil
      partition_good_cons h) ht


/-! ### Occurrence type of quotient nodes -/

/-- A node occurrence in a rose tree.  Child indices distinguish repeated,
definitionally equal child trees. -/
inductive Node : (t : RTree X) → Type _ where
  | root {x : X} {children : List (RTree X)} : Node (.node x children)
  | child {x : X} {children : List (RTree X)} (i : Fin children.length) :
      Node (children.get i) → Node (.node x children)

namespace Node

/-- Root occurrence of a rose tree. -/
abbrev rootNode {x : X} {children : List (RTree X)} : Node (.node x children) :=
  .root

/-- Label at a node occurrence. -/
def label : {t : RTree X} → Node t → X
  | .node x _, .root => x
  | .node _ _, .child _ n => label n

/-- Depth of a node occurrence. -/
def depth : {t : RTree X} → Node t → ℕ
  | .node _ _, .root => 0
  | .node _ _, .child _ n => depth n + 1

/-- The label of an occurrence appears in the preorder label traversal. -/
theorem label_mem_vertices {t : RTree X} (n : Node t) :
    label n ∈ vertices t := by
  induction n with
  | root => simp [label, vertices]
  | @child x children i n ih =>
      simp only [vertices, List.mem_cons]
      right
      rw [List.mem_flatten]
      exact ⟨vertices (children.get i),
        List.mem_map.mpr ⟨children.get i, children.get_mem i, rfl⟩, ih⟩

/-- A node is either the root or a node of one indexed child subtree. -/
def nodeEquiv {x : X} {children : List (RTree X)} :
    Node (.node x children) ≃ (Unit ⊕ Σ i : Fin children.length, Node (children.get i)) where
  toFun
    | .root => Sum.inl ()
    | .child i n => Sum.inr ⟨i, n⟩
  invFun
    | Sum.inl _ => .root
    | Sum.inr p => .child p.1 p.2
  left_inv n := by cases n <;> rfl
  right_inv n := by
    rcases n with (_ | ⟨i, n⟩)
    · rfl
    · rfl

private theorem le_sum_map_of_mem {A : Type*} (f : A → ℕ) {a : A}
    {l : List A} (ha : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      simp only [List.map_cons, List.sum_cons]
      rcases ha with rfl | ha
      · omega
      · have := ih ha
        omega

/-- The occurrence type of a finite rose tree is finite. -/
noncomputable instance instFinite (t : RTree X) : Finite (Node t) := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | node x children =>
          have hchild (i : Fin children.length) :
              Finite (Node (children.get i)) := by
            apply ih (RTree.card (children.get i))
            · have hle : RTree.card (children.get i) ≤
                  (children.map RTree.card).sum :=
                le_sum_map_of_mem RTree.card (children.get_mem i)
              simp only [RTree.card] at hcard
              omega
            · rfl
          letI : ∀ i : Fin children.length, Finite (Node (children.get i)) := hchild
          exact Finite.of_injective nodeEquiv nodeEquiv.injective

/-- Node occurrences and entries of the preorder traversal have the same
finite cardinality. -/
theorem card_eq_length_vertices (t : RTree X) :
    Fintype.card (Node t) = (vertices t).length := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | node x children =>
          have hchild (i : Fin children.length) :
              Fintype.card (Node (children.get i)) =
                (vertices (children.get i)).length := by
            apply ih (RTree.card (children.get i))
            · have hle : RTree.card (children.get i) ≤
                  (children.map RTree.card).sum :=
                le_sum_map_of_mem RTree.card (children.get_mem i)
              simp only [RTree.card] at hcard
              omega
            · rfl
          rw [Fintype.card_congr nodeEquiv, Fintype.card_sum,
            Fintype.card_unit, Fintype.card_sigma]
          simp only [vertices, List.length_cons, List.length_flatten,
            List.map_map, Function.comp_def]
          simp_rw [hchild]
          have hsum :
              (∑ i : Fin children.length,
                (vertices (children.get i)).length) =
                (children.map fun child ↦ (vertices child).length).sum :=
            Fin.sum_univ_fun_getElem children
              (fun child ↦ (vertices child).length)
          rw [hsum]
          omega

/-- Every entry of the preorder traversal is the label of an occurrence. -/
theorem exists_node_of_mem_vertices {t : RTree X} {a : X}
    (ha : a ∈ vertices t) : ∃ n : Node t, label n = a := by
  induction hcard : RTree.card t using Nat.strong_induction_on generalizing t a with
  | h n ih =>
      cases t with
      | node x children =>
          simp only [vertices, List.mem_cons] at ha
          rcases ha with ha | ha
          · subst a
            exact ⟨.root, rfl⟩
          · rw [List.mem_flatten] at ha
            obtain ⟨labels, hlabels, ha⟩ := ha
            rw [List.mem_map] at hlabels
            obtain ⟨child, hchild, rfl⟩ := hlabels
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hchild
            subst child
            have hle : RTree.card (children.get i) ≤
                (children.map RTree.card).sum :=
              le_sum_map_of_mem RTree.card (children.get_mem i)
            have hlt : RTree.card (children.get i) < n := by
              simp only [RTree.card] at hcard
              omega
            obtain ⟨m, hm⟩ := ih _ hlt ha rfl
            exact ⟨.child i m, hm⟩

/-- If the preorder labels have no repetitions, occurrence labels are
injective. -/
theorem label_injective_of_vertices_nodup {t : RTree X}
    (ht : (vertices t).Nodup) :
    Function.Injective (@label X t) := by
  classical
  let f : Node t → {a : X // a ∈ vertices t} :=
    fun n ↦ ⟨label n, label_mem_vertices n⟩
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨n, hn⟩ := exists_node_of_mem_vertices a.property
    refine ⟨n, ?_⟩
    exact Subtype.ext hn
  have hcard : Fintype.card (Node t) =
      Fintype.card {a : X // a ∈ vertices t} := by
    calc
      Fintype.card (Node t) = (vertices t).length := card_eq_length_vertices t
      _ = (vertices t).toFinset.card :=
        (List.toFinset_card_of_nodup ht).symm
      _ = Fintype.card {a : X // a ∈ vertices t} := by
        symm
        apply Fintype.card_of_subtype (vertices t).toFinset
        intro a
        simp
  have hinj : Function.Injective f :=
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard⟩).1
  intro a b hab
  apply hinj
  exact Subtype.ext hab

/-- Parent occurrence; only the global root has no parent. -/
def parent : {t : RTree X} → Node t → Option (Node t)
  | .node _ _, .root => none
  | .node _ _, .child i n =>
      match parent n with
      | none => some .root
      | some p => some (.child i p)

@[simp]
theorem parent_root {x : X} {children : List (RTree X)} :
    parent (rootNode : Node (.node x children)) = none := rfl

/-- A parent step strictly decreases occurrence depth. -/
theorem depth_parent_lt {t : RTree X} {n p : Node t} (hp : parent n = some p) :
    depth p < depth n := by
  induction n with
  | root => simp [parent] at hp
  | @child x children i n ih =>
      simp only [parent] at hp
      split at hp
      · cases hp
        simp [depth]
      · rename_i p' hparent
        cases hp
        simp only [depth, Nat.add_lt_add_iff_right]
        exact ih hparent

/-- Only the root has no parent. -/
theorem parent_eq_none_iff {x : X} {children : List (RTree X)}
    (n : Node (.node x children)) : parent n = none ↔ n = .root := by
  cases n with
  | root => simp [parent]
  | child i n =>
      simp only [parent]
      split <;> simp

/-- Root occurrence, for a tree not syntactically exposed as a node. -/
def globalRoot : (t : RTree X) → Node t
  | .node _ _ => .root

theorem parent_eq_none_iff_root {t : RTree X} (n : Node t) :
    parent n = none ↔ n = globalRoot t := by
  cases t with
  | node x children => exact parent_eq_none_iff n

/-- Structural graph of node occurrences. -/
def graph (t : RTree X) : SimpleGraph (Node t) :=
  SimpleGraph.fromRel fun a b ↦ parent b = some a

/-- Embed occurrences of an indexed child subtree into the ambient rose tree. -/
def childEmbedding {x : X} {children : List (RTree X)}
    (i : Fin children.length) :
    Node (children.get i) ↪ Node (.node x children) where
  toFun := .child i
  inj' := by
    intro a b h
    injection h

@[simp]
theorem childEmbedding_apply {x : X} {children : List (RTree X)}
    (i : Fin children.length) (n : Node (children.get i)) :
    childEmbedding i n = (.child i n : Node (.node x children)) := rfl

@[simp]
theorem parent_child_eq_child_iff {x : X} {children : List (RTree X)}
    (i : Fin children.length) (a b : Node (children.get i)) :
    parent (.child i b : Node (.node x children)) = some (.child i a) ↔
      parent b = some a := by
  simp only [parent]
  split
  · rename_i hnone
    simp [hnone]
  · simp_all

@[simp]
theorem parent_child_eq_root_iff {x : X} {children : List (RTree X)}
    (i : Fin children.length) (n : Node (children.get i)) :
    parent (.child i n : Node (.node x children)) = some .root ↔
      n = globalRoot (children.get i) := by
  simp only [parent]
  split
  · rename_i hnone
    simpa using (parent_eq_none_iff_root n).mp hnone
  · rename_i p hparent
    constructor
    · intro h
      have hp : (.child i p : Node (.node x children)) = .root :=
        Option.some.inj h
      cases hp
    · intro hn
      subst n
      have hnone : parent (globalRoot (children.get i)) = none :=
        (parent_eq_none_iff_root (globalRoot (children.get i))).mpr rfl
      rw [hnone] at hparent
      cases hparent

/-- The child embedding identifies the child's structural graph with the
induced adjacency relation on its occurrence image. -/
@[simp]
theorem graph_adj_childEmbedding_iff {x : X}
    {children : List (RTree X)} (i : Fin children.length)
    (a b : Node (children.get i)) :
    (graph (.node x children)).Adj (childEmbedding i a) (childEmbedding i b) ↔
      (graph (children.get i)).Adj a b := by
  change (graph (.node x children)).Adj (.child i a) (.child i b) ↔
    (graph (children.get i)).Adj a b
  rw [graph, graph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hpar⟩
    refine ⟨?_, ?_⟩
    · intro hab
      apply hne
      rw [hab]
    · rcases hpar with hpar | hpar
      · exact Or.inl ((parent_child_eq_child_iff i a b).mp hpar)
      · exact Or.inr ((parent_child_eq_child_iff i b a).mp hpar)
  · rintro ⟨hne, hpar⟩
    refine ⟨?_, ?_⟩
    · intro hab
      exact hne ((childEmbedding i).injective hab)
    · rcases hpar with hpar | hpar
      · exact Or.inl ((parent_child_eq_child_iff i a b).mpr hpar)
      · exact Or.inr ((parent_child_eq_child_iff i b a).mpr hpar)

/-- The ambient root is adjacent to a wrapped child occurrence exactly at
the root occurrence of that child subtree. -/
@[simp]
theorem graph_adj_root_child_iff {x : X}
    {children : List (RTree X)} (i : Fin children.length)
    (n : Node (children.get i)) :
    (graph (.node x children)).Adj .root (childEmbedding i n) ↔
      n = globalRoot (children.get i) := by
  change (graph (.node x children)).Adj .root (.child i n) ↔
    n = globalRoot (children.get i)
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_hne, hpar | hpar⟩
    · exact (parent_child_eq_root_iff i n).mp hpar
    · simp [parent] at hpar
  · intro hn
    refine ⟨?_, Or.inl ((parent_child_eq_root_iff i n).mpr hn)⟩
    intro h
    cases h

/-- A parent occurrence is adjacent to its child occurrence. -/
theorem graph_adj_parent {t : RTree X} {n p : Node t} (hp : parent n = some p) :
    (graph t).Adj p n := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl hp⟩
  intro hpn
  subst p
  exact (lt_irrefl _ (depth_parent_lt hp))

/-- The root reaches every occurrence in the structural graph. -/
theorem graph_root_reachable (t : RTree X) (n : Node t) :
    (graph t).Reachable (globalRoot t) n := by
  apply (measure depth).wf.induction n
  intro n ih
  cases hp : parent n with
  | none =>
      have hn : n = globalRoot t := (parent_eq_none_iff_root n).mp hp
      subst n
      exact .rfl
  | some p =>
      exact (ih p (depth_parent_lt hp)).trans (graph_adj_parent hp).reachable

/-- The structural graph of a rose tree is connected. -/
theorem graph_connected (t : RTree X) : (graph t).Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable (graph t)).mpr
    ⟨globalRoot t, graph_root_reachable t⟩

/-- Edge selected by a non-root occurrence and its parent. -/
def parentEdge (t : RTree X) (n : Node t) : Sym2 (Node t) :=
  s((parent n).getD (globalRoot t), n)

/-- Non-root node occurrences. -/
def nonRoots (t : RTree X) : Finset (Node t) :=
  Finset.univ.erase (globalRoot t)

/-- Every structural edge is generated by some non-root occurrence. -/
theorem edgeFinset_subset_parentEdges (t : RTree X) :
    (graph t).edgeFinset ⊆ (nonRoots t).image (parentEdge t) := by
  classical
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeSet, graph, SimpleGraph.fromRel_adj] at he
      rcases he.2 with hp | hp
      · have hbroot : b ≠ globalRoot t := by
          intro hb
          subst b
          have hnone : parent (globalRoot t) = none :=
            (parent_eq_none_iff_root (globalRoot t)).mpr rfl
          rw [hnone] at hp
          cases hp
        rw [Finset.mem_image]
        refine ⟨b, by simp [nonRoots, hbroot], ?_⟩
        simp [parentEdge, hp]
      · have haroot : a ≠ globalRoot t := by
          intro ha
          subst a
          have hnone : parent (globalRoot t) = none :=
            (parent_eq_none_iff_root (globalRoot t)).mpr rfl
          rw [hnone] at hp
          cases hp
        rw [Finset.mem_image]
        refine ⟨a, by simp [nonRoots, haroot], ?_⟩
        simp [parentEdge, hp, Sym2.eq_swap]

/-- The structural graph has at most `|Node|-1` edges. -/
theorem card_edgeFinset_le (t : RTree X) :
    (graph t).edgeFinset.card ≤ Fintype.card (Node t) - 1 := by
  classical
  calc
    (graph t).edgeFinset.card ≤ ((nonRoots t).image (parentEdge t)).card :=
      Finset.card_le_card (edgeFinset_subset_parentEdges t)
    _ ≤ (nonRoots t).card := Finset.card_image_le
    _ = Fintype.card (Node t) - 1 := by
      rw [nonRoots, Finset.card_erase_of_mem (Finset.mem_univ (globalRoot t)),
        Finset.card_univ]

/-- The structural graph of every finite rose tree is a mathlib tree. -/
theorem graph_isTree (t : RTree X) : (graph t).IsTree := by
  have hconn := graph_connected t
  have hlower : Fintype.card (Node t) ≤ (graph t).edgeFinset.card + 1 := by
    have h := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← (graph t).edgeFinset_card] at h
    exact h
  have hupper := card_edgeFinset_le t
  have hpos : 0 < Fintype.card (Node t) := Fintype.card_pos_iff.mpr ⟨globalRoot t⟩
  have heq : (graph t).edgeFinset.card + 1 = Fintype.card (Node t) := by omega
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← (graph t).edgeFinset_card]
  exact heq

/-! ### Degree bounds for occurrence graphs -/

/-- Number of immediate rose-tree children below an occurrence. -/
def childCount : {t : RTree X} → Node t → ℕ
  | .node _ children, .root => children.length
  | .node _ _, .child _ n => childCount n

/-- Uniform bound on the child-list length at every rose-tree node. -/
def AllChildrenCardLE (b : ℕ) : RTree X → Prop
  | .node _ children =>
      children.length ≤ b ∧ ∀ child ∈ children, AllChildrenCardLE b child

/-- The local child count at any occurrence inherits a global rose-tree child
bound. -/
theorem childCount_le_of_allChildrenCardLE {b : ℕ} {t : RTree X}
    (h : AllChildrenCardLE b t) (n : Node t) : childCount n ≤ b := by
  induction n with
  | @root x children =>
      rw [AllChildrenCardLE] at h
      exact h.1
  | @child x children i n ih =>
      rw [AllChildrenCardLE] at h
      exact ih (h.2 (children.get i) (children.get_mem i))

/-- Occurrences whose parent is `n`. -/
def childrenOf {t : RTree X} (n : Node t) : Finset (Node t) :=
  Finset.univ.filter fun m ↦ parent m = some n

@[simp]
theorem parent_globalRoot (t : RTree X) : parent (globalRoot t) = none := by
  cases t
  rfl

/-- Top-level child index of an occurrence, when it is not the root. -/
def topIndex {x : X} {children : List (RTree X)} :
    Node (.node x children) → Option (Fin children.length)
  | .root => none
  | .child i _ => some i

/-- Immediate root children, packaged in the parent fiber. -/
def rootChild {x : X} {children : List (RTree X)}
    (i : Fin children.length) :
    {m : Node (.node x children) // parent m = some (.root : Node (.node x children))} :=
  ⟨.child i (globalRoot (children.get i)), by simp [parent]⟩

theorem rootChild_bijective {x : X} {children : List (RTree X)} :
    Function.Bijective (@rootChild X x children) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have htop := congrArg (@topIndex X x children)
      (congrArg Subtype.val hij)
    have hij' : i = j := Option.some.inj
      (by simpa [rootChild, topIndex] using htop)
    exact congrArg Fin.val hij'
  · intro m
    rcases m with ⟨m, hm⟩
    cases m with
    | root => simp [parent] at hm
    | child i n =>
        simp only [parent] at hm
        split at hm
        · rename_i hnone
          have hn : n = globalRoot (children.get i) :=
            (parent_eq_none_iff_root n).mp hnone
          subst n
          refine ⟨i, ?_⟩
          apply Subtype.ext
          rfl
        · cases hm

/-- Wrap a local child-parent fiber into the corresponding occurrence of an
ambient child subtree. -/
def wrapChild {x : X} {children : List (RTree X)}
    (i : Fin children.length) (n : Node (children.get i))
    (m : {m : Node (children.get i) // parent m = some n}) :
    {m : Node (.node x children) // parent m = some (.child i n)} :=
  ⟨.child i m.val, by simp [parent, m.property]⟩

theorem wrapChild_bijective {x : X} {children : List (RTree X)}
    (i : Fin children.length) (n : Node (children.get i)) :
    Function.Bijective (@wrapChild X x children i n) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have hval := congrArg Subtype.val hab
    simp only [wrapChild] at hval
    injection hval
  · intro m
    rcases m with ⟨m, hm⟩
    cases m with
    | root => simp [parent] at hm
    | child j k =>
        simp only [parent] at hm
        split at hm
        · cases hm
        · rename_i p hp
          cases hm
          refine ⟨⟨k, hp⟩, ?_⟩
          apply Subtype.ext
          rfl

/-- The number of occurrences directly below `n` is its local rose-tree child
count. -/
theorem parentFiber_card_eq_childCount {t : RTree X} (n : Node t) :
    Fintype.card {m : Node t // parent m = some n} = childCount n := by
  induction n with
  | @root x children =>
      calc
        Fintype.card {m : Node (.node x children) //
            parent m = some (.root : Node (.node x children))} =
            Fintype.card (Fin children.length) :=
          Fintype.card_congr (Equiv.ofBijective
            (@rootChild X x children) rootChild_bijective).symm
        _ = childCount (.root : Node (.node x children)) := by
          simp [childCount]
  | @child x children i n ih =>
      calc
        Fintype.card {m : Node (.node x children) //
            parent m = some (.child i n)} =
            Fintype.card {m : Node (children.get i) // parent m = some n} :=
          Fintype.card_congr (Equiv.ofBijective (wrapChild i n)
            (@wrapChild_bijective X x children i n)).symm
        _ = childCount (.child i n : Node (.node x children)) := ih

theorem childrenOf_card {t : RTree X} (n : Node t) :
    (childrenOf n).card = childCount n := by
  have hcard : Fintype.card {m : Node t // parent m = some n} =
      (childrenOf n).card := by
    apply Fintype.card_of_subtype (childrenOf n)
    intro m
    simp [childrenOf]
  rw [← hcard]
  exact parentFiber_card_eq_childCount n

/-- Every graph neighbor is either an immediate child occurrence or the one
parent occurrence. -/
theorem neighborFinset_subset_childrenOf_insert_parent {t : RTree X}
    (n : Node t) :
    (graph t).neighborFinset n ⊆
      insert ((parent n).getD (globalRoot t)) (childrenOf n) := by
  intro m hm
  rw [SimpleGraph.mem_neighborFinset, graph, SimpleGraph.fromRel_adj] at hm
  rcases hm.2 with hm | hm
  · rw [Finset.mem_insert]
    exact Or.inr (by simp [childrenOf, hm])
  · rw [Finset.mem_insert]
    left
    simp [hm]

/-- If every rose-tree node has at most `b` children, its occurrence graph has
maximum degree at most `b+1` (one possible parent plus `b` children). -/
theorem graph_degree_le_succ {b : ℕ} {t : RTree X}
    (h : AllChildrenCardLE b t) (n : Node t) :
    (graph t).degree n ≤ b + 1 := by
  rw [SimpleGraph.degree]
  calc
    ((graph t).neighborFinset n).card ≤
        (insert ((parent n).getD (globalRoot t)) (childrenOf n)).card :=
      Finset.card_le_card (neighborFinset_subset_childrenOf_insert_parent n)
    _ ≤ (childrenOf n).card + 1 :=
      Finset.card_insert_le ((parent n).getD (globalRoot t)) (childrenOf n)
    _ = childCount n + 1 := by rw [childrenOf_card]
    _ ≤ b + 1 := Nat.add_le_add_right (childCount_le_of_allChildrenCardLE h n) 1

end Node

/-! ### Nonempty clusters and canonical cluster occurrences -/

/-- Every quotient cluster is nonempty. -/
def AllNonempty : IndexedQuotient X → Prop
  | .node cluster children =>
      cluster ≠ [] ∧ ∀ child ∈ children, AllNonempty child

private theorem partition_nonempty_node {t : RTree X} {cluster : List X}
    {boundary : List (RTree X)} {children : List (IndexedQuotient X)}
    (hsplit : RootSplit t cluster boundary)
    (_hparts : PartitionList boundary children)
    (ihparts : ∀ q ∈ children, AllNonempty q) :
    AllNonempty (.node cluster children) := by
  rw [AllNonempty]
  constructor
  · cases hsplit
    simp
  · exact ihparts

private theorem partition_nonempty_contractFirst {t : RTree X}
    {cluster₁ cluster₂ : List X}
    {grandchildren siblings : List (IndexedQuotient X)}
    (_hprev : IsPartition t
      (.node cluster₁ (.node cluster₂ grandchildren :: siblings)))
    (ihprev : AllNonempty
      (.node cluster₁ (.node cluster₂ grandchildren :: siblings))) :
    AllNonempty (.node (cluster₁ ++ cluster₂)
      (grandchildren ++ siblings)) := by
  rw [AllNonempty] at ihprev ⊢
  rcases ihprev with ⟨hcluster₁, hchildren⟩
  have hfirst := hchildren (.node cluster₂ grandchildren) (by simp)
  rw [AllNonempty] at hfirst
  rcases hfirst with ⟨_hcluster₂, hgrandchildren⟩
  constructor
  · intro happ
    cases cluster₁ with
    | nil => exact hcluster₁ rfl
    | cons x xs => simp at happ
  · intro child hchild
    rw [List.mem_append] at hchild
    rcases hchild with hchild | hchild
    · exact hgrandchildren child hchild
    · exact hchildren child (by simp [hchild])

private theorem partition_nonempty_cons {t : RTree X}
    {q : IndexedQuotient X} {ts : List (RTree X)}
    {qs : List (IndexedQuotient X)}
    (_hfirst : IsPartition t q) (_hrest : PartitionList ts qs)
    (ihfirst : AllNonempty q)
    (ihrest : ∀ q' ∈ qs, AllNonempty q') :
    ∀ q' ∈ q :: qs, AllNonempty q' := by
  intro q' hq'
  rw [List.mem_cons] at hq'
  rcases hq' with rfl | hq'
  · exact ihfirst
  · exact ihrest q' hq'

/-- Every cluster produced by an indexed partition is nonempty. -/
theorem IsPartition.allNonempty {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) : AllNonempty q :=
  IsPartition.rec
    (motive_1 := fun _ q _ ↦ AllNonempty q)
    (motive_2 := fun _ qs _ ↦ ∀ q ∈ qs, AllNonempty q)
    partition_nonempty_node partition_nonempty_contractFirst
    (by simp) partition_nonempty_cons h

namespace Node

/-- Nonemptiness specialized to any quotient-node occurrence. -/
theorem label_nonempty_of_allNonempty {q : IndexedQuotient X}
    (h : AllNonempty q) (n : Node q) : label n ≠ [] := by
  induction n with
  | @root cluster children =>
      rw [AllNonempty] at h
      exact h.1
  | @child cluster children i n ih =>
      rw [AllNonempty] at h
      exact ih (h.2 (children.get i) (children.get_mem i))

end Node

/-- If the concatenation of a list of nonempty lists has no repetitions, then
the outer list has no repetitions as well. -/
private theorem nodup_of_flatten_nodup_of_nonempty
    {lists : List (List X)} (hflat : lists.flatten.Nodup)
    (hne : ∀ l ∈ lists, l ≠ []) : lists.Nodup := by
  induction lists with
  | nil => simp
  | cons l lists ih =>
      rw [List.flatten_cons] at hflat
      rw [List.nodup_cons]
      constructor
      · intro hl
        have hlne := hne l (by simp)
        obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hlne
        have hx : x ∈ x :: xs := by simp
        have hxin : x ∈ lists.flatten := by
          rw [List.mem_flatten]
          exact ⟨x :: xs, hl, hx⟩
        exact (List.disjoint_of_nodup_append hflat) hx hxin
      · exact ih hflat.of_append_right
          (fun s hs ↦ hne s (by simp [hs]))

/-- Cluster lists themselves occur only once in an indexed partition whose
input labels occur only once. -/
theorem IsPartition.clusterLists_nodup {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) : (clusterLists q).Nodup := by
  apply nodup_of_flatten_nodup_of_nonempty (h.flattenClusters_nodup ht)
  intro cluster hcluster
  obtain ⟨n, hn⟩ := Node.exists_node_of_mem_vertices hcluster
  rw [← hn]
  exact Node.label_nonempty_of_allNonempty h.allNonempty n

/-- Every input label lies in the label list of some quotient occurrence. -/
theorem IsPartition.exists_node_mem {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    {x : X} (hx : x ∈ vertices t) :
    ∃ n : Node q, x ∈ Node.label n := by
  have hxq : x ∈ flattenClusters q := h.perm_vertices.mem_iff.mpr hx
  rw [flattenClusters, List.mem_flatten] at hxq
  obtain ⟨cluster, hcluster, hxcluster⟩ := hxq
  obtain ⟨n, hn⟩ := Node.exists_node_of_mem_vertices hcluster
  exact ⟨n, hn.symm ▸ hxcluster⟩

/-- Under input-label uniqueness, an input label belongs to exactly one
quotient occurrence. -/
theorem IsPartition.node_unique_of_mem {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) {x : X} {a b : Node q}
    (ha : x ∈ Node.label a) (hb : x ∈ Node.label b) : a = b := by
  have hflat := h.flattenClusters_nodup ht
  have houter := h.clusterLists_nodup ht
  have hlabelInj := Node.label_injective_of_vertices_nodup houter
  by_contra hab
  have hlabelsNe : Node.label a ≠ Node.label b := by
    intro heq
    exact hab (hlabelInj heq)
  have hpair : (clusterLists q).Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hflat).2
  have hdisjoint := hpair.forall (fun _ _ hd ↦ hd.symm)
    (Node.label_mem_vertices a) (Node.label_mem_vertices b) hlabelsNe
  exact (List.disjoint_left.mp hdisjoint) ha hb

/-- Canonical quotient occurrence containing an input label. -/
def clusterNode {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (x : X) (hx : x ∈ vertices t) : Node q :=
  Classical.choose (h.exists_node_mem hx)

theorem clusterNode_mem {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (x : X) (hx : x ∈ vertices t) :
    x ∈ Node.label (clusterNode h x hx) :=
  Classical.choose_spec (h.exists_node_mem hx)

/-- Membership characterizes the canonical cluster occurrence. -/
theorem clusterNode_eq_iff_mem {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (ht : (vertices t).Nodup)
    (x : X) (hx : x ∈ vertices t) (n : Node q) :
    clusterNode h x hx = n ↔ x ∈ Node.label n := by
  constructor
  · intro hn
    subst n
    exact clusterNode_mem h x hx
  · intro hmem
    exact h.node_unique_of_mem ht (clusterNode_mem h x hx) hmem

/-! ### Structural facts at arbitrary quotient occurrences -/

namespace Node

/-- Connectivity specialized to the cluster at an arbitrary occurrence. -/
theorem connected_of_allConnected {Q : SimpleGraph X}
    {q : IndexedQuotient X} (h : AllConnected Q q) (n : Node q) :
    (Q.induce {x | x ∈ label n}).Connected := by
  induction n with
  | @root cluster children =>
      rw [AllConnected] at h
      exact h.1
  | @child cluster children i n ih =>
      rw [AllConnected] at h
      exact ih (h.2 (children.get i) (children.get_mem i))

end Node

mutual

/-- Look up weight bounds in an aligned quotient forest. -/
theorem weightsInList_get {w : X → ℕ} {lower upper : ℕ}
    {qs : List (IndexedQuotient X)} (h : WeightsInList w lower upper qs)
    (i : Fin qs.length) : WeightsIn w lower upper (qs.get i) := by
  cases qs with
  | nil => exact Fin.elim0 i
  | cons q qs =>
      cases h with
      | cons hq hqs =>
          cases i using Fin.cases with
          | zero => exact hq
          | succ i => exact weightsInList_get hqs i

end

namespace Node

@[simp]
theorem label_globalRoot_eq_rootCluster (q : IndexedQuotient X) :
    label (globalRoot q) = rootCluster q := by
  cases q
  rfl

/-- Weight bounds specialized to the cluster at an arbitrary occurrence. -/
theorem weight_bounds_of_weightsIn {w : X → ℕ} {lower upper : ℕ}
    {q : IndexedQuotient X} (h : WeightsIn w lower upper q)
    (n : Node q) :
    lower ≤ clusterWeight w (label n) ∧
      clusterWeight w (label n) ≤ upper := by
  induction n with
  | @root cluster children =>
      cases h with
      | node hl hu _ => exact ⟨hl, hu⟩
  | @child cluster children i n ih =>
      cases h with
      | node _ _ hchildren =>
          exact ih (weightsInList_get hchildren i)

/-- A quotient parent edge is realized by an original graph edge between the
two retained cluster lists. -/
theorem realized_of_parent {Q : SimpleGraph X} {q : IndexedQuotient X}
    (h : QuotientRespects Q q) {n p : Node q}
    (hp : parent n = some p) :
    ∃ u ∈ label p, ∃ v ∈ label n, Q.Adj u v := by
  induction n with
  | root => simp [parent] at hp
  | @child cluster children i n ih =>
      rw [QuotientRespects] at h
      simp only [parent] at hp
      split at hp
      · rename_i hnone
        have hn : n = globalRoot (children.get i) :=
          (parent_eq_none_iff_root n).mp hnone
        subst n
        cases hp
        obtain ⟨u, hu, v, hv, huv⟩ :=
          h.1 (children.get i) (children.get_mem i)
        have hv' : v ∈ label (globalRoot (children.get i)) := by
          rwa [label_globalRoot_eq_rootCluster]
        exact ⟨u, hu, v, hv', huv⟩
      · rename_i p' hsome
        cases hp
        exact ih (h.2 (children.get i) (children.get_mem i)) hsome

/-- Every displayed structural quotient edge is realized by an original edge
between its endpoint cluster lists. -/
theorem realized_of_graph_adj {Q : SimpleGraph X} {q : IndexedQuotient X}
    (h : QuotientRespects Q q) {a b : Node q}
    (hab : (graph q).Adj a b) :
    ∃ x ∈ label a, ∃ y ∈ label b, Q.Adj x y := by
  rw [graph, SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with hp | hp
  · exact realized_of_parent h hp
  · obtain ⟨y, hy, x, hx, hyx⟩ := realized_of_parent h hp
    exact ⟨x, hx, y, hy, hyx.symm⟩

end Node

/-! ### The graph-tree encoding respects original adjacency -/

/-- Every parent-child edge of the rooted encoding is an original graph edge. -/
theorem labeledTree_respects [Fintype X] {Q : SimpleGraph X}
    (hQ : Q.IsTree) (r x : X) : Respects Q (labeledTree hQ r x) := by
  induction x using (farther_wellFounded hQ r).induction with
  | h x ih =>
      rw [labeledTree_eq, Respects]
      constructor
      · intro child hchild
        rw [List.mem_map] at hchild
        obtain ⟨y, _hy, rfl⟩ := hchild
        have hroot : rootLabel (labeledTree hQ r y.val) = y.val := by
          rw [labeledTree_eq]
          rfl
        rw [hroot]
        exact adj_of_mem_children hQ r x y.val y.property
      · intro child hchild
        rw [List.mem_map] at hchild
        obtain ⟨y, _hy, rfl⟩ := hchild
        apply ih y.val
        change height hQ r x < height hQ r y.val
        exact height_lt_of_mem_children hQ r x y.val y.property

/-! ### Finite indexing of the retained quotient -/

variable [Fintype X]

/-- Canonical finite numbering of quotient-node occurrences. -/
def occurrenceEquiv (q : IndexedQuotient X) :
    Node q ≃ Fin (Fintype.card (Node q)) :=
  Fintype.equivFin _

/-- Cluster assignment obtained from the unique retained cluster containing
each input label. -/
def finiteClusterOf {t : RTree X} {q : IndexedQuotient X}
    (h : IsPartition t q) (hcover : ∀ x : X, x ∈ vertices t) :
    X → Fin (Fintype.card (Node q)) :=
  fun x ↦ occurrenceEquiv q (clusterNode h x (hcover x))

/-- The structural quotient graph, transported to its canonical `Fin`
indexing. -/
def finiteQuotient (q : IndexedQuotient X) :
    SimpleGraph (Fin (Fintype.card (Node q))) :=
  (Node.graph q).comap (occurrenceEquiv q).symm

omit [Fintype X] in
/-- Transporting the structural occurrence graph preserves the tree
property. -/
theorem finiteQuotient_isTree (q : IndexedQuotient X) :
    (finiteQuotient q).IsTree := by
  exact ((SimpleGraph.Iso.comap (occurrenceEquiv q).symm
    (Node.graph q)).isTree_iff).mpr (Node.graph_isTree q)

omit [Fintype X] in
/-- Every retained quotient occurrence receives a finite cluster index. -/
theorem finiteClusterOf_surjective {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t) :
    Function.Surjective (finiteClusterOf h hcover) := by
  intro i
  let n : Node q := (occurrenceEquiv q).symm i
  have hnne : Node.label n ≠ [] :=
    Node.label_nonempty_of_allNonempty h.allNonempty n
  cases hlabel : Node.label n with
  | nil => exact (hnne hlabel).elim
  | cons x xs =>
      refine ⟨x, ?_⟩
      have hxmem : x ∈ Node.label n := by simp [hlabel]
      have hnode : clusterNode h x (hcover x) = n :=
        (clusterNode_eq_iff_mem h ht x (hcover x) n).mpr hxmem
      simp [finiteClusterOf, hnode, n]

omit [Fintype X] in
/-- The finite-index fiber is exactly the label set of the corresponding
quotient occurrence. -/
theorem finiteClusterOf_fiber {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t)
    (i : Fin (Fintype.card (Node q))) :
    {x : X | finiteClusterOf h hcover x = i} =
      {x : X | x ∈ Node.label ((occurrenceEquiv q).symm i)} := by
  ext x
  simp only [Set.mem_setOf_eq, finiteClusterOf]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  exact clusterNode_eq_iff_mem h ht x (hcover x) _

omit [Fintype X] in
/-- Connected retained cluster lists become connected finite-index fibers. -/
theorem finiteClusterOf_connected {Q : SimpleGraph X} {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t)
    (hgood : Good Q t q) (i : Fin (Fintype.card (Node q))) :
    (Q.induce {x : X | finiteClusterOf h hcover x = i}).Connected := by
  rw [finiteClusterOf_fiber h ht hcover i]
  exact Node.connected_of_allConnected hgood.all_connected _

omit [Fintype X] in
/-- Every displayed finite quotient edge is realized by an original edge
crossing its two indexed fibers. -/
theorem finiteQuotient_adj_forward {Q : SimpleGraph X} {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t)
    (hgood : Good Q t q) {i j : Fin (Fintype.card (Node q))}
    (hij : (finiteQuotient q).Adj i j) :
    i ≠ j ∧ ∃ x y : X,
      Q.Adj x y ∧ finiteClusterOf h hcover x = i ∧
        finiteClusterOf h hcover y = j := by
  have hnodeAdj : (Node.graph q).Adj
      ((occurrenceEquiv q).symm i) ((occurrenceEquiv q).symm j) := hij
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Node.realized_of_graph_adj hgood.quotient_respects hnodeAdj
  refine ⟨hij.ne, x, y, hxy, ?_, ?_⟩
  · rw [finiteClusterOf]
    have hnode := (clusterNode_eq_iff_mem h ht x (hcover x)
      ((occurrenceEquiv q).symm i)).mpr hx
    rw [hnode, Equiv.apply_symm_apply]
  · rw [finiteClusterOf]
    have hnode := (clusterNode_eq_iff_mem h ht y (hcover y)
      ((occurrenceEquiv q).symm j)).mpr hy
    rw [hnode, Equiv.apply_symm_apply]

/-! ### Exact quotients of finite trees by connected fibers -/

namespace TreeConnectedQuotient

variable {I : Type*} [Fintype I]

/-- Vertex fiber of a proposed quotient map. -/
def fiber (f : X → I) (i : I) : Set X := {x | f x = i}

/-- Original edges lying entirely in one fiber. -/
def fiberEdges (Q : SimpleGraph X) (f : X → I) (i : I) :
    Finset (Sym2 X) :=
  Q.edgeFinset ∩ (fiber f i).toFinset.sym2

/-- Union of all within-fiber edges. -/
def internalEdges (Q : SimpleGraph X) (f : X → I) : Finset (Sym2 X) :=
  Finset.univ.biUnion (fiberEdges Q f)

/-- Edges crossing between distinct fibers. -/
def crossEdges (Q : SimpleGraph X) (f : X → I) : Finset (Sym2 X) :=
  Q.edgeFinset \ internalEdges Q f

omit [Fintype I] in
theorem fiberEdges_card_eq (Q : SimpleGraph X) (f : X → I) (i : I) :
    (fiberEdges Q f i).card =
      (Q.induce (fiber f i)).edgeFinset.card := by
  classical
  rw [fiberEdges, ← Q.map_edgeFinset_induce, Finset.card_map]

theorem fiberEdges_pairwiseDisjoint (Q : SimpleGraph X) (f : X → I) :
    (Finset.univ : Finset I).toSet.PairwiseDisjoint (fiberEdges Q f) := by
  classical
  intro i _hi j _hj hij
  change Disjoint (fiberEdges Q f i) (fiberEdges Q f j)
  rw [Finset.disjoint_left]
  intro e hei hej
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [fiberEdges, Finset.mem_inter, Finset.mk_mem_sym2_iff,
        Set.mem_toFinset, fiber, Set.mem_setOf_eq] at hei hej
      exact hij (hei.2.1.symm.trans hej.2.1)

theorem internalEdges_subset (Q : SimpleGraph X) (f : X → I) :
    internalEdges Q f ⊆ Q.edgeFinset := by
  classical
  intro e he
  rw [internalEdges, Finset.mem_biUnion] at he
  obtain ⟨i, _hi, he⟩ := he
  exact (Finset.mem_inter.mp he).1

theorem mem_crossEdges_iff (Q : SimpleGraph X) (f : X → I)
    (e : Sym2 X) :
    e ∈ crossEdges Q f ↔
      e ∈ Q.edgeFinset ∧ ¬(e.map f).IsDiag := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp [crossEdges, internalEdges, fiberEdges, fiber, ne_comm]; aesop

/-- Connected fibers of a finite tree consume at least `|X|-|I|` internal
edges. -/
theorem card_sub_le_internalEdges (Q : SimpleGraph X) (f : X → I)
    (hconn : ∀ i : I, (Q.induce (fiber f i)).Connected)
    (hsurj : Function.Surjective f) :
    Fintype.card X - Fintype.card I ≤ (internalEdges Q f).card := by
  classical
  have hedge (i : I) :
      (fiber f i).toFinset.card - 1 ≤ (fiberEdges Q f i).card := by
    have hc := (hconn i).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← (Q.induce (fiber f i)).edgeFinset_card] at hc
    have hverts : Fintype.card {x : X // x ∈ fiber f i} =
        (fiber f i).toFinset.card := by
      apply Fintype.card_of_subtype (fiber f i).toFinset
      intro x
      simp
    rw [hverts, ← fiberEdges_card_eq Q f i] at hc
    omega
  have hsumFiber :
      (∑ i : I, (fiber f i).toFinset.card) = Fintype.card X := by
    simpa [fiber] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset X) (Finset.univ : Finset I) f)
  have hpos (i : I) : 0 < (fiber f i).toFinset.card := by
    obtain ⟨x, hx⟩ := hsurj i
    apply Finset.card_pos.mpr
    refine ⟨x, ?_⟩
    simp [fiber, hx]
  have hsumSub :
      (∑ i : I, ((fiber f i).toFinset.card - 1)) + Fintype.card I =
        Fintype.card X := by
    calc
      (∑ i : I, ((fiber f i).toFinset.card - 1)) + Fintype.card I =
          ∑ i : I, (((fiber f i).toFinset.card - 1) + 1) := by
        rw [show Fintype.card I = ∑ _i : I, 1 by simp,
          ← Finset.sum_add_distrib]
      _ = ∑ i : I, (fiber f i).toFinset.card := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Nat.sub_add_cancel (hpos i)
      _ = Fintype.card X := hsumFiber
  have hsumLe :
      (∑ i : I, ((fiber f i).toFinset.card - 1)) ≤
        ∑ i : I, (fiberEdges Q f i).card := by
    exact Finset.sum_le_sum fun i _ ↦ hedge i
  have hinternal : (internalEdges Q f).card =
      ∑ i : I, (fiberEdges Q f i).card := by
    rw [internalEdges, Finset.card_biUnion (fiberEdges_pairwiseDisjoint Q f)]
  rw [hinternal]
  omega

/-- A finite tree has at most `|I|-1` edges crossing a partition into
connected nonempty fibers. -/
theorem card_crossEdges_le (Q : SimpleGraph X) (hQ : Q.IsTree)
    (f : X → I) (hconn : ∀ i : I, (Q.induce (fiber f i)).Connected)
    (hsurj : Function.Surjective f) :
    (crossEdges Q f).card ≤ Fintype.card I - 1 := by
  classical
  have hinternal := card_sub_le_internalEdges Q f hconn hsurj
  have hcross : (crossEdges Q f).card =
      Q.edgeFinset.card - (internalEdges Q f).card := by
    rw [crossEdges, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (internalEdges_subset Q f)]
  have htreeCard := hQ.card_edgeFinset
  have hcardLe := Fintype.card_le_of_surjective f hsurj
  rw [hcross]
  omega

/-- Every displayed quotient edge has a chosen original crossing edge whose
endpoint-fiber pair is exactly that quotient edge. -/
theorem exists_liftedEdge {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    (e : H.edgeSet) :
    ∃ qe : Q.edgeSet,
      qe.val.map f = e.val ∧ qe.val ∈ crossEdges Q f := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
      have hij : H.Adj i j := by
        rwa [SimpleGraph.mem_edgeSet] at he
      obtain ⟨x, y, hxy, hx, hy⟩ := hforward hij
      let qe : Q.edgeSet := ⟨s(x, y), by
        rwa [SimpleGraph.mem_edgeSet]⟩
      refine ⟨qe, ?_, ?_⟩
      · simp [qe, hx, hy]
      · rw [mem_crossEdges_iff]
        refine ⟨by simpa [qe] using qe.property, ?_⟩
        simpa [qe, hx, hy, Sym2.mk_isDiag_iff] using hij.ne

/-- Choice of a crossing original edge above each displayed quotient edge. -/
noncomputable def liftedEdge {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    (e : H.edgeSet) : Q.edgeSet :=
  Classical.choose (exists_liftedEdge f hforward e)

theorem liftedEdge_map {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    (e : H.edgeSet) :
    (liftedEdge f hforward e).val.map f = e.val :=
  (Classical.choose_spec (exists_liftedEdge f hforward e)).1

theorem liftedEdge_mem_crossEdges {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    (e : H.edgeSet) :
    (liftedEdge f hforward e).val ∈ crossEdges Q f :=
  (Classical.choose_spec (exists_liftedEdge f hforward e)).2

/-- The chosen edge lift is injective because its image under `Sym2.map f`
recovers the displayed quotient edge. -/
theorem liftedEdge_injective {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j) :
    Function.Injective (liftedEdge f hforward) := by
  intro e₁ e₂ he
  apply Subtype.ext
  rw [← liftedEdge_map f hforward e₁,
    ← liftedEdge_map f hforward e₂, he]

/-- The chosen lift, regarded as a map into the finite set of all crossing
edges. -/
noncomputable def liftedCrossEdge {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j) :
    H.edgeSet → {e : Sym2 X // e ∈ crossEdges Q f} :=
  fun e ↦ ⟨(liftedEdge f hforward e).val,
    liftedEdge_mem_crossEdges f hforward e⟩

theorem liftedCrossEdge_injective {Q : SimpleGraph X} {H : SimpleGraph I}
    (f : X → I)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j) :
    Function.Injective (liftedCrossEdge f hforward) := by
  intro e₁ e₂ he
  apply liftedEdge_injective f hforward
  apply Subtype.ext
  have heval := congrArg
    (fun z : {e : Sym2 X // e ∈ crossEdges Q f} ↦ z.val) he
  exact heval

/-- A spanning tree of realized quotient edges exhausts all crossing edges of
the original tree. -/
theorem liftedCrossEdge_surjective {Q : SimpleGraph X} (hQ : Q.IsTree)
    {H : SimpleGraph I} (hH : H.IsTree) (f : X → I)
    (hconn : ∀ i : I, (Q.induce (fiber f i)).Connected)
    (hsurj : Function.Surjective f)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j) :
    Function.Surjective (liftedCrossEdge f hforward) := by
  classical
  have hlower : Fintype.card H.edgeSet ≤ (crossEdges Q f).card := by
    have hinj := liftedCrossEdge_injective f hforward
    have hc := Fintype.card_le_of_injective _ hinj
    have htarget : Fintype.card {e : Sym2 X // e ∈ crossEdges Q f} =
        (crossEdges Q f).card := by
      apply Fintype.card_of_subtype (crossEdges Q f)
      intro e
      rfl
    rwa [htarget] at hc
  have hupper := card_crossEdges_le Q hQ f hconn hsurj
  have hHcard := hH.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card] at hHcard
  have hcard : Fintype.card H.edgeSet =
      Fintype.card {e : Sym2 X // e ∈ crossEdges Q f} := by
    have htarget : Fintype.card {e : Sym2 X // e ∈ crossEdges Q f} =
        (crossEdges Q f).card := by
      apply Fintype.card_of_subtype (crossEdges Q f)
      intro e
      rfl
    rw [htarget]
    omega
  exact (liftedCrossEdge_injective f hforward).surjective_of_fintype
    (Fintype.equivOfCardEq hcard)

/-- Distinct crossing edges of the original tree cannot induce the same edge
between connected quotient fibers. -/
theorem cross_edge_eq_of_map_eq {Q : SimpleGraph X} (hQ : Q.IsTree)
    {H : SimpleGraph I} (hH : H.IsTree) (f : X → I)
    (hconn : ∀ i : I, (Q.induce (fiber f i)).Connected)
    (hsurj : Function.Surjective f)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    {e₁ e₂ : Sym2 X} (he₁ : e₁ ∈ crossEdges Q f)
    (he₂ : e₂ ∈ crossEdges Q f) (hmap : e₁.map f = e₂.map f) :
    e₁ = e₂ := by
  let ce₁ : {e : Sym2 X // e ∈ crossEdges Q f} := ⟨e₁, he₁⟩
  let ce₂ : {e : Sym2 X // e ∈ crossEdges Q f} := ⟨e₂, he₂⟩
  obtain ⟨a, ha⟩ := liftedCrossEdge_surjective hQ hH f hconn hsurj hforward ce₁
  obtain ⟨b, hb⟩ := liftedCrossEdge_surjective hQ hH f hconn hsurj hforward ce₂
  have halift : (liftedEdge f hforward a).val = e₁ :=
    congrArg Subtype.val ha
  have hblift : (liftedEdge f hforward b).val = e₂ :=
    congrArg Subtype.val hb
  have hab : a = b := by
    apply Subtype.ext
    calc
      a.val = (liftedEdge f hforward a).val.map f :=
        (liftedEdge_map f hforward a).symm
      _ = e₁.map f := congrArg (Sym2.map f) halift
      _ = e₂.map f := hmap
      _ = (liftedEdge f hforward b).val.map f :=
        congrArg (Sym2.map f) hblift.symm
      _ = b.val := liftedEdge_map f hforward b
  rw [← halift, ← hblift, hab]

/-- Exactness: any original edge whose endpoints lie in distinct connected
fibers is an edge of the realized tree quotient. -/
theorem adj_of_cross {Q : SimpleGraph X} (hQ : Q.IsTree)
    {H : SimpleGraph I} (hH : H.IsTree) (f : X → I)
    (hconn : ∀ i : I, (Q.induce (fiber f i)).Connected)
    (hsurj : Function.Surjective f)
    (hforward : ∀ ⦃i j : I⦄, H.Adj i j →
      ∃ x y : X, Q.Adj x y ∧ f x = i ∧ f y = j)
    {x y : X} (hxy : Q.Adj x y) (hne : f x ≠ f y) :
    H.Adj (f x) (f y) := by
  classical
  let qe : {e : Sym2 X // e ∈ crossEdges Q f} :=
    ⟨s(x, y), (mem_crossEdges_iff Q f _).mpr ⟨by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hxy, by simpa using hne⟩⟩
  obtain ⟨e, he⟩ := liftedCrossEdge_surjective hQ hH f hconn hsurj hforward qe
  have hmap := liftedEdge_map f hforward e
  have helift : (liftedEdge f hforward e).val = s(x, y) :=
    Subtype.ext_iff.mp he
  have hval : e.val = s(f x, f y) := by
    calc
      e.val = (liftedEdge f hforward e).val.map f := hmap.symm
      _ = s(x, y).map f := congrArg (Sym2.map f) helift
      _ = s(f x, f y) := Sym2.map_pair_eq f x y
  have heprop := e.property
  rw [hval] at heprop
  rw [SimpleGraph.mem_edgeSet] at heprop
  exact heprop

end TreeConnectedQuotient

/-- The structural quotient is extensionally the graph obtained by crossing
original tree edges between distinct finite-index fibers. -/
theorem finiteQuotient_adj_iff {Q : SimpleGraph X} (hQ : Q.IsTree)
    {t : RTree X} {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t)
    (hgood : Good Q t q) {i j : Fin (Fintype.card (Node q))} :
    (finiteQuotient q).Adj i j ↔
      i ≠ j ∧ ∃ x y : X,
        Q.Adj x y ∧ finiteClusterOf h hcover x = i ∧
          finiteClusterOf h hcover y = j := by
  constructor
  · exact finiteQuotient_adj_forward h ht hcover hgood
  · rintro ⟨hij, x, y, hxy, hx, hy⟩
    let f := finiteClusterOf h hcover
    have hconn : ∀ k, (Q.induce
        (TreeConnectedQuotient.fiber f k)).Connected := by
      intro k
      simpa [TreeConnectedQuotient.fiber, f] using
        finiteClusterOf_connected h ht hcover hgood k
    have hsurj : Function.Surjective f := by
      simpa [f] using finiteClusterOf_surjective h ht hcover
    have hforward : ∀ ⦃a b⦄, (finiteQuotient q).Adj a b →
        ∃ u v : X, Q.Adj u v ∧ f u = a ∧ f v = b := by
      intro a b hab
      obtain ⟨_hne, u, v, huv, hu, hv⟩ :=
        finiteQuotient_adj_forward h ht hcover hgood hab
      exact ⟨u, v, huv, hu, hv⟩
    have hxf : f x = i := by simpa [f] using hx
    have hyf : f y = j := by simpa [f] using hy
    have hne : f x ≠ f y := by
      rw [hxf, hyf]
      exact hij
    have hadj := TreeConnectedQuotient.adj_of_cross hQ
      (finiteQuotient_isTree q) f hconn hsurj hforward hxy hne
    simpa [hxf, hyf] using hadj

omit [Fintype X] in
private theorem sum_toFinset_eq_map_sum (w : X → ℕ) {l : List X}
    (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, w x) = (l.map w).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

open TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The owner-edge count of a finite indexed fiber is exactly the retained
natural cluster weight. -/
theorem finiteCluster_owned_card_eq
    (R : EdgeOwnedRefinementWitness G X) {t : RTree X}
    {q : IndexedQuotient X} (h : IsPartition t q)
    (ht : (vertices t).Nodup) (hcover : ∀ x : X, x ∈ vertices t)
    (i : Fin (Fintype.card (Node q))) :
    (G.edgeFinset.filter fun e ↦
      finiteClusterOf h hcover (R.owner e) = i).card =
      clusterWeight (WeightedTreePartition.ownedWeight R)
        (Node.label ((occurrenceEquiv q).symm i)) := by
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
  rw [WeightedTreePartition.cluster_owned_card_eq_sum R
    (finiteClusterOf h hcover) i, hfilter]
  have hnNodup : (Node.label n).Nodup :=
    (List.nodup_flatten.mp (h.flattenClusters_nodup ht)).1 _
      (Node.label_mem_vertices n)
  exact (sum_toFinset_eq_map_sum
    (WeightedTreePartition.ownedWeight R) hnNodup).trans rfl

/-! ### Edge-owned refinement specialization -/

/-- **Label-preserving finite-tree partition theorem.**

For every subcubic edge-owned refinement whose graph has at least `ℓ` edges,
the intrinsic weighted-tree packing theorem produces a genuine
`ClusterQuotientWitness`: the fibers are connected, their quotient is exactly
the original decomposition-tree edge quotient, and every fiber owns between
`ℓ` and `3ℓ` graph edges. -/
theorem EdgeOwnedRefinementWitness.exists_clusterQuotientWitness
    (R : EdgeOwnedRefinementWitness G X) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (htotal : ℓ ≤ G.edgeFinset.card) :
    ∃ m : ℕ, Nonempty (ClusterQuotientWitness R m ℓ (3 * ℓ)) := by
  classical
  obtain ⟨r, erasedQ, _hroot, _hsubcubic, herasedPartition, herasedBounds⟩ :=
    LowDegree.WeightedTreePartitionAdapter.EdgeOwnedRefinementWitness.exists_intrinsic_owner_partition
      R hℓ htotal
  let source : RTree X :=
    labeledTree R.decomposition.isTree r r
  have herasedPartition' :
      WeightedTreePartition.IsPartition
        (withWeights (WeightedTreePartition.ownedWeight R) source) erasedQ := by
    simpa [source] using herasedPartition
  obtain ⟨indexedQ, hpartition, hweigh⟩ :=
    liftPartition (WeightedTreePartition.ownedWeight R)
      (WeightedTreePartition.ownedWeight_le_one R) herasedPartition'
  have hsourceNodup : (vertices source).Nodup := by
    simpa [source] using
      vertices_labeledTree_nodup R.decomposition.isTree r r
  have hsourceCover : ∀ x : X, x ∈ vertices source := by
    intro x
    simpa [source] using
      mem_vertices_labeledTree_root R.decomposition.isTree r x
  have hsourceRespects : Respects R.decomposition.tree source := by
    simpa [source] using labeledTree_respects R.decomposition.isTree r r
  have hgood : Good R.decomposition.tree source indexedQ :=
    hpartition.good hsourceRespects
  have hindexedBounds : WeightsIn (WeightedTreePartition.ownedWeight R)
      ℓ (3 * ℓ) indexedQ := by
    apply weightsIn_of_labelsIn (WeightedTreePartition.ownedWeight R)
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
    exact finiteClusterOf_connected hpartition hsourceNodup hsourceCover hgood i
  · intro i j
    exact finiteQuotient_adj_iff R.decomposition.isTree hpartition
      hsourceNodup hsourceCover hgood
  · exact finiteQuotient_isTree indexedQ
  · intro i
    rw [finiteCluster_owned_card_eq R hpartition hsourceNodup hsourceCover i]
    exact (Node.weight_bounds_of_weightsIn hindexedBounds _).1
  · intro i
    rw [finiteCluster_owned_card_eq R hpartition hsourceNodup hsourceCover i]
    exact (Node.weight_bounds_of_weightsIn hindexedBounds _).2

end


end IndexedWeightedTreePartition
end LowDegree
