import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega
import LowDegree.Combinatorics.TreeDecomposition

/-!
# Weighted partitions of finite subcubic trees

This file isolates the combinatorial content of Lemma 5.4.  We use an
intrinsic rooted representation: a node has zero, one, or two children, so its
underlying unrooted tree has maximum degree at most three (the root has degree
at most two).  A quotient is again represented intrinsically as a finite
rooted tree.  Thus no acyclicity or connectedness obligations are hidden in
the input of the partition theorem.

Node weights are booleans.  This is the node-weighted form needed by an
edge-owned tree decomposition: a decomposition node has weight one exactly
when it owns an edge.  The strictly-positive assumption on `ℓ` is necessary,
and `ℓ ≤ totalWeight` is the exact non-vacuity guard.
-/

namespace LowDegree
namespace WeightedTreePartition

/-- A finite rooted (rose) tree. -/
inductive RTree (A : Type*) where
  | node (label : A) (children : List (RTree A))
  deriving Repr

namespace RTree

/-- Sum a natural-valued label over all nodes. -/
def sum : RTree ℕ → ℕ
  | .node n children => n + (children.map sum).sum

/-- Number of nodes. -/
def card : RTree A → ℕ
  | .node _ children => 1 + (children.map card).sum

end RTree

abbrev WeightedTree := RTree Bool
abbrev QuotientTree := RTree ℕ

/-- Boolean node weight, regarded as a natural number. -/
def nodeWeight (b : Bool) : ℕ := if b then 1 else 0

/-- Total `0/1` node weight. -/
def totalWeight : WeightedTree → ℕ
  | .node b children => nodeWeight b + (children.map totalWeight).sum

/-- Intrinsic certificate that a rooted tree has at most two children per
node.  Away from the root, the parent edge gives unrooted degree at most three. -/
inductive IsSubcubic : WeightedTree → Prop where
  | leaf (b : Bool) : IsSubcubic (.node b [])
  | unary (b : Bool) {t : WeightedTree} :
      IsSubcubic t → IsSubcubic (.node b [t])
  | binary (b : Bool) {t₁ t₂ : WeightedTree} :
      IsSubcubic t₁ → IsSubcubic t₂ → IsSubcubic (.node b [t₁, t₂])

mutual

/-- `RootSplit t n boundary` says that a connected cluster containing the
root of `t` has weight `n`, and that deleting that cluster leaves exactly the
rooted subtrees in `boundary`.

The constructors are the two possible decisions at a child edge: cut the edge,
or absorb the child's root cluster. -/
inductive RootSplit : WeightedTree → ℕ → List WeightedTree → Prop where
  | node (b : Bool) {children : List WeightedTree} {n : ℕ}
      {boundary : List WeightedTree} :
      SplitChildren children n boundary →
      RootSplit (.node b children) (nodeWeight b + n) boundary

/-- Child-list part of `RootSplit`. -/
inductive SplitChildren : List WeightedTree → ℕ → List WeightedTree → Prop where
  | nil : SplitChildren [] 0 []
  | cut {t : WeightedTree} {ts : List WeightedTree} {n : ℕ}
      {boundary : List WeightedTree} :
      SplitChildren ts n boundary →
      SplitChildren (t :: ts) n (t :: boundary)
  | merge {t : WeightedTree} {ts : List WeightedTree} {n₁ n₂ : ℕ}
      {boundary₁ boundary₂ : List WeightedTree} :
      RootSplit t n₁ boundary₁ → SplitChildren ts n₂ boundary₂ →
      SplitChildren (t :: ts) (n₁ + n₂) (boundary₁ ++ boundary₂)

end

mutual

/-- A structural partition of an input tree by connected clusters.  The
output tree is exactly the contraction quotient, and its labels are the
cluster weights. -/
inductive IsPartition : WeightedTree → QuotientTree → Prop where
  | node {t : WeightedTree} {n : ℕ} {boundary : List WeightedTree}
      {children : List QuotientTree} :
      RootSplit t n boundary → PartitionList boundary children →
      IsPartition t (.node n children)
  | contractFirst {t : WeightedTree} {n₁ n₂ : ℕ}
      {grandchildren siblings : List QuotientTree} :
      IsPartition t (.node n₁ (.node n₂ grandchildren :: siblings)) →
      IsPartition t (.node (n₁ + n₂) (grandchildren ++ siblings))

/-- Listwise version of `IsPartition`. -/
inductive PartitionList : List WeightedTree → List QuotientTree → Prop where
  | nil : PartitionList [] []
  | cons {t : WeightedTree} {q : QuotientTree}
      {ts : List WeightedTree} {qs : List QuotientTree} :
      IsPartition t q → PartitionList ts qs → PartitionList (t :: ts) (q :: qs)

end

mutual

/-- Every quotient cluster has weight in the displayed closed interval. -/
inductive LabelsIn (lower upper : ℕ) : QuotientTree → Prop where
  | node {n : ℕ} {children : List QuotientTree} :
      lower ≤ n → n ≤ upper → LabelsInList lower upper children →
      LabelsIn lower upper (.node n children)

/-- Listwise version of `LabelsIn`. -/
inductive LabelsInList (lower upper : ℕ) : List QuotientTree → Prop where
  | nil : LabelsInList lower upper []
  | cons {q : QuotientTree} {qs : List QuotientTree} :
      LabelsIn lower upper q → LabelsInList lower upper qs →
      LabelsInList lower upper (q :: qs)

end

/-- Total weight of a forest. -/
def forestWeight (ts : List WeightedTree) : ℕ := (ts.map totalWeight).sum

mutual

/-- A root split accounts for every input node exactly once. -/
theorem RootSplit.weight_decomposition {t : WeightedTree} {n : ℕ}
    {boundary : List WeightedTree} (h : RootSplit t n boundary) :
    totalWeight t = n + forestWeight boundary := by
  cases h with
  | node _ hchildren =>
      have ih := SplitChildren.weight_decomposition hchildren
      simp only [totalWeight, forestWeight] at ih ⊢
      omega

/-- Forest version of `RootSplit.weight_decomposition`. -/
theorem SplitChildren.weight_decomposition {ts : List WeightedTree} {n : ℕ}
    {boundary : List WeightedTree} (h : SplitChildren ts n boundary) :
    (ts.map totalWeight).sum = n + forestWeight boundary := by
  cases h with
  | nil => rfl
  | cut hrest =>
      have ih := SplitChildren.weight_decomposition (ts := _) (n := _) (boundary := _) hrest
      simp only [forestWeight, List.map_cons, List.sum_cons] at ih ⊢
      omega
  | merge hroot hrest =>
      have ihroot := RootSplit.weight_decomposition hroot
      have ihrest := SplitChildren.weight_decomposition hrest
      simp only [forestWeight, List.map_cons, List.sum_cons, List.map_append,
        List.sum_append] at ihroot ihrest ⊢
      omega

end


namespace PartitionList

/-- Concatenate two aligned lists of structural partitions. -/
theorem append {ts₁ ts₂ : List WeightedTree} {qs₁ qs₂ : List QuotientTree}
    (h₁ : PartitionList ts₁ qs₁) (h₂ : PartitionList ts₂ qs₂) :
    PartitionList (ts₁ ++ ts₂) (qs₁ ++ qs₂) := by
  cases h₁ with
  | nil => exact h₂
  | cons hp hrest => exact .cons hp (append hrest h₂)

end PartitionList

namespace LabelsInList

/-- Concatenate two lists whose cluster labels obey the same bounds. -/
theorem append {lower upper : ℕ} {qs₁ qs₂ : List QuotientTree}
    (h₁ : LabelsInList lower upper qs₁) (h₂ : LabelsInList lower upper qs₂) :
    LabelsInList lower upper (qs₁ ++ qs₂) := by
  cases h₁ with
  | nil => exact h₂
  | cons hq hrest => exact .cons hq (append hrest h₂)

end LabelsInList

mutual

/-- Widen the permitted upper cluster weight. -/
theorem LabelsIn.mono_upper {lower upper upper' : ℕ} (hu : upper ≤ upper')
    {q : QuotientTree} (h : LabelsIn lower upper q) : LabelsIn lower upper' q := by
  cases h with
  | node hl hupper hchildren =>
      exact .node hl (hupper.trans hu) (LabelsInList.mono_upper hu hchildren)

/-- Listwise version of `LabelsIn.mono_upper`. -/
theorem LabelsInList.mono_upper {lower upper upper' : ℕ} (hu : upper ≤ upper')
    {qs : List QuotientTree} (h : LabelsInList lower upper qs) :
    LabelsInList lower upper' qs := by
  cases h with
  | nil => exact .nil
  | cons hq hrest =>
      exact .cons (LabelsIn.mono_upper hu hq) (LabelsInList.mono_upper hu hrest)

end

private theorem partition_sum_node {t : WeightedTree} {n : ℕ}
    {boundary : List WeightedTree} {children : List QuotientTree}
    (hsplit : RootSplit t n boundary) (_hparts : PartitionList boundary children)
    (hp : (children.map RTree.sum).sum = forestWeight boundary) :
    RTree.sum (.node n children) = totalWeight t := by
  have hs := hsplit.weight_decomposition
  simp only [RTree.sum]
  omega

private theorem partition_sum_contractFirst {t : WeightedTree} {n₁ n₂ : ℕ}
    {grandchildren siblings : List QuotientTree}
    (_h : IsPartition t (.node n₁ (.node n₂ grandchildren :: siblings)))
    (ih : RTree.sum (.node n₁ (.node n₂ grandchildren :: siblings)) = totalWeight t) :
    RTree.sum (.node (n₁ + n₂) (grandchildren ++ siblings)) = totalWeight t := by
  simp only [RTree.sum, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append] at ih ⊢
  omega

private theorem partition_sum_cons {t : WeightedTree} {q : QuotientTree}
    {ts : List WeightedTree} {qs : List QuotientTree}
    (_hp : IsPartition t q) (_hr : PartitionList ts qs)
    (ihp : RTree.sum q = totalWeight t)
    (ihr : (qs.map RTree.sum).sum = forestWeight ts) :
    ((q :: qs).map RTree.sum).sum = forestWeight (t :: ts) := by
  simp only [forestWeight, List.map_cons, List.sum_cons] at ihr ⊢
  omega

/-- The quotient labels account for exactly the total input weight. -/
theorem IsPartition.sum_eq {t : WeightedTree} {q : QuotientTree}
    (h : IsPartition t q) : RTree.sum q = totalWeight t :=
  IsPartition.rec (motive_1 := fun t q _ ↦ RTree.sum q = totalWeight t)
    (motive_2 := fun ts qs _ ↦ (qs.map RTree.sum).sum = forestWeight ts)
    partition_sum_node partition_sum_contractFirst rfl partition_sum_cons h

/-- Listwise version of `IsPartition.sum_eq`. -/
theorem PartitionList.sum_eq {ts : List WeightedTree} {qs : List QuotientTree}
    (h : PartitionList ts qs) : (qs.map RTree.sum).sum = forestWeight ts :=
  PartitionList.rec (motive_1 := fun t q _ ↦ RTree.sum q = totalWeight t)
    (motive_2 := fun ts qs _ ↦ (qs.map RTree.sum).sum = forestWeight ts)
    partition_sum_node partition_sum_contractFirst rfl partition_sum_cons h

/-- The contribution of one child to its parent's still-open root cluster. -/
inductive ChildChoice (t : WeightedTree) : ℕ → List WeightedTree → Prop where
  | cut : ChildChoice t 0 [t]
  | merge {n : ℕ} {boundary : List WeightedTree} :
      RootSplit t n boundary → ChildChoice t n boundary

namespace ChildChoice

/-- Prepend a child decision to decisions for the remaining children. -/
theorem cons {t : WeightedTree} {n₁ : ℕ} {boundary₁ : List WeightedTree}
    (h : ChildChoice t n₁ boundary₁) {ts : List WeightedTree} {n₂ : ℕ}
    {boundary₂ : List WeightedTree} (hrest : SplitChildren ts n₂ boundary₂) :
    SplitChildren (t :: ts) (n₁ + n₂) (boundary₁ ++ boundary₂) := by
  cases h with
  | cut => simpa using SplitChildren.cut hrest
  | merge hroot => exact SplitChildren.merge hroot hrest

end ChildChoice

/-- A partial partition keeps the connected cluster containing the subtree
root open.  Its weight is strictly below `ℓ`; every closed cluster hanging
from its boundary already satisfies the target bounds. -/
structure OpenPart (ℓ : ℕ) (t : WeightedTree) where
  weight : ℕ
  boundary : List WeightedTree
  quotientChildren : List QuotientTree
  split : RootSplit t weight boundary
  partitions : PartitionList boundary quotientChildren
  good : LabelsInList ℓ (2 * ℓ) quotientChildren
  weight_lt : weight < ℓ

/-- Result of the bottom-up construction on a rooted subtree. -/
inductive Packed (ℓ : ℕ) (t : WeightedTree) : Type where
  | open : OpenPart ℓ t → Packed ℓ t
  | closed (q : QuotientTree) :
      IsPartition t q → LabelsIn ℓ (2 * ℓ) q → Packed ℓ t

/-- Data contributed by one recursively processed child. -/
structure Contribution (ℓ : ℕ) (t : WeightedTree) where
  weight : ℕ
  boundary : List WeightedTree
  quotient : List QuotientTree
  choice : ChildChoice t weight boundary
  partitions : PartitionList boundary quotient
  good : LabelsInList ℓ (2 * ℓ) quotient
  weight_lt : weight < ℓ

namespace Contribution

/-- Turn a recursively packed child into the decision seen by its parent. -/
def ofPacked {ℓ : ℕ} (hℓ : 0 < ℓ) {t : WeightedTree} :
    Packed ℓ t → Contribution ℓ t
  | .open p =>
      { weight := p.weight
        boundary := p.boundary
        quotient := p.quotientChildren
        choice := .merge p.split
        partitions := p.partitions
        good := p.good
        weight_lt := p.weight_lt }
  | .closed q hpart hgood =>
      { weight := 0
        boundary := [t]
        quotient := [q]
        choice := .cut
        partitions := .cons hpart .nil
        good := .cons hgood .nil
        weight_lt := hℓ }

end Contribution

theorem nodeWeight_le_one (b : Bool) : nodeWeight b ≤ 1 := by
  cases b <;> simp [nodeWeight]

/-- Close a root cluster once it reaches `ℓ`, and otherwise leave it open
for its parent. -/
def closeOrOpen {ℓ : ℕ} {t : WeightedTree} {n : ℕ}
    {boundary : List WeightedTree} {children : List QuotientTree}
    (hsplit : RootSplit t n boundary) (hparts : PartitionList boundary children)
    (hgood : LabelsInList ℓ (2 * ℓ) children) (hupper : n ≤ 2 * ℓ) : Packed ℓ t :=
  if hlt : n < ℓ then
    .open
      { weight := n
        boundary := boundary
        quotientChildren := children
        split := hsplit
        partitions := hparts
        good := hgood
        weight_lt := hlt }
  else
    .closed (.node n children) (.node hsplit hparts)
      (.node (Nat.le_of_not_gt hlt) hupper hgood)

/-- Bottom-up packing of a finite rooted subcubic tree.  Closed clusters have
weight in `[ℓ, 2ℓ]`; at most one connected root cluster remains open, and it
has weight strictly below `ℓ`. -/
theorem pack_exists (ℓ : ℕ) (hℓ : 0 < ℓ) {t : WeightedTree} (ht : IsSubcubic t) :
    Nonempty (Packed ℓ t) := by
  induction ht with
  | leaf b =>
      have hupper : nodeWeight b ≤ 2 * ℓ := by
        have hb := nodeWeight_le_one b
        omega
      exact ⟨closeOrOpen (.node b .nil) .nil .nil hupper⟩
  | @unary b t ht ih =>
      obtain ⟨p⟩ := ih
      let c := Contribution.ofPacked hℓ p
      have hchildren : SplitChildren [t] c.weight c.boundary := by
        simpa using c.choice.cons SplitChildren.nil
      have hsplit : RootSplit (.node b [t]) (nodeWeight b + c.weight) c.boundary :=
        .node b hchildren
      have hupper : nodeWeight b + c.weight ≤ 2 * ℓ := by
        have hb := nodeWeight_le_one b
        have hc := c.weight_lt
        omega
      exact ⟨closeOrOpen hsplit c.partitions c.good hupper⟩
  | @binary b t₁ t₂ ht₁ ht₂ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁
      obtain ⟨p₂⟩ := ih₂
      let c₁ := Contribution.ofPacked hℓ p₁
      let c₂ := Contribution.ofPacked hℓ p₂
      have htail : SplitChildren [t₂] c₂.weight c₂.boundary := by
        simpa using c₂.choice.cons SplitChildren.nil
      have hchildren : SplitChildren [t₁, t₂] (c₁.weight + c₂.weight)
          (c₁.boundary ++ c₂.boundary) := by
        simpa [Nat.add_assoc, List.append_assoc] using c₁.choice.cons htail
      have hsplit : RootSplit (.node b [t₁, t₂])
          (nodeWeight b + (c₁.weight + c₂.weight))
          (c₁.boundary ++ c₂.boundary) := .node b hchildren
      have hparts : PartitionList (c₁.boundary ++ c₂.boundary)
          (c₁.quotient ++ c₂.quotient) := c₁.partitions.append c₂.partitions
      have hgood : LabelsInList ℓ (2 * ℓ) (c₁.quotient ++ c₂.quotient) :=
        c₁.good.append c₂.good
      have hupper : nodeWeight b + (c₁.weight + c₂.weight) ≤ 2 * ℓ := by
        have hb := nodeWeight_le_one b
        have hc₁ := c₁.weight_lt
        have hc₂ := c₂.weight_lt
        omega
      exact ⟨closeOrOpen hsplit hparts hgood hupper⟩

/-- **Weighted subcubic tree partition (node-weighted Lemma 5.4).**

If a finite rooted subcubic tree with `0/1` node weights has total weight at
least the positive threshold `ℓ`, its vertices can be partitioned into
nonempty connected clusters of weight between `ℓ` and `3ℓ`.  `IsPartition`
records the partition by actual adjacent-cluster contractions, so `q` is the
contraction quotient and is a tree by construction.

The intermediate bottom-up construction closes clusters by weight `2ℓ`.
Only the final open root cluster may be light; it is merged with its first
adjacent closed cluster, giving the sharp advertised upper bound `3ℓ`. -/
theorem exists_partition {t : WeightedTree} (ht : IsSubcubic t) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (htotal : ℓ ≤ totalWeight t) :
    ∃ q : QuotientTree, IsPartition t q ∧ LabelsIn ℓ (3 * ℓ) q := by
  obtain ⟨p⟩ := pack_exists ℓ hℓ ht
  cases p with
  | closed q hpart hgood =>
      refine ⟨q, hpart, hgood.mono_upper ?_⟩
      omega
  | «open» o =>
      rcases o with ⟨n, boundary, children, hsplit, hparts, hgood, hnlt⟩
      cases hparts with
      | nil =>
          have hweight := hsplit.weight_decomposition
          simp [forestWeight] at hweight
          omega
      | @cons t₀ q₀ ts qs hpart hrest =>
          cases q₀ with
          | node m grandchildren =>
              cases hgood with
              | cons hq hqs =>
                  cases hq with
                  | node hml hmu hgrand =>
                      let initial : IsPartition t
                          (.node n (.node m grandchildren :: qs)) :=
                        .node hsplit (.cons hpart hrest)
                      have hnew : IsPartition t
                          (.node (n + m) (grandchildren ++ qs)) :=
                        .contractFirst initial
                      have hchildren : LabelsInList ℓ (3 * ℓ)
                          (grandchildren ++ qs) :=
                        (hgrand.append hqs).mono_upper (by omega)
                      have hrootLower : ℓ ≤ n + m := by omega
                      have hrootUpper : n + m ≤ 3 * ℓ := by omega
                      exact ⟨.node (n + m) (grandchildren ++ qs), hnew,
                        .node hrootLower hrootUpper hchildren⟩

/-! ### Edge-owner weight adapter -/

open scoped BigOperators
open TreeDecomposition

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

variable {V X : Type*} [Fintype V] [Fintype X] {G : SimpleGraph V}

/-- Number of graph edges owned by a decomposition-tree node. -/
def ownedWeight (R : EdgeOwnedRefinementWitness G X) (x : X) : ℕ :=
  (G.edgeFinset.filter fun e ↦ R.owner e = x).card

/-- Injectivity of edge ownership makes the owner-node weights genuinely
`0/1`-valued. -/
theorem ownedWeight_le_one (R : EdgeOwnedRefinementWitness G X) (x : X) :
    ownedWeight R x ≤ 1 := by
  classical
  rw [ownedWeight, Finset.card_le_one]
  intro e he f hf
  simp only [Finset.mem_filter] at he hf
  exact R.owner_inj (by simpa using he.1) (by simpa using hf.1)
    (he.2.trans hf.2.symm)

/-- Boolean form of the owner-node weight. -/
def ownedBool (R : EdgeOwnedRefinementWitness G X) (x : X) : Bool :=
  decide (ownedWeight R x = 1)

@[simp]
theorem nodeWeight_ownedBool (R : EdgeOwnedRefinementWitness G X) (x : X) :
    nodeWeight (ownedBool R x) = ownedWeight R x := by
  have h := ownedWeight_le_one R x
  have hw : ownedWeight R x = 0 ∨ ownedWeight R x = 1 := by omega
  rcases hw with hw | hw <;> simp [ownedBool, nodeWeight, hw]

/-- Double-counting owner incidences: the total node weight is exactly the
number of graph edges. -/
theorem sum_ownedWeight (R : EdgeOwnedRefinementWitness G X) :
    (∑ x : X, ownedWeight R x) = G.edgeFinset.card := by
  classical
  calc
    (∑ x : X, ownedWeight R x) =
        ∑ x : X, ∑ e ∈ G.edgeFinset, if R.owner e = x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [ownedWeight, Finset.card_eq_sum_ones]
          simp only [Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ x : X, if R.owner e = x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ _e ∈ G.edgeFinset, 1 := by
          apply Finset.sum_congr rfl
          intro e _
          simp
    _ = G.edgeFinset.card := by simp

/-- Boolean-weight version of `sum_ownedWeight`.  This is the numerical part
of the adapter to `ClusterQuotientWitness`. -/
theorem sum_nodeWeight_ownedBool (R : EdgeOwnedRefinementWitness G X) :
    (∑ x : X, nodeWeight (ownedBool R x)) = G.edgeFinset.card := by
  simp_rw [nodeWeight_ownedBool R]
  exact sum_ownedWeight R

/-- For any proposed clustering of decomposition nodes, the existing
`ClusterQuotientWitness` edge count is exactly the sum of owner-node weights
over the corresponding fiber. -/
theorem cluster_owned_card_eq_sum {I : Type*} [DecidableEq I]
    (R : EdgeOwnedRefinementWitness G X) (clusterOf : X → I) (i : I) :
    (G.edgeFinset.filter fun e ↦ clusterOf (R.owner e) = i).card =
      ∑ x ∈ Finset.univ.filter (fun x ↦ clusterOf x = i), ownedWeight R x := by
  classical
  calc
    (G.edgeFinset.filter fun e ↦ clusterOf (R.owner e) = i).card =
        ∑ e ∈ G.edgeFinset, if clusterOf (R.owner e) = i then 1 else 0 := by
          rw [Finset.card_eq_sum_ones]
          simp only [Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset,
          ∑ x ∈ Finset.univ.filter (fun x ↦ clusterOf x = i),
            if R.owner e = x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          simp
    _ = ∑ x ∈ Finset.univ.filter (fun x ↦ clusterOf x = i),
          ∑ e ∈ G.edgeFinset, if R.owner e = x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ Finset.univ.filter (fun x ↦ clusterOf x = i), ownedWeight R x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [ownedWeight, Finset.card_eq_sum_ones]
          simp only [Finset.sum_filter]

end

end WeightedTreePartition
end LowDegree
