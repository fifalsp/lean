import LowDegree.Asymptotics.ConnectedBetaMass
import LowDegree.Combinatorics.AggregateGraphRestriction
import LowDegree.Combinatorics.BoundedOverlapDivision

/-!
# Aggregate large connected beta-mass bounds

This file combines the graph-specific aggregate restriction injection with
the per-triple beta scale.  For a fixed number `m` of decomposition pieces,
the complete sum over parent graph-shape classes is bounded by the `m`th
power of the block beta mass, with no duplicate parent-shape factor.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

open TreeDecomposition
open AggregateGraphRestriction

namespace AggregateGraphRestriction.FixedPieceClassDivision

variable {Parent : Type*} [Fintype Parent]
variable {n m l : ℕ} (D : FixedPieceClassDivision Parent n m l)

/-- Edge counts add over an ordered edge division. -/
theorem edgeCount_eq_sum_piece_edgeCount (a : Parent) :
    (D.classOf a).shape.edgeCount =
      ∑ i, ((D.classOf a).shape.pieceShape (D.decomposition a) i).edgeCount := by
  calc
    (D.classOf a).shape.edgeCount =
        (D.classOf a).shape.graph.edgeFinset.card := by
      rw [FiniteGraphShape.edgeCount_eq_ncard]
      exact Set.ncard_eq_toFinset_card' _
    _ = ∑ i, ((D.decomposition a).piece i).edgeFinset.card :=
      (D.decomposition a).card_edges_eq_sum
    _ = ∑ i,
        ((D.classOf a).shape.pieceShape (D.decomposition a) i).edgeCount := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (pieceShape_edgeCount_eq_edgeFinset_card
        (D.classOf a) (D.decomposition a) i).symm

/-- The sum of piece vertex counts is the parent vertex count plus overlap. -/
theorem sum_piece_vertexCount_eq (a : Parent) :
    (∑ i, ((D.classOf a).shape.pieceShape
      (D.decomposition a) i).vertexCount) =
      (D.classOf a).shape.vertexCount + (D.decomposition a).overlap := by
  calc
    (∑ i, ((D.classOf a).shape.pieceShape
        (D.decomposition a) i).vertexCount) =
        ∑ i, ((D.decomposition a).vertexFinset i).card := by
      simp only [FiniteGraphShape.pieceShape_vertexCount]
    _ = (D.decomposition a).overlap +
        (D.decomposition a).graphVertexFinset.card :=
      (D.decomposition a).overlap_add_graphVertex_card.symm
    _ = (D.classOf a).shape.vertexCount +
        (D.decomposition a).overlap := by
      rw [← (D.classOf a).shape.vertexCount_eq_graphVertexFinset_card
        (D.decomposition a)]
      omega

/-- Per-triple Equation (4.4), before summing: one parent scale is at most
`n^overlap` times the product of its piece scales. -/
theorem tripleBetaScale_le_overlap_mul_prod
    (c : ℝ) (hc : 0 < c) (hn : 0 < n) (a : Parent) :
    tripleBetaScale c n (D.classOf a).shape ≤
      (n : ℝ) ^ (D.decomposition a).overlap *
        ∏ i, tripleBetaScale c n
          ((D.classOf a).shape.pieceShape (D.decomposition a) i) := by
  apply beta_le_overlap_mul_prod
    (n := (n : ℝ)) (c := c)
    (edgeCount := (D.classOf a).shape.edgeCount)
    (vertexCount := (D.classOf a).shape.vertexCount)
    (overlap := (D.decomposition a).overlap)
    (pieceEdges := fun i ↦
      ((D.classOf a).shape.pieceShape (D.decomposition a) i).edgeCount)
    (pieceVertices := fun i ↦
      ((D.classOf a).shape.pieceShape (D.decomposition a) i).vertexCount)
    (tripleCount := 1) (pieceTripleCount := fun _ ↦ 1)
  · exact_mod_cast hn
  · exact hc
  · exact D.edgeCount_eq_sum_piece_edgeCount a
  · exact D.sum_piece_vertexCount_eq a
  · norm_num
  · intro i
    norm_num
  · simp

/-- Reindexing a piece by its ambient support class does not change its
per-triple beta scale. -/
theorem tripleBetaScale_pieceClass (c : ℝ) (a : Parent) (i : Fin m) :
    tripleBetaScale c n (D.pieceBlockClass a i).1.shape =
      tripleBetaScale c n
        ((D.classOf a).shape.pieceShape (D.decomposition a) i) := by
  exact (tripleBetaScale_eq_of_iso
    (pieceShapeIso (D.classOf a) (D.decomposition a) i)).symm

/-- If noise absorbs the vertex-overlap factor, the noised scale of every
global triple is bounded by the product of its encoded block-triple scales. -/
theorem noisedTripleScale_le_prod
    (G : SimpleGraph (Fin n))
    (c : ℝ) (hc : 0 < c) (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : Parent,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        (n : ℝ) ^ (D.decomposition a).overlap ≤ 1)
    (z : D.GlobalTriple G) :
    (1 - (noise : ℝ)) ^ (2 * (D.classOf z.1).shape.edgeCount) *
        tripleBetaScale c n (D.classOf z.1).shape ≤
      ∏ i, tripleBetaScale c n (D.encode G z i).1.1.shape := by
  rcases z with ⟨a, triple⟩
  have hscale := D.tripleBetaScale_le_overlap_mul_prod c hc hn a
  have hnoise : 0 ≤
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) :=
    pow_nonneg (sub_nonneg.mpr noise.2.2.le) _
  have hprod : 0 ≤ ∏ i, tripleBetaScale c n
      ((D.classOf a).shape.pieceShape (D.decomposition a) i) := by
    exact Finset.prod_nonneg fun i _ ↦
      tripleBetaScale_nonneg hc n _
  calc
    (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        tripleBetaScale c n (D.classOf a).shape ≤
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        ((n : ℝ) ^ (D.decomposition a).overlap *
          ∏ i, tripleBetaScale c n
            ((D.classOf a).shape.pieceShape (D.decomposition a) i)) :=
      mul_le_mul_of_nonneg_left hscale hnoise
    _ = ((1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
          (n : ℝ) ^ (D.decomposition a).overlap) *
        ∏ i, tripleBetaScale c n
          ((D.classOf a).shape.pieceShape (D.decomposition a) i) := by ring
    _ ≤ 1 * ∏ i, tripleBetaScale c n
          ((D.classOf a).shape.pieceShape (D.decomposition a) i) :=
      mul_le_mul_of_nonneg_right (habsorb a) hprod
    _ = ∏ i, tripleBetaScale c n
          ((D.classOf a).shape.pieceShape (D.decomposition a) i) := one_mul _
    _ = ∏ i, tripleBetaScale c n
          (D.encode G ⟨a, triple⟩ i).1.1.shape := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact (D.tripleBetaScale_pieceClass c a i).symm

/-- Expanding the tagged global-triple sum recovers the corresponding sum of
noised class beta weights. -/
theorem sum_globalTriple_noisedScale_eq
    (G : SimpleGraph (Fin n)) (c : ℝ) (noise : NoiseRate) :
    (∑ z : D.GlobalTriple G,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf z.1).shape.edgeCount) *
        tripleBetaScale c n (D.classOf z.1).shape) =
      ∑ a : Parent,
        (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
          (D.classOf a).shape.graphBetaWeight c n G := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _ha
  change (∑ _y : (D.classOf a).shape.IsomorphismTripleIn G,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        tripleBetaScale c n (D.classOf a).shape) = _
  rw [← Finset.mul_sum, sum_tripleBetaScale_eq_graphBetaWeight]

/-- Expanding the tagged block-triple sum gives exactly the beta mass of all
ambient support classes in the block range. -/
theorem sum_blockTriple_scale_eq
    (G : SimpleGraph (Fin n)) (c : ℝ) :
    (∑ z : BlockTriple (n := n) (l := l) G,
      tripleBetaScale c n z.1.1.shape) =
      ∑ C : AmbientSupportClass n with
          l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l,
        C.shape.graphBetaWeight c n G := by
  rw [Fintype.sum_sigma]
  calc
    (∑ B : BlockClass n l,
        ∑ _triple : B.1.shape.IsomorphismTripleIn G,
          tripleBetaScale c n B.1.shape) =
        ∑ B : BlockClass n l, B.1.shape.graphBetaWeight c n G := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact sum_tripleBetaScale_eq_graphBetaWeight c n B.1.shape G
    _ = ∑ C : AmbientSupportClass n with
          l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l,
        C.shape.graphBetaWeight c n G := by
      symm
      exact Finset.sum_subtype
        (p := fun C : AmbientSupportClass n ↦
          l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l)
        ((Finset.univ : Finset (AmbientSupportClass n)).filter fun C ↦
          l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l)
        (by intro C; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun C ↦ C.shape.graphBetaWeight c n G)

/-- **Fixed-piece aggregate large-support inequality.**

For a duplicate-free family of parent classes, all divided into exactly `m`
block-sized pieces, aggregate restriction bounds their total noised beta mass
by the `m`th power of the full block beta mass. -/
theorem noisedClassMass_le_blockMass_pow
    (G : SimpleGraph (Fin n))
    (c : ℝ) (hc : 0 < c) (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : Parent,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        (n : ℝ) ^ (D.decomposition a).overlap ≤ 1) :
    (∑ a : Parent,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        (D.classOf a).shape.graphBetaWeight c n G) ≤
      (∑ C : AmbientSupportClass n with
          l ≤ C.shape.edgeCount ∧ C.shape.edgeCount ≤ 3 * l,
        C.shape.graphBetaWeight c n G) ^ m := by
  rw [← D.sum_globalTriple_noisedScale_eq G c noise,
    ← sum_blockTriple_scale_eq (n := n) (l := l) G c]
  apply weighted_sum_le_sum_pow_of_injective m
    (D.encode G) (D.encode_injective G)
    (fun z ↦
      (1 - (noise : ℝ)) ^ (2 * (D.classOf z.1).shape.edgeCount) *
        tripleBetaScale c n (D.classOf z.1).shape)
    (fun z : BlockTriple (n := n) (l := l) G ↦
      tripleBetaScale c n z.1.1.shape)
  · intro z
    exact tripleBetaScale_nonneg hc n z.1.1.shape
  · exact D.noisedTripleScale_le_prod G c hc noise hn habsorb

end AggregateGraphRestriction.FixedPieceClassDivision

namespace BoundedTreewidthPlantModel

/-- Model-facing form of the fixed-piece aggregate restriction inequality. -/
theorem fixedPieceNoisedClassMass_le_blockBetaMass_pow
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) {n m : ℕ} (hn : 0 < n)
    {Parent : Type*} [Fintype Parent]
    (D : AggregateGraphRestriction.FixedPieceClassDivision Parent n m (l n))
    (habsorb : ∀ a : Parent,
      (1 - (noise : ℝ)) ^ (2 * (D.classOf a).shape.edgeCount) *
        (n : ℝ) ^ (D.decomposition a).overlap ≤ 1) :
    (∑ a : Parent, M.noisedBetaClassWeight noise (D.classOf a)) ≤
      (M.blockBetaMass l n) ^ m := by
  simpa only [noisedBetaClassWeight, blockBetaMass] using
    D.noisedClassMass_le_blockMass_pow
      (M.plant n) M.backgroundDensity M.backgroundDensity_pos noise hn habsorb

/-! ## Summing over the number of pieces -/

/-- Connected support classes in the large range that actually occur in the
plant.  Classes outside this subtype have zero beta weight. -/
abbrev LargeOccurringClass
    (M : BoundedTreewidthPlantModel) (l n : ℕ) :=
  {C : AmbientSupportClass n //
    C.shape.graph.Connected ∧ l ≤ C.shape.edgeCount ∧
      0 < C.shape.nonInducedCopyCount (M.plant n)}

/-- A support class that does not occur in the plant has zero noised beta
weight. -/
theorem noisedBetaClassWeight_eq_zero_of_not_occurring
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) {n : ℕ}
    (C : AmbientSupportClass n)
    (hocc : ¬ 0 < C.shape.nonInducedCopyCount (M.plant n)) :
    M.noisedBetaClassWeight noise C = 0 := by
  have hzero : C.shape.nonInducedCopyCount (M.plant n) = 0 :=
    Nat.eq_zero_of_not_pos hocc
  simp [noisedBetaClassWeight, FiniteGraphShape.graphBetaWeight,
    betaWeight, hzero]

/-- Removing the zero-weight nonoccurring classes identifies the large
connected mass with the sum over `LargeOccurringClass`. -/
theorem largeConnectedNoisedBetaMass_eq_sum_largeOccurring
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) :
    M.largeConnectedNoisedBetaMass noise l n =
      ∑ a : M.LargeOccurringClass (l n) n,
        M.noisedBetaClassWeight noise a.1 := by
  let p : AmbientSupportClass n → Prop := fun C ↦
    C.shape.graph.Connected ∧ l n ≤ C.shape.edgeCount
  let q : AmbientSupportClass n → Prop := fun C ↦
    p C ∧ 0 < C.shape.nonInducedCopyCount (M.plant n)
  calc
    M.largeConnectedNoisedBetaMass noise l n =
        ∑ C : AmbientSupportClass n with p C,
          M.noisedBetaClassWeight noise C := by
      rfl
    _ = ∑ C : AmbientSupportClass n with q C,
          M.noisedBetaClassWeight noise C := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro C _hC
      by_cases hp : p C
      · by_cases hocc : 0 < C.shape.nonInducedCopyCount (M.plant n)
        · simp [hp, hocc, q]
        · simp [hp, hocc, q,
            M.noisedBetaClassWeight_eq_zero_of_not_occurring noise C hocc]
      · simp [hp, q]
    _ = ∑ a : M.LargeOccurringClass (l n) n,
          M.noisedBetaClassWeight noise a.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (AmbientSupportClass n)).filter q)
        (by intro C; simp [q, p, and_assoc])
        (fun C ↦ M.noisedBetaClassWeight noise C)

/-- A simultaneous choice of a block decomposition for every occurring
large connected class at fixed `n` and block scale `l`. -/
structure LargeClassDivision
    (M : BoundedTreewidthPlantModel) (l n : ℕ) where
  pieceCount : M.LargeOccurringClass l n → ℕ
  pieceCount_pos : ∀ a, 0 < pieceCount a
  decomposition : ∀ a,
    OrderedEdgeDecomposition a.1.shape.graph (pieceCount a)
  piece_lower : ∀ a i,
    l ≤ ((decomposition a).piece i).edgeFinset.card
  piece_upper : ∀ a i,
    ((decomposition a).piece i).edgeFinset.card ≤ 3 * l
  overlap_le : ∀ a,
    (decomposition a).overlap ≤
      (M.treewidthBound n + 1) * (pieceCount a - 1)

namespace LargeClassDivision

variable {M : BoundedTreewidthPlantModel} {l n : ℕ}
    (Q : M.LargeClassDivision l n)

/-- The occurring large classes whose selected decomposition has exactly
`m` pieces. -/
abbrev PieceCountFiber (m : ℕ) :=
  {a : M.LargeOccurringClass l n // Q.pieceCount a = m}

/-- Regard one piece-count fiber as a fixed-piece division, ready for the
aggregate restriction injection. -/
noncomputable def fixedPieceDivision (m : ℕ) :
    AggregateGraphRestriction.FixedPieceClassDivision
      (Q.PieceCountFiber m) n m l where
  classOf a := a.1.1
  classOf_injective := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    apply Subtype.ext
    exact Subtype.ext hab
  decomposition := fun a ↦
    Eq.mp (congrArg
      (OrderedEdgeDecomposition a.1.1.shape.graph) a.property)
      (Q.decomposition a.1)
  piece_lower := by
    rintro ⟨a, rfl⟩ i
    exact Q.piece_lower a i
  piece_upper := by
    rintro ⟨a, rfl⟩ i
    exact Q.piece_upper a i

/-- Every selected piece count is bounded by the supremum over the finite
class family. -/
theorem pieceCount_le_sup (a : M.LargeOccurringClass l n) :
    Q.pieceCount a ≤
      (Finset.univ : Finset (M.LargeOccurringClass l n)).sup Q.pieceCount := by
  exact Finset.le_sup (Finset.mem_univ a)

/-- The fixed-piece inequality on one piece-count fiber, expressed as a
filtered sum over the original class subtype. -/
theorem fiberNoisedMass_le_blockBetaMass_pow
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.LargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (m : ℕ) :
    (∑ a ∈ (Finset.univ : Finset (M.LargeOccurringClass l n)) with
        Q.pieceCount a = m,
      M.noisedBetaClassWeight noise a.1) ≤
      (M.blockBetaMass (fun _ ↦ l) n) ^ m := by
  have hfixed := M.fixedPieceNoisedClassMass_le_blockBetaMass_pow
    noise (fun _ ↦ l) hn (Q.fixedPieceDivision m) (by
      rintro ⟨a, rfl⟩
      exact habsorb a)
  calc
    (∑ a ∈ (Finset.univ : Finset (M.LargeOccurringClass l n)) with
        Q.pieceCount a = m,
      M.noisedBetaClassWeight noise a.1) =
        ∑ a : Q.PieceCountFiber m,
          M.noisedBetaClassWeight noise a.1.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (M.LargeOccurringClass l n)).filter
          fun a ↦ Q.pieceCount a = m)
        (by intro a; simp)
        (fun a ↦ M.noisedBetaClassWeight noise a.1)
    _ ≤ (M.blockBetaMass (fun _ ↦ l) n) ^ m := hfixed

/-- Sum the fixed-piece restriction bounds over every possible positive
piece count. -/
theorem occurringNoisedMass_le_geometricPartialSum
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.LargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1) :
    (∑ a : M.LargeOccurringClass l n,
      M.noisedBetaClassWeight noise a.1) ≤
      ∑ m ∈ Finset.Ico 1
          ((Finset.univ : Finset (M.LargeOccurringClass l n)).sup
            Q.pieceCount + 1),
        (M.blockBetaMass (fun _ ↦ l) n) ^ m := by
  let topCount :=
    (Finset.univ : Finset (M.LargeOccurringClass l n)).sup Q.pieceCount
  have hfiber :
      (∑ m ∈ Finset.Ico 1 (topCount + 1),
        ∑ a ∈ (Finset.univ : Finset (M.LargeOccurringClass l n)) with
          Q.pieceCount a = m,
          M.noisedBetaClassWeight noise a.1) =
        ∑ a : M.LargeOccurringClass l n,
          M.noisedBetaClassWeight noise a.1 := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    have hfilter :
        (Finset.univ : Finset (M.LargeOccurringClass l n)).filter
            (fun a ↦ Q.pieceCount a ∈ Finset.Ico 1 (topCount + 1)) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro a _ha
      simp only [Finset.mem_Ico]
      exact ⟨Q.pieceCount_pos a, by
        simpa only [topCount] using
          Nat.lt_succ_of_le (Q.pieceCount_le_sup a)⟩
    rw [hfilter]
  rw [← hfiber]
  apply Finset.sum_le_sum
  intro m _hm
  exact Q.fiberNoisedMass_le_blockBetaMass_pow noise hn habsorb m

/-- The complete occurring large-class mass is bounded by the geometric
tail of the block mass whenever that mass lies in `[0,1)`. -/
theorem occurringNoisedMass_le_geometricTail
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.LargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (hblock0 : 0 ≤ M.blockBetaMass (fun _ ↦ l) n)
    (hblock1 : M.blockBetaMass (fun _ ↦ l) n < 1) :
    (∑ a : M.LargeOccurringClass l n,
      M.noisedBetaClassWeight noise a.1) ≤
      M.blockBetaMass (fun _ ↦ l) n /
        (1 - M.blockBetaMass (fun _ ↦ l) n) := by
  let b := M.blockBetaMass (fun _ ↦ l) n
  let topCount :=
    (Finset.univ : Finset (M.LargeOccurringClass l n)).sup Q.pieceCount
  have hpartial := Q.occurringNoisedMass_le_geometricPartialSum
    noise hn habsorb
  have hgeom :
      (∑ m ∈ Finset.Ico 1 (topCount + 1), b ^ m) ≤
        b / (1 - b) := by
    rw [geom_sum_Ico' (ne_of_lt hblock1) (by omega)]
    have hden : 0 < 1 - b := sub_pos.mpr hblock1
    rw [div_le_div_iff_of_pos_right hden]
    have hp : 0 ≤ b ^ (topCount + 1) := pow_nonneg hblock0 _
    simp only [pow_one]
    linarith
  exact hpartial.trans (by simpa only [b, topCount] using hgeom)

end LargeClassDivision

/-- A decomposition of a nonempty graph necessarily has a positive number
of pieces. -/
private theorem orderedEdgeDecomposition_pieceCount_pos
    {V : Type*} [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (P : OrderedEdgeDecomposition G m) (hG : G ≠ ⊥) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  have hbot : G = ⊥ := by
    have hcover := P.cover
    rw [iSup_of_empty] at hcover
    exact hcover.symm
  exact hG hbot

/-- Proposition 5.1, chosen simultaneously over the finite family of all
occurring large connected classes. -/
noncomputable def largeClassDivision
    (M : BoundedTreewidthPlantModel) (l : ℕ) (hl : 0 < l) (n : ℕ) :
    M.LargeClassDivision l n := by
  let Data : M.LargeOccurringClass l n → Type := fun a ↦
    Σ m : ℕ, {P : OrderedEdgeDecomposition a.1.shape.graph m //
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ (M.treewidthBound n + 1) * (m - 1)}
  have hData : ∀ a : M.LargeOccurringClass l n, Nonempty (Data a) := by
    intro a
    have htw : TreeDecomposition.HasTreewidthAtMost
        a.1.shape.graph (M.treewidthBound n) :=
      a.1.shape.hasTreewidthAtMost_of_occurrence
        (M.plant n) a.property.2.2 (M.treewidth_le n)
    have htotal : l ≤ a.1.shape.graph.edgeFinset.card := by
      calc
        l ≤ a.1.shape.edgeCount := a.property.2.1
        _ = a.1.shape.graph.edgeFinset.card := by
          rw [FiniteGraphShape.edgeCount_eq_ncard]
          exact Set.ncard_eq_toFinset_card' _
    obtain ⟨m, P, hpieces, hoverlap⟩ :=
      TreeDecomposition.connected_exists_boundedOverlap_orderedEdgeDecomposition
        a.property.1 htw hl htotal
    exact ⟨⟨m, ⟨P, hpieces, hoverlap⟩⟩⟩
  let data : ∀ a : M.LargeOccurringClass l n, Data a := fun a ↦
    Classical.choice (hData a)
  refine
    { pieceCount := fun a ↦ (data a).1
      pieceCount_pos := ?_
      decomposition := fun a ↦ (data a).2.1
      piece_lower := ?_
      piece_upper := ?_
      overlap_le := ?_ }
  · intro a
    apply orderedEdgeDecomposition_pieceCount_pos (data a).2.1
    intro hbot
    have hedge0 : a.1.shape.graph.edgeFinset.card = 0 := by simp [hbot]
    have htotal : l ≤ a.1.shape.graph.edgeFinset.card := by
      calc
        l ≤ a.1.shape.edgeCount := a.property.2.1
        _ = a.1.shape.graph.edgeFinset.card := by
          rw [FiniteGraphShape.edgeCount_eq_ncard]
          exact Set.ncard_eq_toFinset_card' _
    omega
  · intro a i
    exact (data a).2.2.1 i |>.1
  · intro a i
    exact (data a).2.2.1 i |>.2
  · intro a
    exact (data a).2.2.2

/-- Rewrite the product of the edge-noise factor and the maximal
treewidth-overlap factor as the exponential used in `ConnectedUpperBound`. -/
private theorem noiseOverlapProduct_eq_exp
    (noise : NoiseRate) (k : ℕ → ℕ) (l : ℕ)
    {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) :
    (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ ((k n + 1) * (m - 1)) =
      Real.exp
        (overlapNoiseExponent (noise : ℝ) k (fun _ ↦ l) n m) := by
  have hq : 0 < 1 - (noise : ℝ) := sub_pos.mpr noise.2.2
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have qpow :
      (1 - (noise : ℝ)) ^ (2 * m * l) =
        Real.exp
          (Real.log (1 - (noise : ℝ)) * ((2 * m * l : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_def_of_pos hq _
  have npow :
      (n : ℝ) ^ ((k n + 1) * (m - 1)) =
        Real.exp
          (Real.log (n : ℝ) * (((k n + 1) * (m - 1) : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_def_of_pos hnreal _
  rw [qpow, npow, ← Real.exp_add]
  apply congrArg Real.exp
  unfold overlapNoiseExponent
  push_cast [Nat.cast_sub hm]
  ring

/-- The uniform exponential estimate absorbs the actual overlap of every
chosen class decomposition. -/
theorem LargeClassDivision.noise_absorbs_overlap
    {M : BoundedTreewidthPlantModel} {l n : ℕ}
    (Q : M.LargeClassDivision l n) (noise : NoiseRate) (hn : 0 < n)
    (hexp : ∀ m : ℕ, 1 ≤ m →
      Real.exp
        (overlapNoiseExponent (noise : ℝ) M.treewidthBound
          (fun _ ↦ l) n m) ≤ 1) :
    ∀ a : M.LargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1 := by
  intro a
  let m := Q.pieceCount a
  let P := Q.decomposition a
  have hm : 1 ≤ m := Q.pieceCount_pos a
  have hedge : m * l ≤ a.1.shape.edgeCount := by
    calc
      m * l = ∑ _i : Fin m, l := by simp [mul_comm]
      _ ≤ ∑ i : Fin m, (P.piece i).edgeFinset.card := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Q.piece_lower a i
      _ = a.1.shape.graph.edgeFinset.card := P.card_edges_eq_sum.symm
      _ = a.1.shape.edgeCount := by
        rw [FiniteGraphShape.edgeCount_eq_ncard]
        exact (Set.ncard_eq_toFinset_card' _).symm
  have hq0 : 0 ≤ 1 - (noise : ℝ) := sub_nonneg.mpr noise.2.2.le
  have hq1 : 1 - (noise : ℝ) ≤ 1 := by linarith [noise.2.1]
  have hqpow :
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) ≤
        (1 - (noise : ℝ)) ^ (2 * m * l) := by
    apply pow_le_pow_of_le_one hq0 hq1
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hedge
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpow :
      (n : ℝ) ^ (P.overlap) ≤
        (n : ℝ) ^ ((M.treewidthBound n + 1) * (m - 1)) :=
    pow_le_pow_right₀ hn1 (Q.overlap_le a)
  calc
    (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ P.overlap ≤
      (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ P.overlap :=
      mul_le_mul_of_nonneg_right hqpow (pow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ ((M.treewidthBound n + 1) * (m - 1)) :=
      mul_le_mul_of_nonneg_left hnpow (pow_nonneg hq0 _)
    _ = Real.exp
        (overlapNoiseExponent (noise : ℝ) M.treewidthBound
          (fun _ ↦ l) n m) :=
      noiseOverlapProduct_eq_exp noise M.treewidthBound l hn hm
    _ ≤ 1 := hexp m hm

/-- Finite large-support inequality supplied by any simultaneous family of
block divisions whose overlap penalties are absorbed by the noise. -/
theorem largeConnectedNoisedBetaMass_le_geometricTail_of_division
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (Q : M.LargeClassDivision (l n) n)
    (habsorb : ∀ a : M.LargeOccurringClass (l n) n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (hblock0 : 0 ≤ M.blockBetaMass l n)
    (hblock1 : M.blockBetaMass l n < 1) :
    M.largeConnectedNoisedBetaMass noise l n ≤
      M.blockBetaMass l n / (1 - M.blockBetaMass l n) := by
  rw [M.largeConnectedNoisedBetaMass_eq_sum_largeOccurring noise l n]
  simpa only using
    Q.occurringNoisedMass_le_geometricTail noise hn habsorb hblock0 hblock1

/-- The block beta mass is nonnegative at every finite `n`. -/
theorem blockBetaMass_nonneg
    (M : BoundedTreewidthPlantModel) (l : ℕ → ℕ) (n : ℕ) :
    0 ≤ M.blockBetaMass l n := by
  unfold blockBetaMass
  apply Finset.sum_nonneg
  intro C _hC
  rw [← sum_tripleBetaScale_eq_graphBetaWeight]
  exact Finset.sum_nonneg fun _triple _htriple ↦
    tripleBetaScale_nonneg M.backgroundDensity_pos n C.shape

/-- **Large connected-mass estimate (paper Lemma 4.5, large part).**

The scale condition makes noise absorb every treewidth-interface overlap;
the fixed-piece aggregate injection then gives the geometric block-mass
majorant eventually. -/
theorem eventually_largeConnectedNoisedBetaMass_le_geometricTail
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate)
    (l : ℕ → ℕ) (hlpos : ∀ n, 0 < l n)
    (hthree : ∀ᶠ n in Filter.atTop, 3 * l n ≤ M.degreeCutoff n)
    (hscale : LittleO
      (fun n ↦ ((M.treewidthBound n : ℝ) + 1) * Real.log (n : ℝ))
      (fun n ↦ (l n : ℝ))) :
    ∀ᶠ n in Filter.atTop,
      M.largeConnectedNoisedBetaMass noise l n ≤
        M.blockBetaMass l n / (1 - M.blockBetaMass l n) := by
  have hexp := eventually_exp_overlapNoiseExponent_le_one noise hscale
  have hblockVan := M.blockBetaMass_vanishes hlow l hthree
  have hblocklt : ∀ᶠ n in Filter.atTop, M.blockBetaMass l n < 1 :=
    hblockVan.eventually_lt_const (by norm_num)
  filter_upwards [hexp, hblocklt, Filter.eventually_gt_atTop (0 : ℕ)] with
      n hnexp hnblock hn
  let Q := M.largeClassDivision (l n) (hlpos n) n
  have habsorb : ∀ a : M.LargeOccurringClass (l n) n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1 :=
    Q.noise_absorbs_overlap noise hn (by
      intro m hm
      simpa only using hnexp m hm)
  exact M.largeConnectedNoisedBetaMass_le_geometricTail_of_division
    noise l hn Q habsorb (M.blockBetaMass_nonneg l n) hnblock

/-- **Connected beta-mass consequence of bounded treewidth.**

This closes paper Lemma 4.5: under the theorem's treewidth/degree scale and
low-degree second-moment premise, the full connected noised leading mass is
`o(1)` for every fixed noise rate. -/
theorem connectedNoisedBetaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthDegreeScale M.treewidthBound M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate) :
    Vanishes (M.connectedNoisedBetaMass noise) := by
  obtain ⟨l, hlpos, hthree, hlscale⟩ := hscale.exists_intermediateScale
  apply M.connectedNoisedBetaMass_vanishes_of_large_bound
    hlow noise l hthree
  exact M.eventually_largeConnectedNoisedBetaMass_le_geometricTail
    hlow noise l hlpos hthree hlscale

end BoundedTreewidthPlantModel

end

end LowDegree
