import LowDegree.Asymptotics.ForestComponentExpansion
import LowDegree.Asymptotics.LargeConnectedBetaMass
import LowDegree.Combinatorics.TreewidthAcyclic

/-!
# Large connected forest mass

This module specializes the aggregate large-support argument to connected
acyclic support shapes.  Such shapes have treewidth at most one, independently
of the treewidth of the ambient planted graph.  This is the graph-sum input
needed for the treewidth-free critical/subcritical theorem.
-/

namespace LowDegree

open scoped BigOperators SimpleGraph
open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

open TreeDecomposition
open AggregateGraphRestriction

namespace BoundedTreewidthPlantModel

/-- Connected acyclic noised mass below the intermediate edge scale. -/
noncomputable def smallConnectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
        C.shape.edgeCount < l n,
    M.noisedBetaClassWeight noise C

/-- Connected acyclic noised mass at or above the intermediate edge scale. -/
noncomputable def largeConnectedForestNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ C : AmbientSupportClass n with
      C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
        l n ≤ C.shape.edgeCount,
    M.noisedBetaClassWeight noise C

private theorem noisedBetaClassWeight_nonneg
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate) {n : ℕ}
    (C : AmbientSupportClass n) :
    0 ≤ M.noisedBetaClassWeight noise C := by
  unfold noisedBetaClassWeight FiniteGraphShape.graphBetaWeight betaWeight
  exact mul_nonneg
    (pow_nonneg (sub_nonneg.mpr noise.2.2.le) _)
    (mul_nonneg
      (div_nonneg
        (div_nonneg (pow_nonneg (Nat.cast_nonneg n) C.shape.edgeCount)
          (pow_nonneg (Nat.cast_nonneg n) C.shape.vertexCount))
        (pow_nonneg M.backgroundDensity_pos.le C.shape.edgeCount))
      (mul_nonneg
        (sq_nonneg (C.shape.nonInducedCopyCount (M.plant n) : ℝ))
        (Nat.cast_nonneg _)))

/-- The connected forest mass splits exactly at an arbitrary edge scale. -/
theorem connectedForestNoisedBetaMass_eq_small_add_large
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) :
    M.connectedForestNoisedBetaMass noise n =
      M.smallConnectedForestNoisedBetaMass noise l n +
        M.largeConnectedForestNoisedBetaMass noise l n := by
  unfold connectedForestNoisedBetaMass
    smallConnectedForestNoisedBetaMass largeConnectedForestNoisedBetaMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _hC
  by_cases hconn : C.shape.graph.Connected
  · by_cases hacyclic : C.shape.graph.IsAcyclic
    · by_cases hedge : C.shape.edgeCount < l n
      · have hedge' : C.representative.1.card < l n := by
          rw [← C.shape_edgeCount_eq_representative_card]
          exact hedge
        have hnle' : ¬l n ≤ C.representative.1.card :=
          Nat.not_le_of_lt hedge'
        simp [hconn, hacyclic, hedge', hnle', noisedBetaClassWeight]
      · have hle : l n ≤ C.shape.edgeCount := Nat.le_of_not_gt hedge
        have hle' : l n ≤ C.representative.1.card := by
          rw [← C.shape_edgeCount_eq_representative_card]
          exact hle
        have hnlt' : ¬C.representative.1.card < l n :=
          Nat.not_lt_of_ge hle'
        simp [hconn, hacyclic, hle', hnlt', noisedBetaClassWeight]
    · simp [hconn, hacyclic]
  · simp [hconn]

/-- The small connected forest mass is bounded by the unrestricted small
connected mass. -/
theorem smallConnectedForestNoisedBetaMass_le_smallConnectedNoisedBetaMass
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) :
    M.smallConnectedForestNoisedBetaMass noise l n ≤
      M.smallConnectedNoisedBetaMass noise l n := by
  unfold smallConnectedForestNoisedBetaMass smallConnectedNoisedBetaMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact ⟨hC.1, hC.2.2⟩
  · intro C _hC _hnot
    exact M.noisedBetaClassWeight_nonneg noise C

/-- The small connected forest contribution vanishes under the low-degree
premise whenever the intermediate scale lies below the degree cutoff. -/
theorem smallConnectedForestNoisedBetaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate)
    (l : ℕ → ℕ)
    (hlD : ∀ᶠ n in atTop, l n ≤ M.degreeCutoff n) :
    Vanishes (M.smallConnectedForestNoisedBetaMass noise l) := by
  have hupper := M.smallConnectedNoisedBetaMass_vanishes hlow noise l hlD
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun C _ ↦ M.noisedBetaClassWeight_nonneg noise C
  · exact Eventually.of_forall fun n ↦
      M.smallConnectedForestNoisedBetaMass_le_smallConnectedNoisedBetaMass
        noise l n
  · exact hupper

/-- Large connected acyclic support classes which actually occur in the
ambient plant. -/
abbrev ForestLargeOccurringClass
    (M : BoundedTreewidthPlantModel) (l n : ℕ) :=
  {C : AmbientSupportClass n //
    C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
      l ≤ C.shape.edgeCount ∧
      0 < C.shape.nonInducedCopyCount (M.plant n)}

/-- Removing zero-weight nonoccurring classes identifies the large forest
mass with the corresponding occurring-class subtype sum. -/
theorem largeConnectedForestNoisedBetaMass_eq_sum_occurring
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) (n : ℕ) :
    M.largeConnectedForestNoisedBetaMass noise l n =
      ∑ a : M.ForestLargeOccurringClass (l n) n,
        M.noisedBetaClassWeight noise a.1 := by
  let p : AmbientSupportClass n → Prop := fun C ↦
    C.shape.graph.Connected ∧ C.shape.graph.IsAcyclic ∧
      l n ≤ C.shape.edgeCount
  let q : AmbientSupportClass n → Prop := fun C ↦
    p C ∧ 0 < C.shape.nonInducedCopyCount (M.plant n)
  calc
    M.largeConnectedForestNoisedBetaMass noise l n =
        ∑ C : AmbientSupportClass n with p C,
          M.noisedBetaClassWeight noise C := by rfl
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
    _ = ∑ a : M.ForestLargeOccurringClass (l n) n,
          M.noisedBetaClassWeight noise a.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (AmbientSupportClass n)).filter q)
        (by intro C; simp [q, p, and_assoc])
        (fun C ↦ M.noisedBetaClassWeight noise C)

/-- A simultaneous width-one block division for every occurring large
connected acyclic support class. -/
structure ForestLargeClassDivision
    (M : BoundedTreewidthPlantModel) (l n : ℕ) where
  pieceCount : M.ForestLargeOccurringClass l n → ℕ
  pieceCount_pos : ∀ a, 0 < pieceCount a
  decomposition : ∀ a,
    OrderedEdgeDecomposition a.1.shape.graph (pieceCount a)
  piece_lower : ∀ a i, l ≤ ((decomposition a).piece i).edgeFinset.card
  piece_upper : ∀ a i,
    ((decomposition a).piece i).edgeFinset.card ≤ 3 * l
  overlap_le : ∀ a, (decomposition a).overlap ≤ 2 * (pieceCount a - 1)

namespace ForestLargeClassDivision

variable {M : BoundedTreewidthPlantModel} {l n : ℕ}
    (Q : M.ForestLargeClassDivision l n)

/-- One fiber of the selected number of decomposition pieces. -/
abbrev PieceCountFiber (m : ℕ) :=
  {a : M.ForestLargeOccurringClass l n // Q.pieceCount a = m}

/-- Regard a piece-count fiber as a fixed-piece division for the aggregate
restriction injection. -/
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

theorem pieceCount_le_sup (a : M.ForestLargeOccurringClass l n) :
    Q.pieceCount a ≤
      (Finset.univ : Finset (M.ForestLargeOccurringClass l n)).sup
        Q.pieceCount := by
  exact Finset.le_sup (Finset.mem_univ a)

/-- The aggregate inequality on one fixed piece-count fiber. -/
theorem fiberNoisedMass_le_blockBetaMass_pow
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.ForestLargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (m : ℕ) :
    (∑ a ∈ (Finset.univ : Finset (M.ForestLargeOccurringClass l n)) with
        Q.pieceCount a = m,
      M.noisedBetaClassWeight noise a.1) ≤
      (M.blockBetaMass (fun _ ↦ l) n) ^ m := by
  have hfixed := M.fixedPieceNoisedClassMass_le_blockBetaMass_pow
    noise (fun _ ↦ l) hn (Q.fixedPieceDivision m) (by
      rintro ⟨a, rfl⟩
      exact habsorb a)
  calc
    (∑ a ∈ (Finset.univ : Finset (M.ForestLargeOccurringClass l n)) with
        Q.pieceCount a = m,
      M.noisedBetaClassWeight noise a.1) =
        ∑ a : Q.PieceCountFiber m,
          M.noisedBetaClassWeight noise a.1.1 := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (M.ForestLargeOccurringClass l n)).filter
          fun a ↦ Q.pieceCount a = m)
        (by intro a; simp)
        (fun a ↦ M.noisedBetaClassWeight noise a.1)
    _ ≤ (M.blockBetaMass (fun _ ↦ l) n) ^ m := hfixed

/-- Sum the fixed-piece bounds over all positive piece counts. -/
theorem occurringNoisedMass_le_geometricPartialSum
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.ForestLargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1) :
    (∑ a : M.ForestLargeOccurringClass l n,
      M.noisedBetaClassWeight noise a.1) ≤
      ∑ m ∈ Finset.Ico 1
          ((Finset.univ : Finset (M.ForestLargeOccurringClass l n)).sup
            Q.pieceCount + 1),
        (M.blockBetaMass (fun _ ↦ l) n) ^ m := by
  let topCount :=
    (Finset.univ : Finset (M.ForestLargeOccurringClass l n)).sup
      Q.pieceCount
  have hfiber :
      (∑ m ∈ Finset.Ico 1 (topCount + 1),
        ∑ a ∈ (Finset.univ : Finset (M.ForestLargeOccurringClass l n)) with
          Q.pieceCount a = m,
          M.noisedBetaClassWeight noise a.1) =
        ∑ a : M.ForestLargeOccurringClass l n,
          M.noisedBetaClassWeight noise a.1 := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    have hfilter :
        (Finset.univ : Finset (M.ForestLargeOccurringClass l n)).filter
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

/-- The complete occurring large-forest mass is bounded by the nonempty
geometric series in the block mass. -/
theorem occurringNoisedMass_le_geometricTail
    (noise : NoiseRate) (hn : 0 < n)
    (habsorb : ∀ a : M.ForestLargeOccurringClass l n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (hblock0 : 0 ≤ M.blockBetaMass (fun _ ↦ l) n)
    (hblock1 : M.blockBetaMass (fun _ ↦ l) n < 1) :
    (∑ a : M.ForestLargeOccurringClass l n,
      M.noisedBetaClassWeight noise a.1) ≤
      M.blockBetaMass (fun _ ↦ l) n /
        (1 - M.blockBetaMass (fun _ ↦ l) n) := by
  let b := M.blockBetaMass (fun _ ↦ l) n
  let topCount :=
    (Finset.univ : Finset (M.ForestLargeOccurringClass l n)).sup
      Q.pieceCount
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

end ForestLargeClassDivision

/-- A decomposition of a graph with at least one edge has a positive number
of pieces. -/
private theorem forestOrderedEdgeDecomposition_pieceCount_pos
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

/-- Choose the width-one bounded-overlap division simultaneously for all
large occurring connected acyclic classes. -/
noncomputable def forestLargeClassDivision
    (M : BoundedTreewidthPlantModel) (l : ℕ) (hl : 0 < l) (n : ℕ) :
    M.ForestLargeClassDivision l n := by
  let Data : M.ForestLargeOccurringClass l n → Type := fun a ↦
    Σ m : ℕ, {P : OrderedEdgeDecomposition a.1.shape.graph m //
      (∀ i : Fin m,
        l ≤ (P.piece i).edgeFinset.card ∧
          (P.piece i).edgeFinset.card ≤ 3 * l) ∧
      P.overlap ≤ 2 * (m - 1)}
  have hData : ∀ a : M.ForestLargeOccurringClass l n,
      Nonempty (Data a) := by
    intro a
    have htotal : l ≤ a.1.shape.graph.edgeFinset.card := by
      calc
        l ≤ a.1.shape.edgeCount := a.property.2.2.1
        _ = a.1.shape.graph.edgeFinset.card := by
          rw [FiniteGraphShape.edgeCount_eq_ncard]
          exact Set.ncard_eq_toFinset_card' _
    obtain ⟨m, P, hpieces, hoverlap⟩ :=
      TreeDecomposition.connectedAcyclic_exists_boundedOverlap_orderedEdgeDecomposition
        a.property.1 a.property.2.1 hl htotal
    exact ⟨⟨m, ⟨P, hpieces, hoverlap⟩⟩⟩
  let data : ∀ a : M.ForestLargeOccurringClass l n, Data a := fun a ↦
    Classical.choice (hData a)
  refine
    { pieceCount := fun a ↦ (data a).1
      pieceCount_pos := ?_
      decomposition := fun a ↦ (data a).2.1
      piece_lower := ?_
      piece_upper := ?_
      overlap_le := ?_ }
  · intro a
    apply forestOrderedEdgeDecomposition_pieceCount_pos (data a).2.1
    intro hbot
    have hedge0 : a.1.shape.graph.edgeFinset.card = 0 := by simp [hbot]
    have htotal : l ≤ a.1.shape.graph.edgeFinset.card := by
      calc
        l ≤ a.1.shape.edgeCount := a.property.2.2.1
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

/-- Exponential rewriting of the width-one overlap/noise product. -/
private theorem forestNoiseOverlapProduct_eq_exp
    (noise : NoiseRate) (l : ℕ) {n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) :
    (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ (2 * (m - 1)) =
      Real.exp
        (overlapNoiseExponent (noise : ℝ) (fun _ ↦ 1)
          (fun _ ↦ l) n m) := by
  have hq : 0 < 1 - (noise : ℝ) := sub_pos.mpr noise.2.2
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have qpow :
      (1 - (noise : ℝ)) ^ (2 * m * l) =
        Real.exp
          (Real.log (1 - (noise : ℝ)) * ((2 * m * l : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_def_of_pos hq _
  have npow :
      (n : ℝ) ^ (2 * (m - 1)) =
        Real.exp
          (Real.log (n : ℝ) * (((2 * (m - 1) : ℕ)) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_def_of_pos hnreal _
  rw [qpow, npow, ← Real.exp_add]
  apply congrArg Real.exp
  unfold overlapNoiseExponent
  push_cast [Nat.cast_sub hm]
  ring

/-- Fixed-rate noise absorbs every selected width-one interface overlap. -/
theorem ForestLargeClassDivision.noise_absorbs_overlap
    {M : BoundedTreewidthPlantModel} {l n : ℕ}
    (Q : M.ForestLargeClassDivision l n) (noise : NoiseRate)
    (hn : 0 < n)
    (hexp : ∀ m : ℕ, 1 ≤ m →
      Real.exp
        (overlapNoiseExponent (noise : ℝ) (fun _ ↦ 1)
          (fun _ ↦ l) n m) ≤ 1) :
    ∀ a : M.ForestLargeOccurringClass l n,
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
      (n : ℝ) ^ P.overlap ≤ (n : ℝ) ^ (2 * (m - 1)) :=
    pow_le_pow_right₀ hn1 (Q.overlap_le a)
  calc
    (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ P.overlap ≤
      (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ P.overlap :=
      mul_le_mul_of_nonneg_right hqpow (pow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ (1 - (noise : ℝ)) ^ (2 * m * l) *
        (n : ℝ) ^ (2 * (m - 1)) :=
      mul_le_mul_of_nonneg_left hnpow (pow_nonneg hq0 _)
    _ = Real.exp
        (overlapNoiseExponent (noise : ℝ) (fun _ ↦ 1)
          (fun _ ↦ l) n m) :=
      forestNoiseOverlapProduct_eq_exp noise l hn hm
    _ ≤ 1 := hexp m hm

/-- Finite large-forest inequality supplied by a simultaneous width-one
division whose overlaps are absorbed by noise. -/
theorem largeConnectedForestNoisedBetaMass_le_geometricTail_of_division
    (M : BoundedTreewidthPlantModel) (noise : NoiseRate)
    (l : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (Q : M.ForestLargeClassDivision (l n) n)
    (habsorb : ∀ a : M.ForestLargeOccurringClass (l n) n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1)
    (hblock0 : 0 ≤ M.blockBetaMass l n)
    (hblock1 : M.blockBetaMass l n < 1) :
    M.largeConnectedForestNoisedBetaMass noise l n ≤
      M.blockBetaMass l n / (1 - M.blockBetaMass l n) := by
  rw [M.largeConnectedForestNoisedBetaMass_eq_sum_occurring noise l n]
  simpa only using
    Q.occurringNoisedMass_le_geometricTail noise hn habsorb hblock0 hblock1

/-- The width-one overlap estimate gives the large connected forest bound
eventually. -/
theorem eventually_largeConnectedForestNoisedBetaMass_le_geometricTail
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate)
    (l : ℕ → ℕ) (hlpos : ∀ n, 0 < l n)
    (hthree : ∀ᶠ n in atTop, 3 * l n ≤ M.degreeCutoff n)
    (hscale : LittleO
      (fun n ↦ (((1 : ℕ) : ℝ) + 1) * Real.log (n : ℝ))
      (fun n ↦ (l n : ℝ))) :
    ∀ᶠ n in atTop,
      M.largeConnectedForestNoisedBetaMass noise l n ≤
        M.blockBetaMass l n / (1 - M.blockBetaMass l n) := by
  have hexp := eventually_exp_overlapNoiseExponent_le_one
    (k := fun _ ↦ 1) noise hscale
  have hblockVan := M.blockBetaMass_vanishes hlow l hthree
  have hblocklt : ∀ᶠ n in atTop, M.blockBetaMass l n < 1 :=
    hblockVan.eventually_lt_const (by norm_num)
  filter_upwards [hexp, hblocklt, Filter.eventually_gt_atTop (0 : ℕ)] with
      n hnexp hnblock hn
  let Q := M.forestLargeClassDivision (l n) (hlpos n) n
  have habsorb : ∀ a : M.ForestLargeOccurringClass (l n) n,
      (1 - (noise : ℝ)) ^ (2 * a.1.shape.edgeCount) *
        (n : ℝ) ^ (Q.decomposition a).overlap ≤ 1 :=
    Q.noise_absorbs_overlap noise hn (by
      intro m hm
      simpa only using hnexp m hm)
  exact M.largeConnectedForestNoisedBetaMass_le_geometricTail_of_division
    noise l hn Q habsorb (M.blockBetaMass_nonneg l n) hnblock

/-- The connected acyclic noised beta mass vanishes under the width-one
degree scale, with no treewidth hypothesis on the ambient plant. -/
theorem connectedForestNoisedBetaMass_vanishes_of_widthOneScale
    (M : BoundedTreewidthPlantModel)
    (hscale : TreewidthDegreeScale (fun _ ↦ 1) M.degreeCutoff)
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate) :
    Vanishes (M.connectedForestNoisedBetaMass noise) := by
  obtain ⟨l, hlpos, hthree, hlscale⟩ := hscale.exists_intermediateScale
  have hsmall := M.smallConnectedForestNoisedBetaMass_vanishes
    hlow noise l
    (hthree.mono fun n hn ↦
      (Nat.le_mul_of_pos_left _ (by norm_num)).trans hn)
  have hblock := M.blockBetaMass_vanishes hlow l hthree
  have hlarge :=
    M.eventually_largeConnectedForestNoisedBetaMass_le_geometricTail
      hlow noise l hlpos hthree hlscale
  apply connectedNoisedMass_vanishes_of_decomposition
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun C _ ↦ M.noisedBetaClassWeight_nonneg noise C
  · exact hsmall
  · exact hblock
  · filter_upwards [hlarge] with n hn
    rw [M.connectedForestNoisedBetaMass_eq_small_add_large noise l n]
    exact add_le_add_left hn _

/-- The paper's assumption `Dₙ = ω(log n)` supplies the constant-width-one
scale needed for connected forest supports. -/
theorem widthOneScale_of_degree_isOmega_log
    (M : BoundedTreewidthPlantModel)
    (hD : Omega (fun n ↦ (M.degreeCutoff n : ℝ))
      (fun n ↦ Real.log (n : ℝ))) :
    TreewidthDegreeScale (fun _ ↦ 1) M.degreeCutoff := by
  change
    (fun n : ℕ ↦ (((1 : ℕ) : ℝ) + 1) * Real.log (n : ℝ)) =o[atTop]
      (fun n ↦ (M.degreeCutoff n : ℝ))
  change
    (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n ↦ (M.degreeCutoff n : ℝ)) at hD
  simpa only [Nat.cast_one, one_add_one_eq_two] using hD.const_mul_left 2

/-- Treewidth-free connected-forest consequence under `Dₙ = ω(log n)`. -/
theorem connectedForestNoisedBetaMass_vanishes
    (M : BoundedTreewidthPlantModel)
    (hD : Omega (fun n ↦ (M.degreeCutoff n : ℝ))
      (fun n ↦ Real.log (n : ℝ)))
    (hlow : TendsToOne M.lowDegreeNormSq) (noise : NoiseRate) :
    Vanishes (M.connectedForestNoisedBetaMass noise) :=
  M.connectedForestNoisedBetaMass_vanishes_of_widthOneScale
    (M.widthOneScale_of_degree_isOmega_log hD) hlow noise

/-- **Paper Theorem 1.2 (critical and subcritical backgrounds).**

No treewidth scale is assumed.  The administrative treewidth witness carried
by `BoundedTreewidthPlantModel` is unused: connected forest support shapes are
decomposed at width one, while Lemma 4.6 controls the discarded cyclic part.
-/
theorem subcritical_lowDegree_to_tv
    (M : BoundedTreewidthPlantModel)
    (hc_one : M.backgroundDensity ≤ 1)
    (hD : Omega (fun n ↦ (M.degreeCutoff n : ℝ))
      (fun n ↦ Real.log (n : ℝ)))
    (hlow : TendsToOne M.lowDegreeNormSq) :
    ∀ noise : NoiseRate, Vanishes (M.noisedTotalVariation noise) := by
  intro noise
  have hconnected : Vanishes (M.connectedForestNoisedBetaMass noise) :=
    M.connectedForestNoisedBetaMass_vanishes hD hlow noise
  have hforestBeta : Vanishes (M.forestNoisedBetaMass noise) :=
    M.forestNoisedBetaMass_vanishes_of_connectedForestNoisedBetaMass
      hlow noise hconnected
  have hforestNorm : TendsToOne (M.forestTruncatedNormSq noise) :=
    M.forestTruncatedNormSq_tendsToOne_of_betaMass_vanishes
      hlow noise hforestBeta
  exact M.subcriticalTotalVariation_vanishes_of_forestNorm
    hc_one noise hD hlow hforestNorm

end BoundedTreewidthPlantModel

/-- Root-namespace paper-facing alias for Theorem 1.2. -/
theorem subcritical_lowDegree_to_tv
    (M : BoundedTreewidthPlantModel)
    (hc_one : M.backgroundDensity ≤ 1)
    (hD : Omega (fun n ↦ (M.degreeCutoff n : ℝ))
      (fun n ↦ Real.log (n : ℝ)))
    (hlow : TendsToOne M.lowDegreeNormSq) :
    ∀ noise : NoiseRate, Vanishes (M.noisedTotalVariation noise) :=
  M.subcritical_lowDegree_to_tv hc_one hD hlow

end

end LowDegree
