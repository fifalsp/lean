import LowDegree.DeletedPlant
import LowDegree.RandomPlant
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Concrete forest truncation for the deleted planted graph

This file realizes the finite forest-truncation step used in Theorem 1.2.
First choose a uniform ambient permutation of a deterministic plant and retain
each of its edges independently with probability `1 - ε`.  The resulting
`retainedPlantLaw` is an honest finite law on edge sets, and its observation
likelihood is exactly the deleted/noised planted likelihood.

An ambient edge finset is then interpreted as a simple graph.  Acyclicity is a
hereditary predicate on these finsets, so the generic all-or-nothing truncation
from `RandomPlant.lean` applies.  The truncated mixture has only forest outputs,
has dominated containment probabilities and Fourier coefficients, has zero
coefficients on cyclic supports, and differs in total variation from the
untruncated observation law by at most the retained plant's cycle probability.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem sum_deletionWeight_over_all
    {E : Type*} [Fintype E] [DecidableEq E]
    (ε : ℝ) (A : Finset E) :
    (∑ R : Finset E, if R ⊆ A then deletionWeight ε A R else 0) = 1 := by
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun R : Finset E ↦ R ⊆ A) = A.powerset := by
    ext R
    simp
  rw [hfilter, sum_deletionWeight]

/-- The actual retained-edge-set law: first choose a uniform ambient
permutation, then retain every edge of that permuted plant independently with
probability `1 - ε`. -/
noncomputable def retainedPlantLaw {n : ℕ} (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) : FiniteLaw (Finset (AmbientEdge n)) where
  mass R := ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
    if R ⊆ permutedPlantEdges plant σ then
      deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
    else 0
  mass_nonneg R := Finset.sum_nonneg fun σ _ ↦ by
    apply mul_nonneg (uniformPermutationWeight_pos n).le
    split
    · exact deletionWeight_nonneg ε.2.1.le ε.2.2.le _ _
    · exact le_rfl
  sum_mass := by
    calc
      (∑ R : Finset (AmbientEdge n),
          ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
            if R ⊆ permutedPlantEdges plant σ then
              deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
            else 0) =
          ∑ σ : Equiv.Perm (Fin n),
            ∑ R : Finset (AmbientEdge n), uniformPermutationWeight n *
              if R ⊆ permutedPlantEdges plant σ then
                deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
              else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [← Finset.mul_sum, sum_deletionWeight_over_all, mul_one]
      _ = 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul, uniformPermutationWeight]
        have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos_iff.mpr
            ⟨Equiv.refl (Fin n)⟩ : 0 < Fintype.card (Equiv.Perm (Fin n))).ne'
        rw [Finset.card_univ]
        field_simp

@[simp]
theorem retainedPlantLaw_mass {n : ℕ} (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) (R : Finset (AmbientEdge n)) :
    (retainedPlantLaw ε plant).mass R =
      ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
        if R ⊆ permutedPlantEdges plant σ then
          deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
        else 0 := rfl

/-- Mixing fixed-forcing likelihoods against the retained-edge law gives the
deletion-before-superposition likelihood. -/
theorem randomForcedLikelihood_retainedPlantLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    randomForcedLikelihood θ (retainedPlantLaw ε plant) =
      deletedPlantedLikelihood θ ε plant := by
  funext x
  unfold randomForcedLikelihood deletedPlantedLikelihood deletedForcedLikelihood
  simp only [retainedPlantLaw_mass]
  calc
    (∑ R : Finset (AmbientEdge n),
        (∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
          if R ⊆ permutedPlantEdges plant σ then
            deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
          else 0) * forcedLikelihood θ R x) =
        ∑ R : Finset (AmbientEdge n),
          ∑ σ : Equiv.Perm (Fin n),
            (uniformPermutationWeight n *
              if R ⊆ permutedPlantEdges plant σ then
                deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
              else 0) * forcedLikelihood θ R x := by
                apply Finset.sum_congr rfl
                intro R _
                rw [Finset.sum_mul]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ R : Finset (AmbientEdge n),
            (uniformPermutationWeight n *
              if R ⊆ permutedPlantEdges plant σ then
                deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R
              else 0) * forcedLikelihood θ R x := by
                rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
          ∑ R ∈ (permutedPlantEdges plant σ).powerset,
            deletionWeight (ε : ℝ) (permutedPlantEdges plant σ) R *
              forcedLikelihood θ R x := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
        have hpow : (permutedPlantEdges plant σ).powerset =
            (Finset.univ : Finset (Finset (AmbientEdge n))).filter
              (fun R ↦ R ⊆ permutedPlantEdges plant σ) := by
          ext R
          simp
        rw [hpow, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro R _
        by_cases hR : R ⊆ permutedPlantEdges plant σ
        · rw [if_pos hR, if_pos hR]
          ring
        · rw [if_neg hR, if_neg hR]
          ring

/-- Equivalently, the retained-edge law generates the edge-noised planted
likelihood. -/
theorem randomForcedLikelihood_retainedPlantLaw_eq_noisedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    randomForcedLikelihood θ (retainedPlantLaw ε plant) =
      noisedLikelihood θ ε plant := by
  rw [randomForcedLikelihood_retainedPlantLaw,
    deletedPlantedLikelihood_eq_noisedLikelihood]

/-- Forget the proof that an ambient edge belongs to the complete graph and
view a finset of ambient edges as a set of unordered vertex pairs. -/
def ambientEdgeSet {n : ℕ} (A : Finset (AmbientEdge n)) : Set (Sym2 (Fin n)) :=
  {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet,
    (⟨e, h⟩ : AmbientEdge n) ∈ A}

/-- The spanning simple graph whose edge set is `A`. -/
def graphOfAmbientEdges {n : ℕ} (A : Finset (AmbientEdge n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (ambientEdgeSet A)

@[simp]
theorem mem_graphOfAmbientEdges_edgeSet_iff {n : ℕ}
    (A : Finset (AmbientEdge n)) (e : AmbientEdge n) :
    (e : Sym2 (Fin n)) ∈ (graphOfAmbientEdges A).edgeSet ↔ e ∈ A := by
  simp only [graphOfAmbientEdges, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_diff, ambientEdgeSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h, he⟩, _⟩
    simpa using he
  · intro he
    exact ⟨⟨e.property, he⟩,
      (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet e.property⟩

theorem ambientEdgeSet_mono {n : ℕ} {A B : Finset (AmbientEdge n)}
    (hAB : A ⊆ B) : ambientEdgeSet A ⊆ ambientEdgeSet B := by
  rintro e ⟨he, hA⟩
  exact ⟨he, hAB hA⟩

theorem graphOfAmbientEdges_mono {n : ℕ} {A B : Finset (AmbientEdge n)}
    (hAB : A ⊆ B) : graphOfAmbientEdges A ≤ graphOfAmbientEdges B := by
  exact SimpleGraph.fromEdgeSet_mono (ambientEdgeSet_mono hAB)

/-- A finset of ambient edges is a forest when its associated spanning graph
is acyclic. -/
def IsForestEdgeSet {n : ℕ} (A : Finset (AmbientEdge n)) : Prop :=
  (graphOfAmbientEdges A).IsAcyclic

theorem isForestEdgeSet_empty (n : ℕ) :
    IsForestEdgeSet (∅ : Finset (AmbientEdge n)) := by
  change (SimpleGraph.fromEdgeSet
    (ambientEdgeSet (∅ : Finset (AmbientEdge n)))).IsAcyclic
  have hempty : ambientEdgeSet (∅ : Finset (AmbientEdge n)) = ∅ := by
    ext e
    simp [ambientEdgeSet]
  rw [hempty, SimpleGraph.fromEdgeSet_empty]
  exact SimpleGraph.isAcyclic_bot

/-- Acyclicity is hereditary under taking subsets of an ambient edge finset. -/
theorem isForestEdgeSet_hereditary {n : ℕ}
    {A B : Finset (AmbientEdge n)} (hAB : A ⊆ B)
    (hB : IsForestEdgeSet B) : IsForestEdgeSet A := by
  exact SimpleGraph.IsAcyclic.anti (graphOfAmbientEdges_mono hAB) hB

/-- The exact all-or-nothing forest truncation: keep an acyclic retained plant
unchanged and replace a cyclic retained plant by the empty edge set. -/
noncomputable def forestTruncatedRetainedPlantLaw {n : ℕ} (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) : FiniteLaw (Finset (AmbientEdge n)) :=
  truncatePlantLaw (retainedPlantLaw ε plant) IsForestEdgeSet

theorem forestTruncatePlantSet_isForest {n : ℕ}
    (A : Finset (AmbientEdge n)) :
    IsForestEdgeSet (truncatePlantSet IsForestEdgeSet A) := by
  exact truncatePlantSet_good IsForestEdgeSet (isForestEdgeSet_empty n) A

/-- Every cyclic edge set has zero mass under the forest-truncated law. -/
theorem forestTruncatedRetainedPlantLaw_mass_eq_zero_of_not_isForest
    {n : ℕ} (ε : NoiseRate) (plant : SimpleGraph (Fin n))
    (A : Finset (AmbientEdge n)) (hA : ¬IsForestEdgeSet A) :
    (forestTruncatedRetainedPlantLaw ε plant).mass A = 0 := by
  unfold forestTruncatedRetainedPlantLaw truncatePlantLaw
  rw [FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro B _
  by_cases hBA : truncatePlantSet IsForestEdgeSet B = A
  · have hgood : IsForestEdgeSet A := by
      rw [← hBA]
      exact forestTruncatePlantSet_isForest B
    exact (hA hgood).elim
  · rw [if_neg hBA]

/-- Thus every output in the support of the forest-truncated law is acyclic. -/
theorem forestTruncatedRetainedPlantLaw_mass_pos_isForest
    {n : ℕ} (ε : NoiseRate) (plant : SimpleGraph (Fin n))
    (A : Finset (AmbientEdge n))
    (hA : 0 < (forestTruncatedRetainedPlantLaw ε plant).mass A) :
    IsForestEdgeSet A := by
  by_contra hforest
  rw [forestTruncatedRetainedPlantLaw_mass_eq_zero_of_not_isForest
    ε plant A hforest] at hA
  exact lt_irrefl 0 hA

/-- Forest truncation can only decrease the probability of containing any
fixed support. -/
theorem forestTruncatedContainmentProbability_le {n : ℕ}
    (ε : NoiseRate) (plant : SimpleGraph (Fin n))
    (S : Finset (AmbientEdge n)) :
    randomPlantContainmentProbability
        (forestTruncatedRetainedPlantLaw ε plant) S ≤
      randomPlantContainmentProbability (retainedPlantLaw ε plant) S := by
  exact randomPlantContainmentProbability_truncate_le
    (retainedPlantLaw ε plant) IsForestEdgeSet S

/-- Observation likelihood generated by the all-or-nothing forest-truncated
retained plant. -/
noncomputable def forestTruncatedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    BooleanConfiguration (AmbientEdge n) → ℝ :=
  randomForcedLikelihood θ (forestTruncatedRetainedPlantLaw ε plant)

/-- Every Fourier coefficient of the forest-truncated likelihood is dominated
by the corresponding coefficient of the untruncated noised likelihood. -/
theorem fourierCoeff_forestTruncatedLikelihood_le_noisedLikelihood
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) :
    fourierCoeff θ (forestTruncatedLikelihood θ ε plant) S ≤
      fourierCoeff θ (noisedLikelihood θ ε plant) S := by
  have h := fourierCoeff_truncated_randomForcedLikelihood_le
    θ (retainedPlantLaw ε plant) IsForestEdgeSet S
  rw [randomForcedLikelihood_retainedPlantLaw_eq_noisedLikelihood] at h
  exact h

/-- A cyclic Fourier support has coefficient zero after forest truncation. -/
theorem fourierCoeff_forestTruncatedLikelihood_eq_zero_of_cyclic
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n))
    (hcycle : ¬IsForestEdgeSet S) :
    fourierCoeff θ (forestTruncatedLikelihood θ ε plant) S = 0 := by
  exact fourierCoeff_truncated_randomForcedLikelihood_eq_zero_of_not_good
    θ (retainedPlantLaw ε plant) IsForestEdgeSet
      (isForestEdgeSet_empty n)
      (fun {A B} hAB hB ↦ isForestEdgeSet_hereditary
        (A := A) (B := B) hAB hB)
      S hcycle

/-- The observation law generated by the forest-truncated retained plant. -/
noncomputable def forestTruncatedObservationLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  randomForcedLaw θ (forestTruncatedRetainedPlantLaw ε plant)

theorem randomForcedLaw_retainedPlantLaw_eq_deletedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    randomForcedLaw θ (retainedPlantLaw ε plant) =
      deletedPlantedLaw θ ε plant := by
  apply FiniteLaw.ext_mass
  funext x
  change bernoulliProductMass θ x *
      randomForcedLikelihood θ (retainedPlantLaw ε plant) x =
    bernoulliProductMass θ x * deletedPlantedLikelihood θ ε plant x
  rw [randomForcedLikelihood_retainedPlantLaw]

theorem randomForcedLaw_retainedPlantLaw_eq_noisedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    randomForcedLaw θ (retainedPlantLaw ε plant) =
      noisedPlantedLaw θ ε plant := by
  rw [randomForcedLaw_retainedPlantLaw_eq_deletedPlantedLaw,
    deletedPlantedLaw_eq_noisedPlantedLaw]

/-- Probability that the retained planted edge set contains a cycle. -/
noncomputable def retainedPlantCycleProbability {n : ℕ}
    (ε : NoiseRate) (plant : SimpleGraph (Fin n)) : ℝ :=
  (retainedPlantLaw ε plant).prob
    ((Finset.univ : Finset (Finset (AmbientEdge n))).filter
      (fun A ↦ ¬IsForestEdgeSet A))

/-! ## A finite coupling bound for all-or-nothing truncation -/

theorem randomForcedLikelihood_truncatePlantLaw_apply
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (p : FiniteLaw (Finset E))
    (good : Finset E → Prop) (x : BooleanConfiguration E) :
    randomForcedLikelihood θ (truncatePlantLaw p good) x =
      ∑ A : Finset E, p.mass A *
        forcedLikelihood θ (truncatePlantSet good A) x := by
  change (truncatePlantLaw p good).expect
      (fun A ↦ forcedLikelihood θ A x) = _
  rw [truncatePlantLaw, FiniteLaw.expect_map]
  rfl

theorem randomForcedLikelihood_sub_truncatePlantLaw_apply
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (p : FiniteLaw (Finset E))
    (good : Finset E → Prop) (x : BooleanConfiguration E) :
    randomForcedLikelihood θ p x -
        randomForcedLikelihood θ (truncatePlantLaw p good) x =
      ∑ A ∈ (Finset.univ : Finset (Finset E)).filter (fun A ↦ ¬good A),
        p.mass A * (forcedLikelihood θ A x - 1) := by
  rw [randomForcedLikelihood_truncatePlantLaw_apply]
  unfold randomForcedLikelihood
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ A : Finset E, (
        p.mass A * forcedLikelihood θ A x -
          p.mass A * forcedLikelihood θ (truncatePlantSet good A) x)) =
        ∑ A : Finset E, if ¬good A then
          p.mass A * (forcedLikelihood θ A x - 1) else 0 := by
            apply Finset.sum_congr rfl
            intro A _
            by_cases hA : good A
            · simp [hA, truncatePlantSet]
            · simp [hA, truncatePlantSet, forcedLikelihood]
              ring
    _ = ∑ A ∈ (Finset.univ : Finset (Finset E)).filter (fun A ↦ ¬good A),
        p.mass A * (forcedLikelihood θ A x - 1) := by
          rw [Finset.sum_filter]

private theorem sum_nullMass_mul_forcedLikelihood_add_one
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E) :
    ∑ x : BooleanConfiguration E, bernoulliProductMass θ x *
      (forcedLikelihood θ A x + 1) = 2 := by
  calc
    (∑ x : BooleanConfiguration E, bernoulliProductMass θ x *
        (forcedLikelihood θ A x + 1)) =
        (∑ x, bernoulliProductMass θ x * forcedLikelihood θ A x) +
          ∑ x, bernoulliProductMass θ x := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = 2 := by
      rw [show (∑ x, bernoulliProductMass θ x * forcedLikelihood θ A x) = 1 by
          simpa only [bernoulliExpectation] using
            bernoulliExpectation_forcedLikelihood θ A,
        sum_bernoulliProductMass]
      norm_num

/-- For any random forced set and any all-or-nothing truncation, the
observation-law TV cost is at most the probability that truncation fires. -/
theorem randomForcedLaw_tv_truncatePlantLaw_le_badProbability
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (p : FiniteLaw (Finset E))
    (good : Finset E → Prop) :
    (randomForcedLaw θ p).tv
        (randomForcedLaw θ (truncatePlantLaw p good)) ≤
      p.prob ((Finset.univ : Finset (Finset E)).filter (fun A ↦ ¬good A)) := by
  let bad : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter (fun A ↦ ¬good A)
  have hpoint (x : BooleanConfiguration E) :
      |(randomForcedLaw θ p).mass x -
          (randomForcedLaw θ (truncatePlantLaw p good)).mass x| ≤
        bernoulliProductMass θ x *
          ∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x + 1) := by
    rw [randomForcedLaw_mass, randomForcedLaw_mass]
    change |bernoulliProductMass θ x * randomForcedLikelihood θ p x -
        bernoulliProductMass θ x *
          randomForcedLikelihood θ (truncatePlantLaw p good) x| ≤ _
    rw [← mul_sub, randomForcedLikelihood_sub_truncatePlantLaw_apply]
    change |bernoulliProductMass θ x *
        ∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x - 1)| ≤ _
    rw [abs_mul, abs_of_nonneg (bernoulliProductMass_nonneg θ x)]
    apply mul_le_mul_of_nonneg_left _ (bernoulliProductMass_nonneg θ x)
    calc
      |∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x - 1)| ≤
          ∑ A ∈ bad, |p.mass A * (forcedLikelihood θ A x - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x + 1) := by
        apply Finset.sum_le_sum
        intro A _
        rw [abs_mul, abs_of_nonneg (p.mass_nonneg A)]
        apply mul_le_mul_of_nonneg_left _ (p.mass_nonneg A)
        calc
          |forcedLikelihood θ A x - 1| ≤
              |forcedLikelihood θ A x| + |(1 : ℝ)| := abs_sub _ _
          _ = forcedLikelihood θ A x + 1 := by
            rw [abs_of_nonneg (forcedLikelihood_nonneg θ A x)]
            norm_num
  unfold FiniteLaw.tv
  calc
    (1 / 2 : ℝ) * ∑ x,
        |(randomForcedLaw θ p).mass x -
          (randomForcedLaw θ (truncatePlantLaw p good)).mass x| ≤
        (1 / 2 : ℝ) * ∑ x, bernoulliProductMass θ x *
          ∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Finset.sum_le_sum fun x _ ↦ hpoint x
    _ = (1 / 2 : ℝ) * ∑ A ∈ bad, p.mass A *
          ∑ x, bernoulliProductMass θ x *
            (forcedLikelihood θ A x + 1) := by
      congr 1
      calc
        (∑ x, bernoulliProductMass θ x *
            ∑ A ∈ bad, p.mass A * (forcedLikelihood θ A x + 1)) =
            ∑ x, ∑ A ∈ bad, bernoulliProductMass θ x *
              (p.mass A * (forcedLikelihood θ A x + 1)) := by
                apply Finset.sum_congr rfl
                intro x _
                rw [Finset.mul_sum]
        _ = ∑ A ∈ bad, ∑ x, bernoulliProductMass θ x *
              (p.mass A * (forcedLikelihood θ A x + 1)) := by
                rw [Finset.sum_comm]
        _ = ∑ A ∈ bad, p.mass A *
              ∑ x, bernoulliProductMass θ x *
                (forcedLikelihood θ A x + 1) := by
                apply Finset.sum_congr rfl
                intro A _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
    _ = ∑ A ∈ bad, p.mass A := by
      simp_rw [sum_nullMass_mul_forcedLikelihood_add_one]
      rw [← Finset.sum_mul]
      ring
    _ = p.prob ((Finset.univ : Finset (Finset E)).filter (fun A ↦ ¬good A)) := by
      rfl

/-- Concrete coupling bound before identifying the untruncated observation
law with the noised planted law. -/
theorem retainedObservationLaw_tv_forestTruncated_le_cycleProbability
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    (randomForcedLaw θ (retainedPlantLaw ε plant)).tv
        (forestTruncatedObservationLaw θ ε plant) ≤
      retainedPlantCycleProbability ε plant := by
  exact randomForcedLaw_tv_truncatePlantLaw_le_badProbability
    θ (retainedPlantLaw ε plant) IsForestEdgeSet

/-- The observation-law TV between the noised/untruncated mixture and the
forest-truncated mixture is bounded by the retained plant's cycle probability. -/
theorem noisedPlantedLaw_tv_forestTruncated_le_cycleProbability
    {n : ℕ} (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    (noisedPlantedLaw θ ε plant).tv
        (forestTruncatedObservationLaw θ ε plant) ≤
      retainedPlantCycleProbability ε plant := by
  rw [← randomForcedLaw_retainedPlantLaw_eq_noisedPlantedLaw]
  exact retainedObservationLaw_tv_forestTruncated_le_cycleProbability
    θ ε plant

end

end LowDegree
