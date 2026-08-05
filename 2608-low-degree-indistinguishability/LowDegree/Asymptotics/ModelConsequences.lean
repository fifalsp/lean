import LowDegree.Asymptotics.LeadingTerm
import LowDegree.Combinatorics.GraphCopies
import LowDegree.Main
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Concrete model consequences of low-degree boundedness

This file derives the degree-one consequence (paper Lemma 3.2) directly from
the finite planted likelihood.  In particular, the hypothesis is the actual
low-degree norm of `BoundedTreewidthPlantModel`, rather than an abstract scalar
profile supplied with a separate `K₂`-coefficient bound.
-/

namespace LowDegree

open Filter Topology

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Relabeling a spanning plant preserves its number of forced coordinates. -/
theorem card_permutedPlantEdges {n : ℕ}
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (permutedPlantEdges plant σ).card = plant.edgeFinset.card := by
  classical
  letI : DecidableRel (permutedPlant plant σ).Adj :=
    fun _ _ ↦ SimpleGraph.instDecidableMapAdj (G := plant)
      (f := σ.toEmbedding)
  let includeEdge : (permutedPlant plant σ).edgeSet ↪ AmbientEdge n :=
    { toFun := fun e ↦ ⟨e.1, SimpleGraph.edgeSet_mono le_top e.2⟩
      inj' := by
        intro e f h
        apply Subtype.ext
        exact congrArg (fun x : AmbientEdge n ↦ x.1) h }
  have hedgeFinset :
      permutedPlantEdges plant σ =
        (Finset.univ : Finset (permutedPlant plant σ).edgeSet).map includeEdge := by
    ext e
    rw [mem_permutedPlantEdges_iff]
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro he
      exact ⟨⟨e.1, he⟩, Subtype.ext rfl⟩
    · rintro ⟨a, ha⟩
      have hval : a.1 = e.1 := congrArg Subtype.val ha
      simpa only [hval] using a.2
  rw [hedgeFinset, Finset.card_map, Finset.card_univ]
  calc
    Fintype.card (permutedPlant plant σ).edgeSet =
        Fintype.card plant.edgeSet := by
      exact (Fintype.card_congr
        (SimpleGraph.Iso.mapEdgeSet (SimpleGraph.Iso.map σ plant))).symm
    _ = plant.edgeFinset.card := SimpleGraph.edgeFinset_card.symm

/-- Double-counting incidences between ambient edges and relabelings of the
plant.  The left side sums the number of relabelings containing each fixed
edge; the right side first chooses a relabeling and then one of its plant
edges. -/
theorem sum_singleton_permutationContainmentCount {n : ℕ}
    (plant : SimpleGraph (Fin n)) :
    (∑ e : AmbientEdge n, permutationContainmentCount plant {e}) =
      Fintype.card (Equiv.Perm (Fin n)) * plant.edgeFinset.card := by
  classical
  calc
    (∑ e : AmbientEdge n, permutationContainmentCount plant {e}) =
        ∑ e : AmbientEdge n,
          ∑ σ : Equiv.Perm (Fin n),
            if e ∈ permutedPlantEdges plant σ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      simp [permutationContainmentCount]
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ e : AmbientEdge n,
            if e ∈ permutedPlantEdges plant σ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm (Fin n),
          (permutedPlantEdges plant σ).card := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      change (∑ e ∈ (Finset.univ : Finset (AmbientEdge n)),
        if e ∈ permutedPlantEdges plant σ then 1 else 0) = _
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ : Finset (AmbientEdge n)).filter
              (fun e ↦ e ∈ permutedPlantEdges plant σ) =
            permutedPlantEdges plant σ := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfilter, Finset.sum_const, nsmul_eq_mul, mul_one]
      norm_num
    _ = ∑ _σ : Equiv.Perm (Fin n), plant.edgeFinset.card := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact card_permutedPlantEdges plant σ
    _ = Fintype.card (Equiv.Perm (Fin n)) * plant.edgeFinset.card := by
      simp

/-- The degree-one Fourier mass is part of every positive-degree projection.
This is the concrete bridge from the likelihood's singleton coefficients to
the low-degree norm. -/
theorem singleton_fourier_mass_le_lowDegree_excess {n D : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (hD : 0 < D) :
    (∑ e : AmbientEdge n,
        ((((permutationContainmentCount plant {e} : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight) ^ 2)) ≤
      plantedLowDegreeNormSq θ plant D - 1 := by
  classical
  let weight : Finset (AmbientEdge n) → ℝ := fun S ↦
    ((((permutationContainmentCount plant S : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
      θ.forcedWeight ^ S.card) ^ 2)
  let singletons : Finset (Finset (AmbientEdge n)) :=
    (Finset.univ : Finset (AmbientEdge n)).image fun e ↦ {e}
  let supports : Finset (Finset (AmbientEdge n)) :=
    Finset.univ.filter fun S ↦ S.card ≤ D ∧ S.Nonempty
  have hsubset : singletons ⊆ supports := by
    intro S hS
    simp only [singletons, Finset.mem_image, Finset.mem_univ, true_and] at hS
    obtain ⟨e, rfl⟩ := hS
    simp [supports, Nat.succ_le_iff, hD]
  have hmono : (∑ S ∈ singletons, weight S) ≤
      ∑ S ∈ supports, weight S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun S _hS _hnot ↦ sq_nonneg _)
  rw [plantedLowDegreeNormSq_sub_one_eq_sum_nonempty]
  change (∑ e : AmbientEdge n,
      ((((permutationContainmentCount plant {e} : ℝ) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
        θ.forcedWeight) ^ 2)) ≤ ∑ S ∈ supports, weight S
  calc
    _ = ∑ S ∈ singletons, weight S := by
      dsimp [singletons]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro e _he
        simp [weight]
      · exact fun _ _ _ _ h ↦ Finset.singleton_injective h
    _ ≤ _ := hmono

/-- Cauchy--Schwarz applied to the singleton containment probabilities.  The
only ambient-size estimate used is `|E(Kₙ)| ≤ n²`, so no isomorphism-class
regrouping is needed. -/
theorem edgeCount_sq_le_ambient_sq_mul_singleton_mass {n : ℕ}
    (plant : SimpleGraph (Fin n)) :
    (plant.edgeFinset.card : ℝ) ^ 2 ≤
      (n : ℝ) ^ 2 *
        ∑ e : AmbientEdge n,
          ((permutationContainmentCount plant {e} : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) ^ 2 := by
  classical
  let q : AmbientEdge n → ℝ := fun e ↦
    (permutationContainmentCount plant {e} : ℝ) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  have hperm_pos : 0 < Fintype.card (Equiv.Perm (Fin n)) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hperm_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast hperm_pos.ne'
  have hsum_real :
      (∑ e : AmbientEdge n,
          (permutationContainmentCount plant {e} : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (plant.edgeFinset.card : ℝ) := by
    exact_mod_cast sum_singleton_permutationContainmentCount plant
  have hsum_q : (∑ e : AmbientEdge n, q e) =
      (plant.edgeFinset.card : ℝ) := by
    dsimp [q]
    rw [← Finset.sum_div, hsum_real]
    field_simp
  have hcauchy :
      (∑ e : AmbientEdge n, q e) ^ 2 ≤
        (Fintype.card (AmbientEdge n) : ℝ) *
          ∑ e : AmbientEdge n, (q e) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (AmbientEdge n))) (f := q))
  have hcard_nat : Fintype.card (AmbientEdge n) ≤ n ^ 2 := by
    calc
      Fintype.card (AmbientEdge n) = n.choose 2 := by
        rw [← SimpleGraph.edgeFinset_card,
          SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
        simp
      _ ≤ n ^ 2 := Nat.choose_le_pow n 2
  have hcard_real : (Fintype.card (AmbientEdge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hcard_nat
  calc
    (plant.edgeFinset.card : ℝ) ^ 2 =
        (∑ e : AmbientEdge n, q e) ^ 2 := by rw [hsum_q]
    _ ≤ (Fintype.card (AmbientEdge n) : ℝ) *
          ∑ e : AmbientEdge n, (q e) ^ 2 := hcauchy
    _ ≤ (n : ℝ) ^ 2 * ∑ e : AmbientEdge n, (q e) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hcard_real
        (Finset.sum_nonneg fun e _he ↦ sq_nonneg (q e))
    _ = _ := by rfl

/-- At sparse density `p=c/n`, degree-one Fourier mass controls the paper's
`K₂` leading weight up to an absolute constant.  This theorem derives that
control from the actual permutation-mixture likelihood. -/
theorem betaWeight_edge_le_four_mul_lowDegree_excess
    {c : ℝ} (hc : 0 < c) {n D : ℕ} (hn : 0 < n)
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (hp : θ.p = c / (n : ℝ)) (hp_half : θ.p ≤ 1 / 2) (hD : 0 < D) :
    betaWeight c n 1 2 plant.edgeFinset.card 2 ≤
      4 * (plantedLowDegreeNormSq θ plant D - 1) := by
  classical
  let A : ℝ :=
    ∑ e : AmbientEdge n,
      ((permutationContainmentCount plant {e} : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) ^ 2
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hA_nonneg : 0 ≤ A := by
    exact Finset.sum_nonneg fun e _he ↦ sq_nonneg _
  have hedge : (plant.edgeFinset.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * A := by
    exact edgeCount_sq_le_ambient_sq_mul_singleton_mass plant
  have hsingle := singleton_fourier_mass_le_lowDegree_excess θ plant hD
  have hsingle' : θ.forcedWeight ^ 2 * A ≤
      plantedLowDegreeNormSq θ plant D - 1 := by
    calc
      θ.forcedWeight ^ 2 * A =
          ∑ e : AmbientEdge n,
            ((((permutationContainmentCount plant {e} : ℝ) /
                (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
              θ.forcedWeight) ^ 2) := by
        dsimp [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _he
        ring
      _ ≤ _ := hsingle
  have hhalf : (1 / 2 : ℝ) ≤ 1 - θ.p := by linarith
  have hforced_lower_zero : (1 / 2 : ℝ) / θ.p ≤ θ.forcedWeight ^ 2 := by
    rw [θ.forcedWeight_sq]
    exact (div_le_div_iff_of_pos_right θ.p_pos).2 hhalf
  have hforced_lower : (n : ℝ) / (2 * c) ≤ θ.forcedWeight ^ 2 := by
    calc
      (n : ℝ) / (2 * c) = (1 / 2 : ℝ) / θ.p := by
        rw [hp]
        field_simp [hc.ne', hn_real.ne']
      _ ≤ θ.forcedWeight ^ 2 := hforced_lower_zero
  have hmass_lower : (n : ℝ) / (2 * c) * A ≤
      plantedLowDegreeNormSq θ plant D - 1 := by
    exact (mul_le_mul_of_nonneg_right hforced_lower hA_nonneg).trans hsingle'
  have hscale_nonneg : 0 ≤ (2 : ℝ) / (c * (n : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hedge hscale_nonneg
  have hbeta_formula :
      betaWeight c n 1 2 plant.edgeFinset.card 2 =
        (2 : ℝ) / (c * (n : ℝ)) * (plant.edgeFinset.card : ℝ) ^ 2 := by
    rw [betaWeight_edge_eq_normalized_sq hc hn, div_pow,
      Real.sq_sqrt hn_real.le]
    field_simp [hc.ne', hn_real.ne']
  have hbeta_to_mass :
      betaWeight c n 1 2 plant.edgeFinset.card 2 ≤
        4 * ((n : ℝ) / (2 * c) * A) := by
    rw [hbeta_formula]
    calc
      (2 : ℝ) / (c * (n : ℝ)) * (plant.edgeFinset.card : ℝ) ^ 2 ≤
          (2 : ℝ) / (c * (n : ℝ)) * ((n : ℝ) ^ 2 * A) := hscaled
      _ = 4 * ((n : ℝ) / (2 * c) * A) := by
        field_simp [hc.ne', hn_real.ne']
        ring
  exact hbeta_to_mass.trans
    (mul_le_mul_of_nonneg_left hmass_lower (by norm_num))

namespace FiniteGraphShape

/-- A finite graph with no isolated vertices has at most twice as many
vertices as edges. -/
theorem vertexCount_le_twice_edgeCount (F : FiniteGraphShape) :
    F.vertexCount ≤ 2 * F.edgeCount := by
  classical
  have hdegree : ∀ v : F.Vertex, 1 ≤ F.graph.degree v := by
    intro v
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hnmem : v ∉ F.graph.support :=
      (F.graph.degree_eq_zero_iff_notMem_support v).mp hzero
    apply hnmem
    rw [F.support_eq_univ]
    exact Set.mem_univ v
  have hsum : (∑ _v : F.Vertex, 1) ≤
      ∑ v : F.Vertex, F.graph.degree v := by
    exact Finset.sum_le_sum fun v _hv ↦ hdegree v
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  have hedgeCount : F.edgeCount = F.graph.edgeFinset.card := by
    rw [FiniteGraphShape.edgeCount_eq_ncard, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  simpa [FiniteGraphShape.vertexCount, hedgeCount] using hsum

/-- An occurring shape cannot use more vertices than the ambient graph. -/
theorem vertexCount_le_ambient_of_copyCount_pos {n : ℕ}
    (F : FiniteGraphShape) (G : SimpleGraph (Fin n))
    (hcopy : 0 < F.nonInducedCopyCount G) :
    F.vertexCount ≤ n := by
  have hcopy' : 0 < G.copyCount F.graph := by
    rwa [← F.nonInducedCopyCount_eq_copyCount]
  rcases SimpleGraph.copyCount_pos.mp hcopy' with ⟨copy⟩
  simpa [FiniteGraphShape.vertexCount] using
    (Fintype.card_le_of_embedding copy.toEmbedding)

/-- Package an actual nonempty support shape occurring in an ambient plant as
the arithmetic datum consumed by the uniform scalar Lemma 3.1. -/
noncomputable def leadingTermDatumOfOccurrence {n : ℕ}
    (F : FiniteGraphShape) (G : SimpleGraph (Fin n))
    (hedge : 0 < F.edgeCount) (hcopy : 0 < F.nonInducedCopyCount G) :
    LeadingTermDatum n where
  edgeCount := F.edgeCount
  vertexCount := F.vertexCount
  copyCount := F.nonInducedCopyCount G
  autCount := Fintype.card F.Automorphism
  edgeCount_pos := hedge
  vertexCount_le_twice_edges := F.vertexCount_le_twice_edgeCount
  vertexCount_le_ambient := F.vertexCount_le_ambient_of_copyCount_pos G hcopy
  copyCount_pos := hcopy
  autCount_pos := Fintype.card_pos_iff.mpr
    ⟨(SimpleGraph.Iso.refl : F.graph ≃g F.graph)⟩

end FiniteGraphShape

/-- **Graph-facing adapter for paper Lemma 3.1.**

The scalar uniform estimate applies uniformly to every nonempty support shape
that actually occurs in the ambient plant.  Occurrence supplies both the
positive copy count and the bound on the number of vertices; the
no-isolated-vertices invariant of `FiniteGraphShape` supplies `v(F) ≤ 2e(F)`.
-/
theorem alpha_div_graphBeta_tendsto_uniformly_on_occurringShapes
    {d : ℕ → ℕ} (c : ℝ) (hc : 0 < c)
    (hd : (fun n : ℕ ↦ (d n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)))
    (G : (n : ℕ) → SimpleGraph (Fin n)) :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ F : FiniteGraphShape,
      0 < F.edgeCount →
      0 < F.nonInducedCopyCount (G n) →
      F.edgeCount ≤ d n →
      |alphaWeight c n F.edgeCount F.vertexCount
          (F.nonInducedCopyCount (G n)) (Fintype.card F.Automorphism) /
          F.graphBetaWeight c n (G n) - 1| < δ := by
  have huniform := alpha_div_beta_tendsto_uniformly c hc hd
  intro δ hδ
  have hδ_uniform := huniform δ hδ
  filter_upwards [hδ_uniform] with n hn
  intro F hedge hcopy hFed
  let datum : LeadingTermDatum n :=
    F.leadingTermDatumOfOccurrence (G n) hedge hcopy
  have hdatum := hn datum hFed
  simpa only [datum, FiniteGraphShape.leadingTermDatumOfOccurrence,
    FiniteGraphShape.graphBetaWeight] using hdatum

namespace BoundedTreewidthPlantModel

/-- The concrete degree-one comparison furnished by the planted likelihood.
Unlike the scalar adapter in `LeadingTerm`, this theorem assumes no separate
`K₂` coefficient estimate. -/
theorem eventually_betaWeight_edge_le_four_mul_lowDegree_excess
    (M : BoundedTreewidthPlantModel) :
    ∀ᶠ n in atTop,
      betaWeight M.backgroundDensity n 1 2
          (M.plant n).edgeFinset.card 2 ≤
        4 * (M.lowDegreeNormSq n - 1) := by
  have hp_eventually :=
    eventually_sparseBernoulliParameter_p_eq M.backgroundDensity_pos
  filter_upwards
      [hp_eventually,
        eventually_ge_atTop (⌈2 * M.backgroundDensity⌉₊ + 1)]
      with n hp hn
  have hn_pos : 0 < n := by omega
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have htwoc_lt_n : 2 * M.backgroundDensity < (n : ℝ) := by
    have hceil : 2 * M.backgroundDensity ≤
        (⌈2 * M.backgroundDensity⌉₊ : ℝ) :=
      Nat.le_ceil (2 * M.backgroundDensity)
    have hceil_lt : (⌈2 * M.backgroundDensity⌉₊ : ℝ) < n := by
      exact_mod_cast (Nat.lt_of_succ_le hn)
    exact hceil.trans_lt hceil_lt
  have hp_half : (M.parameter n).p ≤ 1 / 2 := by
    rw [BoundedTreewidthPlantModel.parameter, hp]
    apply (div_le_iff₀ hn_real).2
    linarith
  simpa only [BoundedTreewidthPlantModel.lowDegreeNormSq,
    BoundedTreewidthPlantModel.parameter] using
      betaWeight_edge_le_four_mul_lowDegree_excess
        M.backgroundDensity_pos hn_pos (M.parameter n) (M.plant n)
        hp hp_half (M.degreeCutoff_pos n)

/-- **Paper Lemma 3.2 for the concrete planted model.**

If the actual projected likelihood ratio has squared norm tending to one and
the cutoff contains degree one, then the spanning plant has
`o(√n)` edges.  The degree-one premise is part of
`BoundedTreewidthPlantModel` as `degreeCutoff_pos`. -/
theorem edgeCount_isLittleO_sqrt
    (M : BoundedTreewidthPlantModel)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    (fun n : ℕ ↦ ((M.plant n).edgeFinset.card : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  have hupper := M.eventually_betaWeight_edge_le_four_mul_lowDegree_excess
  have hright : Vanishes
      (fun n ↦ 4 * (M.lowDegreeNormSq n - 1)) := by
    exact hlow.sub_one.const_mul 4
  have hnonneg : ∀ n,
      0 ≤ betaWeight M.backgroundDensity n 1 2
        (M.plant n).edgeFinset.card 2 := by
    intro n
    dsimp [betaWeight]
    exact mul_nonneg
      (div_nonneg
        (div_nonneg (pow_nonneg (Nat.cast_nonneg n) 1)
          (pow_nonneg (Nat.cast_nonneg n) 2))
        (pow_nonneg M.backgroundDensity_pos.le 1))
      (mul_nonneg (sq_nonneg ((M.plant n).edgeFinset.card : ℝ))
        (by norm_num))
  have hbeta : Vanishes
      (fun n ↦ betaWeight M.backgroundDensity n 1 2
        (M.plant n).edgeFinset.card 2) :=
    squeeze_zero' (Eventually.of_forall hnonneg) hupper hright
  exact edgeCount_isLittleO_sqrt_of_betaEdge_vanishes
    M.backgroundDensity_pos hbeta

end BoundedTreewidthPlantModel

end

end LowDegree
