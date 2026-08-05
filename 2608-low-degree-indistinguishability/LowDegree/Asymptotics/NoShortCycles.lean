import LowDegree.Asymptotics.ModelConsequences
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.CardEmbedding

/-!
# No short cycles from the concrete low-degree norm

This file proves paper Lemma 3.3 directly from the finite planted Fourier
formula.  We do not assume an abstract cycle penalty.

Fix one copy of `cycleGraph l` in the plant.  Every ambient permutation sends
it to an `l`-cycle support counted by `permutationContainmentCount`.  The number
of distinct such supports is at most the number of maps `Fin l → Fin n`,
namely `n ^ l`.  Double-counting permutation/support incidences and applying
Cauchy--Schwarz therefore gives

`1 ≤ n^l * ∑_S containmentProbability(S)^2`.

The exact planted Parseval formula then gives the explicit lower bound

`((1 - c/n) / c)^l ≤ lowDegreeNormSq(n) - 1`.

For `0 < c ≤ 1`, every actual cycle has `l ≤ n`; a logarithmic estimate
makes the left side uniformly at least `exp (-2)`.  This contradicts the
low-degree norm tending to one, simultaneously for every
`3 ≤ l ≤ degreeCutoff n`.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq Fintype.ofFinite

namespace NoShortCycles

variable {W : Type*} [Fintype W]

/-- Edge support in the ambient complete graph of a labelled graph copy. -/
noncomputable def ambientCopyEdges {n : ℕ} {H : SimpleGraph W}
    (f : SimpleGraph.Copy H (⊤ : SimpleGraph (Fin n))) : Finset (AmbientEdge n) := by
  classical
  exact Finset.univ.map f.mapEdgeSet

@[simp]
theorem card_ambientCopyEdges {n : ℕ} {H : SimpleGraph W}
    (f : SimpleGraph.Copy H (⊤ : SimpleGraph (Fin n))) :
    (ambientCopyEdges f).card = Nat.card H.edgeSet := by
  classical
  rw [ambientCopyEdges, Finset.card_map, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- A cycle of length at least three has exactly that many edges. -/
theorem cycleGraph_card_edgeSet {l : ℕ} (hl : 3 ≤ l) :
    Nat.card (SimpleGraph.cycleGraph l).edgeSet = l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 3 := by
    exact ⟨l - 3, by omega⟩
  have hsum :=
    (SimpleGraph.cycleGraph (k + 3)).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : Fin (k + 3),
      (SimpleGraph.cycleGraph (k + 3)).degree v = 2 :=
    fun _ ↦ SimpleGraph.cycleGraph_degree_three_le
  rw [show (∑ v : Fin (k + 3),
      (SimpleGraph.cycleGraph (k + 3)).degree v) = 2 * (k + 3) by
        simp [hdeg]
        omega] at hsum
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

@[simp]
theorem card_ambientCycleCopyEdges {n l : ℕ} (hl : 3 ≤ l)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph l)
      (⊤ : SimpleGraph (Fin n))) :
    (ambientCopyEdges f).card = l := by
  simpa only [card_ambientCopyEdges] using cycleGraph_card_edgeSet hl

/-- All edge supports of labelled ambient copies of `cycleGraph l`. -/
noncomputable def cycleSupports (n l : ℕ) :
    Finset (Finset (AmbientEdge n)) :=
  Finset.univ.image fun f :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l)
      (⊤ : SimpleGraph (Fin n)) ↦ ambientCopyEdges f

/-- There are at most `n^l` ambient supports of `l`-cycles.  The deliberately
coarse bound suffices and avoids needing the cycle automorphism count. -/
theorem cycleSupports_card_le_pow (n l : ℕ) :
    (cycleSupports n l).card ≤ n ^ l := by
  calc
    (cycleSupports n l).card ≤
        Fintype.card (SimpleGraph.Copy (SimpleGraph.cycleGraph l)
          (⊤ : SimpleGraph (Fin n))) := by
      rw [cycleSupports]
      exact Finset.card_image_le
    _ ≤ Fintype.card (Fin l → Fin n) := by
      apply Fintype.card_le_of_injective (fun f x ↦ f x)
      intro f g h
      apply SimpleGraph.Copy.ext
      intro x
      exact congrFun h x
    _ = n ^ l := by simp

/-- Move a fixed cycle copy together with the plant and then include it in the
ambient complete graph. -/
noncomputable def permutedCycleCopy {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant)
    (σ : Equiv.Perm (Fin n)) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l)
      (⊤ : SimpleGraph (Fin n)) :=
  (SimpleGraph.Copy.ofLE (permutedPlant plant σ) ⊤ le_top).comp
    ((SimpleGraph.Embedding.map σ.toEmbedding plant).toCopy.comp g)

/-- A copy factored through `G` uses only edges of `G`. -/
theorem ambientCopyEdges_ofLE_subset {n : ℕ} {H : SimpleGraph W}
    {G : SimpleGraph (Fin n)} (f : SimpleGraph.Copy H G) :
    ambientCopyEdges ((SimpleGraph.Copy.ofLE G ⊤ le_top).comp f) ⊆
      Finset.univ.filter fun e : AmbientEdge n ↦
        (e : Sym2 (Fin n)) ∈ G.edgeSet := by
  classical
  intro e he
  rw [ambientCopyEdges, Finset.mem_map] at he
  rcases he with ⟨a, _ha, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (f.mapEdgeSet a).property

/-- The moved fixed cycle is contained in the moved plant edge set. -/
theorem permutedCycleCopy_subset {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant)
    (σ : Equiv.Perm (Fin n)) :
    ambientCopyEdges (permutedCycleCopy g σ) ⊆
      permutedPlantEdges plant σ := by
  rw [show permutedCycleCopy g σ =
      (SimpleGraph.Copy.ofLE (permutedPlant plant σ) ⊤ le_top).comp
        ((SimpleGraph.Embedding.map σ.toEmbedding plant).toCopy.comp g) by
      rfl]
  simpa only [permutedPlantEdges] using
    ambientCopyEdges_ofLE_subset
      ((SimpleGraph.Embedding.map σ.toEmbedding plant).toCopy.comp g)

theorem permutedCycleSupport_mem {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant)
    (σ : Equiv.Perm (Fin n)) :
    ambientCopyEdges (permutedCycleCopy g σ) ∈ cycleSupports n l := by
  simp only [cycleSupports, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨permutedCycleCopy g σ, rfl⟩

/-- Double-count the incidence relation between ambient cycle supports and
permutations whose moved plant contains the support.  Each permutation
contributes at least its image of the fixed cycle copy. -/
theorem card_perm_le_sum_cycleContainment {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant) :
    Fintype.card (Equiv.Perm (Fin n)) ≤
      ∑ S ∈ cycleSupports n l, permutationContainmentCount plant S := by
  classical
  calc
    Fintype.card (Equiv.Perm (Fin n)) =
        ∑ _σ : Equiv.Perm (Fin n), 1 := by simp
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
          ∑ S ∈ cycleSupports n l,
            if S ⊆ permutedPlantEdges plant σ then 1 else 0 := by
      apply Finset.sum_le_sum
      intro σ _
      let S := ambientCopyEdges (permutedCycleCopy g σ)
      have hS : S ∈ cycleSupports n l := permutedCycleSupport_mem g σ
      have hsub : S ⊆ permutedPlantEdges plant σ :=
        permutedCycleCopy_subset g σ
      calc
        1 = (if S ⊆ permutedPlantEdges plant σ then 1 else 0) := by
          simp [hsub]
        _ ≤ ∑ T ∈ cycleSupports n l,
            if T ⊆ permutedPlantEdges plant σ then 1 else 0 := by
          exact Finset.single_le_sum
            (f := fun T ↦
              if T ⊆ permutedPlantEdges plant σ then 1 else 0)
            (fun _ _ ↦ Nat.zero_le _) hS
    _ = ∑ S ∈ cycleSupports n l,
          ∑ σ : Equiv.Perm (Fin n),
            if S ⊆ permutedPlantEdges plant σ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ cycleSupports n l,
        permutationContainmentCount plant S := by
      apply Finset.sum_congr rfl
      intro S _
      simp [permutationContainmentCount]

/-- Probability that a uniformly moved plant contains a fixed support.  This
is exactly the first factor in `fourierCoeff_plantedLikelihood`. -/
noncomputable def containmentProbability {n : ℕ}
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) : ℝ :=
  (permutationContainmentCount plant S : ℝ) /
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

/-- Cauchy--Schwarz consequence of the incidence count: the squared
containment probabilities of the ambient cycle supports have total at least
`n^{-l}`.  The division-free form remains meaningful for every `n`. -/
theorem one_le_pow_mul_sum_cycle_containment_sq {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant) :
    (1 : ℝ) ≤ (n : ℝ) ^ l *
      ∑ S ∈ cycleSupports n l, (containmentProbability plant S) ^ 2 := by
  classical
  let A : ℝ :=
    ∑ S ∈ cycleSupports n l, (containmentProbability plant S) ^ 2
  let T : ℝ :=
    ∑ S ∈ cycleSupports n l, containmentProbability plant S
  have hperm_pos : 0 < Fintype.card (Equiv.Perm (Fin n)) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hperm_real_pos :
      (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast hperm_pos
  have hsum_nat := card_perm_le_sum_cycleContainment g
  have hsum_real : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤
      ∑ S ∈ cycleSupports n l,
        (permutationContainmentCount plant S : ℝ) := by
    exact_mod_cast hsum_nat
  have hT : 1 ≤ T := by
    dsimp [T, containmentProbability]
    rw [← Finset.sum_div]
    exact (le_div_iff₀ hperm_real_pos).2 (by simpa using hsum_real)
  have hT_sq : 1 ≤ T ^ 2 := by nlinarith
  have hcauchy : T ^ 2 ≤ ((cycleSupports n l).card : ℝ) * A := by
    dsimp [T, A]
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := cycleSupports n l) (f := containmentProbability plant))
  have hcard_nat := cycleSupports_card_le_pow n l
  have hcard_real : ((cycleSupports n l).card : ℝ) ≤ (n : ℝ) ^ l := by
    exact_mod_cast hcard_nat
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc
    (1 : ℝ) ≤ T ^ 2 := hT_sq
    _ ≤ ((cycleSupports n l).card : ℝ) * A := hcauchy
    _ ≤ (n : ℝ) ^ l * A :=
      mul_le_mul_of_nonneg_right hcard_real hA_nonneg
    _ = _ := rfl

/-- The exact planted Parseval formula contains the complete cycle-support
family whenever `l ≤ D`. -/
theorem cycle_family_mass_le_lowDegree_excess {n l D : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (hl : 3 ≤ l) (hlD : l ≤ D) :
    (θ.forcedWeight ^ l) ^ 2 *
        (∑ S ∈ cycleSupports n l,
          (containmentProbability plant S) ^ 2) ≤
      plantedLowDegreeNormSq θ plant D - 1 := by
  classical
  let weight : Finset (AmbientEdge n) → ℝ := fun S ↦
    ((containmentProbability plant S * θ.forcedWeight ^ S.card) ^ 2)
  let supports : Finset (Finset (AmbientEdge n)) :=
    Finset.univ.filter fun S ↦ S.card ≤ D ∧ S.Nonempty
  have hsubset : cycleSupports n l ⊆ supports := by
    intro S hS
    simp only [cycleSupports, Finset.mem_image, Finset.mem_univ, true_and] at hS
    obtain ⟨f, rfl⟩ := hS
    have hcard := card_ambientCycleCopyEdges hl f
    simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(by simpa [hcard] using hlD), Finset.card_pos.mp (by omega)⟩
  rw [plantedLowDegreeNormSq_sub_one_eq_sum_nonempty]
  change _ ≤ ∑ S ∈ supports, weight S
  calc
    (θ.forcedWeight ^ l) ^ 2 *
        (∑ S ∈ cycleSupports n l,
          (containmentProbability plant S) ^ 2) =
        ∑ S ∈ cycleSupports n l, weight S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      have hcard : S.card = l := by
        simp only [cycleSupports, Finset.mem_image, Finset.mem_univ,
          true_and] at hS
        obtain ⟨f, rfl⟩ := hS
        exact card_ambientCycleCopyEdges hl f
      simp only [weight, hcard]
      ring
    _ ≤ ∑ S ∈ supports, weight S :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)

/-- Concrete Fourier penalty caused by one cycle copy.  This is a slightly
weaker but fully sufficient version of the paper's `2l`-enhanced bound; no
automorphism-count formula is needed. -/
theorem cycle_penalty_le_lowDegree_excess
    {c : ℝ} (hc : 0 < c) {n l D : ℕ} (hn : 0 < n)
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (hp : θ.p = c / (n : ℝ)) (hl : 3 ≤ l) (hlD : l ≤ D)
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant) :
    ((1 - c / (n : ℝ)) / c) ^ l ≤
      plantedLowDegreeNormSq θ plant D - 1 := by
  classical
  let A : ℝ :=
    ∑ S ∈ cycleSupports n l, (containmentProbability plant S) ^ 2
  let K : ℝ := (θ.forcedWeight ^ l) ^ 2
  have hcycle := one_le_pow_mul_sum_cycle_containment_sq g
  change (1 : ℝ) ≤ (n : ℝ) ^ l * A at hcycle
  have hmass := cycle_family_mass_le_lowDegree_excess θ plant hl hlD
  change K * A ≤ plantedLowDegreeNormSq θ plant D - 1 at hmass
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hnpow : (0 : ℝ) < (n : ℝ) ^ l := pow_pos hn_real _
  have hK_nonneg : 0 ≤ K := sq_nonneg _
  have hscaled :=
    mul_le_mul_of_nonneg_left hcycle (div_nonneg hK_nonneg hnpow.le)
  have hKA : K / (n : ℝ) ^ l ≤ K * A := by
    calc
      K / (n : ℝ) ^ l = (K / (n : ℝ) ^ l) * 1 := by ring
      _ ≤ (K / (n : ℝ) ^ l) * ((n : ℝ) ^ l * A) := hscaled
      _ = K * A := by field_simp [hnpow.ne']
  have hpenalty :
      K / (n : ℝ) ^ l = ((1 - c / (n : ℝ)) / c) ^ l := by
    dsimp [K]
    rw [show (θ.forcedWeight ^ l) ^ 2 = (θ.forcedWeight ^ 2) ^ l by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega]
    rw [θ.forcedWeight_sq, hp, ← div_pow]
    congr 1
    field_simp [hc.ne', hn_real.ne']
  rw [← hpenalty]
  exact hKA.trans hmass

/-- Uniform lower bound on the explicit cycle penalty.  The guard `l ≤ n`
is automatic for a cycle copy in a graph on `Fin n`; retaining the exact base
handles the boundary case `c = 1`. -/
theorem exp_neg_two_le_cycle_penalty
    {c : ℝ} (hc : 0 < c) (hc_one : c ≤ 1)
    {n l : ℕ} (hn : 0 < n) (hc_half : c / (n : ℝ) ≤ 1 / 2)
    (hln : l ≤ n) :
    Real.exp (-2) ≤ ((1 - c / (n : ℝ)) / c) ^ l := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hx_nonneg : 0 ≤ c / (n : ℝ) := div_nonneg hc.le hn_real.le
  have hbase_pos : 0 < 1 - c / (n : ℝ) := by linarith
  have hlog_abs := abs_log_one_sub_le_two_mul hx_nonneg hc_half
  have hlog_lower : -(2 * (c / (n : ℝ))) ≤
      Real.log (1 - c / (n : ℝ)) := neg_le_of_abs_le hlog_abs
  have hl_real : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
  have hxl : c / (n : ℝ) * (l : ℝ) ≤ c := by
    calc
      c / (n : ℝ) * (l : ℝ) ≤ c / (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hl_real hx_nonneg
      _ = c := div_mul_cancel₀ c hn_real.ne'
  have hlog_power : (-2 : ℝ) ≤
      (l : ℝ) * Real.log (1 - c / (n : ℝ)) := by
    calc
      (-2 : ℝ) ≤ -2 * c := by nlinarith
      _ ≤ -2 * (c / (n : ℝ) * (l : ℝ)) := by nlinarith
      _ = (l : ℝ) * (-(2 * (c / (n : ℝ)))) := by ring
      _ ≤ (l : ℝ) * Real.log (1 - c / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hexp : Real.exp (-2) ≤
      Real.exp ((l : ℝ) * Real.log (1 - c / (n : ℝ))) :=
    Real.exp_le_exp.mpr hlog_power
  have hbase_le :
      1 - c / (n : ℝ) ≤ (1 - c / (n : ℝ)) / c := by
    exact (le_div_iff₀ hc).2
      (mul_le_of_le_one_right hbase_pos.le hc_one)
  calc
    Real.exp (-2) ≤
        Real.exp ((l : ℝ) * Real.log (1 - c / (n : ℝ))) := hexp
    _ = (1 - c / (n : ℝ)) ^ l := by
      rw [Real.exp_nat_mul, Real.exp_log hbase_pos]
    _ ≤ ((1 - c / (n : ℝ)) / c) ^ l :=
      pow_le_pow_left₀ hbase_pos.le hbase_le l

/-- A cycle copy injects its `l` vertices into the `n` ambient vertices. -/
theorem cycle_length_le_ambient {n l : ℕ}
    {plant : SimpleGraph (Fin n)}
    (g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) plant) : l ≤ n := by
  simpa using Fintype.card_le_of_embedding g.toEmbedding

end NoShortCycles

namespace BoundedTreewidthPlantModel

open NoShortCycles

/-- Every short cycle would force a fixed positive excess in the concrete
model's actual low-degree norm. -/
theorem eventually_cycle_penalty
    (M : BoundedTreewidthPlantModel) (hc_one : M.backgroundDensity ≤ 1) :
    ∀ᶠ n in atTop, ∀ l : ℕ,
      3 ≤ l → l ≤ M.degreeCutoff n →
        SimpleGraph.cycleGraph l ⊑ M.plant n →
          Real.exp (-2) ≤ M.lowDegreeNormSq n - 1 := by
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
  have hc_half : M.backgroundDensity / (n : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hn_real).2
    linarith
  intro l hl hlD hcontained
  let g : SimpleGraph.Copy (SimpleGraph.cycleGraph l) (M.plant n) :=
    hcontained.some
  have hln : l ≤ n := cycle_length_le_ambient g
  have hpenalty := cycle_penalty_le_lowDegree_excess
    M.backgroundDensity_pos hn_pos (M.parameter n) (M.plant n)
    hp hl hlD g
  have hlower := exp_neg_two_le_cycle_penalty
    M.backgroundDensity_pos hc_one hn_pos hc_half hln
  exact hlower.trans (by
    simpa only [BoundedTreewidthPlantModel.lowDegreeNormSq,
      BoundedTreewidthPlantModel.parameter] using hpenalty)

/-- **Paper Lemma 3.3 for the concrete planted model.**

For `0 < c ≤ 1`, if the actual squared low-degree norm tends to one, then
eventually the plant contains no cycle of any integer length
`3 ≤ l ≤ degreeCutoff n`.  The paper's additional growth condition on the
cutoff is not consumed by this lemma. -/
theorem no_shortCycles_of_lowDegree
    (M : BoundedTreewidthPlantModel) (hc_one : M.backgroundDensity ≤ 1)
    (hlow : TendsToOne M.lowDegreeNormSq) :
    ∀ᶠ n in atTop, ∀ l : ℕ,
      3 ≤ l → l ≤ M.degreeCutoff n →
        ¬(SimpleGraph.cycleGraph l ⊑ M.plant n) := by
  have hvanish :
      Tendsto (fun n ↦ M.lowDegreeNormSq n - 1) atTop (nhds 0) :=
    hlow.sub_one
  have hsmall : ∀ᶠ n in atTop,
      M.lowDegreeNormSq n - 1 < Real.exp (-2) :=
    (tendsto_order.1 hvanish).2 _ (Real.exp_pos _)
  filter_upwards [M.eventually_cycle_penalty hc_one, hsmall]
    with n hpenalty hsmall_n
  intro l hl hlD hcycle
  exact (not_le_of_gt hsmall_n) (hpenalty l hl hlD hcycle)

end BoundedTreewidthPlantModel

end

end LowDegree
