import LowDegree.ForestTruncation
import LowDegree.SupercriticalTruncation

/-!
# Statistical distinguishability in the supercritical appendix

This file formalizes the scan-test half of paper Theorem A.1.  In particular,
it upgrades the count-valued twice truncation from
`SupercriticalTruncation.lean` to an actual random finite edge set, applies an
independent retained-edge mask, embeds the result in the ambient graph, and
records the exact two union bounds used by the scan test.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## The appendix scales -/

/-- Paper Appendix A's plant size `m_n = floor(n^r)`. -/
noncomputable def appendixPlantSize (r : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ r⌋₊

/-- Paper Appendix A's low-degree cutoff `D_n = ceil((log n)^2)`. -/
noncomputable def appendixDegreeCutoff (n : ℕ) : ℕ :=
  ⌈(Real.log (n : ℝ)) ^ 2⌉₊

/-- Paper Appendix A's cycle cutoff `g_n = max(3,floor(log log n))`. -/
noncomputable def appendixCycleCutoff (n : ℕ) : ℕ :=
  max 3 ⌊Real.log (Real.log (n : ℝ))⌋₊

/-- The paper's scan threshold `K_n = ceil(τ m_n)`. -/
noncomputable def appendixScanThreshold (τ r : ℝ) (n : ℕ) : ℕ :=
  ⌈τ * appendixPlantSize r n⌉₊

theorem appendixPlantSize_tendsto_atTop {r : ℝ} (hr : 0 < r) :
    Tendsto (appendixPlantSize r) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)

theorem appendixPlantSize_le_index {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (n : ℕ) : appendixPlantSize r n ≤ n := by
  cases n with
  | zero => simp [appendixPlantSize, Real.zero_rpow hr0.ne']
  | succ n =>
      have hnOne : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast n.zero_lt_succ
      have hfloor : (appendixPlantSize r (n + 1) : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) ^ r := by
        exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hrpow : ((n + 1 : ℕ) : ℝ) ^ r ≤ (n + 1 : ℕ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hnOne hr1
      exact_mod_cast hfloor.trans hrpow

/-- Since `r<1`, the appendix plant occupies a vanishing fraction of the
ambient vertices. -/
theorem appendixPlantSize_div_index_vanishes {r : ℝ} (hr : r < 1) :
    Vanishes fun n ↦ (appendixPlantSize r n : ℝ) / (n : ℝ) := by
  have htarget : Vanishes fun n ↦ ((n : ℝ) ^ (-(1 - r))) := by
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp
      tendsto_natCast_atTop_atTop
  have hnonneg : ∀ n,
      0 ≤ (appendixPlantSize r n : ℝ) / (n : ℝ) := fun _ ↦ by
    positivity
  have hupper : ∀ᶠ n in atTop,
      (appendixPlantSize r n : ℝ) / (n : ℝ) ≤
        (n : ℝ) ^ (-(1 - r)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hfloor : (appendixPlantSize r n : ℝ) ≤ (n : ℝ) ^ r := by
      exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc
      (appendixPlantSize r n : ℝ) / (n : ℝ) ≤
          (n : ℝ) ^ r / (n : ℝ) := by gcongr
      _ = (n : ℝ) ^ (r - 1) := by
        rw [Real.rpow_sub hnreal, Real.rpow_one]
      _ = (n : ℝ) ^ (-(1 - r)) := by ring_nf
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper htarget

/-! ## The edge-set-valued twice truncation -/

/-- Present coordinates of a Boolean graph configuration. -/
noncomputable def presentAmbientEdges {m : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) : Finset (AmbientEdge m) :=
  Finset.univ.filter fun e ↦ x e = true

@[simp]
theorem mem_presentAmbientEdges {m : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) (e : AmbientEdge m) :
    e ∈ presentAmbientEdges x ↔ x e = true := by
  simp [presentAmbientEdges]

theorem card_presentAmbientEdges {m : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) :
    ((presentAmbientEdges x).card : ℝ) = bernoulliCountReal x := by
  unfold presentAmbientEdges bernoulliCountReal
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro e _
  cases x e <;> simp [BernoulliParameter.bitValue]

theorem shortCycleRemovedEdges_subset_present (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) :
    shortCycleRemovedEdges m g x ⊆ presentAmbientEdges x := by
  intro e he
  rw [shortCycleRemovedEdges, Finset.mem_biUnion] at he
  rcases he with ⟨k, _hk, he⟩
  rw [Finset.mem_biUnion] at he
  rcases he with ⟨f, _hf, he⟩
  unfold presentCycleEdges at he
  split at he
  next hpresent =>
    have hall := (mem_allPresentEvent (cycleEmbeddingEdges f) x).mp hpresent
    exact mem_presentAmbientEdges x e |>.2 (hall e he)
  next => simp at he

/-- Edge set after deleting every edge on a cycle of length at most `g`. -/
noncomputable def shortCyclePrunedEdges (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) : Finset (AmbientEdge m) :=
  presentAmbientEdges x \ shortCycleRemovedEdges m g x

theorem card_shortCyclePrunedEdges (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) :
    ((shortCyclePrunedEdges m g x).card : ℝ) =
      bernoulliCountReal x - shortCycleRemovedCountReal m g x := by
  have hsub := shortCycleRemovedEdges_subset_present m g x
  unfold shortCyclePrunedEdges shortCycleRemovedCountReal
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    Nat.cast_sub (Finset.card_le_card hsub), card_presentAmbientEdges]

/-- The actual twice-truncated edge set from Appendix A: first prune short
cycles, then replace the result by the empty graph off the local-sparsity
event. -/
noncomputable def twiceTruncatedPlantEdgesAt
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) :
    Finset (AmbientEdge (m n)) :=
  if x ∈ localSparsityEvent n (m n)
      (localSparsityPowerCutoff (m n) gamma)
      (localSparsitySlackConstant lam r gamma) then
    shortCyclePrunedEdges (m n) (g n) x
  else ∅

theorem twiceTruncatedPlantEdgesAt_card_div
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) :
    ((twiceTruncatedPlantEdgesAt lam r gamma m g n x).card : ℝ) /
        (m n : ℝ) =
      locallyTruncatedPrunedEdgeDensityAt lam r gamma m g n x := by
  unfold twiceTruncatedPlantEdgesAt locallyTruncatedPrunedEdgeDensityAt
  split
  · rw [card_shortCyclePrunedEdges]
    rfl
  · simp

/-- The twice-truncated random plant as an honest finite law on edge sets. -/
noncomputable def twiceTruncatedPlantLawAt
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ) :
    FiniteLaw (Finset (AmbientEdge (m n))) :=
  (erdosRenyiLaw (n := m n) (sparseBernoulliParameter lam (m n))).map
    (twiceTruncatedPlantEdgesAt lam r gamma m g n)

theorem twiceTruncatedPlantLawAt_edgeDensity_tendstoInProbability
    (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m g : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ))
    (hgrowth : Vanishes fun n ↦
      (((g n + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ (g n)) /
        (m n : ℝ)) :
    TendstoInProbability
      (twiceTruncatedPlantLawAt lam r gamma m g)
      (fun n A ↦ (A.card : ℝ) / (m n : ℝ))
      (lam / 2) := by
  have h := locallyTruncatedPruned_edgeDensity_tendstoInProbability
    lam r gamma hlam hr hgamma m g hm hpowerScale hgrowth
  intro δ hδ
  simpa only [twiceTruncatedPlantLawAt, FiniteLaw.prob_map,
    FiniteLaw.mem_event, twiceTruncatedPlantEdgesAt_card_div] using h δ hδ

/-! ## Independent retention of a random finite plant -/

namespace FiniteLaw

/-- Product of two finite probability laws. -/
noncomputable def product {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  mass z := p.mass z.1 * q.mass z.2
  mass_nonneg z := mul_nonneg (p.mass_nonneg z.1) (q.mass_nonneg z.2)
  sum_mass := by
    calc
      (∑ z : A × B, p.mass z.1 * q.mass z.2) =
          (∑ a : A, p.mass a) * ∑ b : B, q.mass b := by
            simp only [Fintype.sum_prod_type]
            calc
              (∑ a : A, ∑ b : B, p.mass a * q.mass b) =
                  ∑ a : A, p.mass a * ∑ b : B, q.mass b := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.mul_sum]
              _ = _ := by rw [Finset.sum_mul]
      _ = 1 := by rw [p.sum_mass, q.sum_mass, one_mul]

@[simp]
theorem product_mass {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : FiniteLaw B) (z : A × B) :
    (p.product q).mass z = p.mass z.1 * q.mass z.2 := rfl

theorem product_prob_fst {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : FiniteLaw B) (s : Finset A) :
    (p.product q).prob (FiniteLaw.event fun z : A × B ↦ z.1 ∈ s) =
      p.prob s := by
  classical
  have hevent : FiniteLaw.event (fun z : A × B ↦ z.1 ∈ s) =
      s.product (Finset.univ : Finset B) := by
    ext z
    simp
  rw [hevent]
  unfold FiniteLaw.prob
  change (∑ z ∈ s ×ˢ (Finset.univ : Finset B),
      p.mass z.1 * q.mass z.2) = ∑ a ∈ s, p.mass a
  rw [Finset.sum_product]
  calc
    (∑ a ∈ s, ∑ b : B, p.mass a * q.mass b) =
        ∑ a ∈ s, p.mass a * (∑ b : B, q.mass b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ a ∈ s, p.mass a := by rw [q.sum_mass]; simp

theorem prob_le_one {A : Type*} [Fintype A]
    (p : FiniteLaw A) (s : Finset A) : p.prob s ≤ 1 := by
  calc
    p.prob s ≤ p.prob Finset.univ :=
      p.prob_mono (Finset.subset_univ s)
    _ = 1 := by simp [FiniteLaw.prob, p.sum_mass]

/-- Fiber decomposition for an event in a product finite law. -/
theorem product_prob_fibers {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : FiniteLaw B) (s : Finset A)
    (event : A → Finset B) :
    (p.product q).prob
        (FiniteLaw.event fun z : A × B ↦ z.1 ∈ s ∧ z.2 ∈ event z.1) =
      ∑ a ∈ s, p.mass a * q.prob (event a) := by
  classical
  unfold FiniteLaw.prob FiniteLaw.event
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  calc
    _ = ∑ a ∈ (Finset.univ.filter fun a : A ↦ a ∈ s),
          ∑ b ∈ (Finset.univ.filter fun b : B ↦ b ∈ event a),
            p.mass a * q.mass b := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ s
      · simp only [ha, true_and, if_true, product_mass]
        rw [Finset.sum_filter]
      · simp [ha]
    _ = ∑ a ∈ s, ∑ b ∈ event a, p.mass a * q.mass b := by
      simp
    _ = ∑ a ∈ s, p.mass a * ∑ b ∈ event a, q.mass b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

/-- Positive mass under a pushforward has a positive-mass preimage. -/
theorem exists_preimage_of_map_mass_pos
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) {y : B}
    (hy : 0 < (p.map f).mass y) :
    ∃ x : A, f x = y ∧ 0 < p.mass x := by
  rw [FiniteLaw.map_mass] at hy
  by_contra hnone
  push_neg at hnone
  have hzero : ∀ x : A, (if f x = y then p.mass x else 0) = 0 := by
    intro x
    by_cases hxy : f x = y
    · rw [if_pos hxy]
      exact le_antisymm (hnone x hxy) (p.mass_nonneg x)
    · rw [if_neg hxy]
  rw [show (∑ x : A, if f x = y then p.mass x else 0) = 0 by
    exact Finset.sum_eq_zero fun x _ ↦ hzero x] at hy
  exact lt_irrefl 0 hy

end FiniteLaw

namespace TendstoInProbability

/-- Multiplication by a fixed scalar preserves convergence in probability. -/
theorem const_mul
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {law : ∀ n, FiniteLaw (Ω n)}
    {X : ∀ n, Ω n → ℝ} {a c : ℝ}
    (hX : TendstoInProbability law X a) :
    TendstoInProbability law (fun n ω ↦ c * X n ω) (c * a) := by
  by_cases hc : c = 0
  · subst c
    simpa using TendstoInProbability.const law 0
  · intro δ hδ
    have habs : 0 < |c| := abs_pos.mpr hc
    have hevent : ∀ n,
        FiniteLaw.event (fun ω ↦ δ ≤ |c * X n ω - c * a|) =
          FiniteLaw.event (fun ω ↦ δ / |c| ≤ |X n ω - a|) := by
      intro n
      ext ω
      simp only [FiniteLaw.mem_event]
      rw [← mul_sub, abs_mul]
      rw [mul_comm]
      exact (div_le_iff₀ habs).symm
    simpa only [hevent] using hX (δ / |c|) (div_pos hδ habs)

/-- Adjoining an independent finite coordinate does not change convergence
of a statistic depending only on the first coordinate. -/
theorem product_fst
    {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]
    {p : ∀ n, FiniteLaw (A n)} (q : ∀ n, FiniteLaw (B n))
    {X : ∀ n, A n → ℝ} {a : ℝ}
    (hX : TendstoInProbability p X a) :
    TendstoInProbability (fun n ↦ (p n).product (q n))
      (fun n z ↦ X n z.1) a := by
  intro δ hδ
  have hv := hX δ hδ
  convert hv using 1
  funext n
  simpa [FiniteLaw.event] using
    (FiniteLaw.product_prob_fst (p n) (q n)
      (FiniteLaw.event fun x ↦ δ ≤ |X n x - a|))

/-- Convergence in probability pushes forward through a deterministic map. -/
theorem map_law
    {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]
    {p : ∀ n, FiniteLaw (A n)}
    {X : ∀ n, A n → ℝ} {a : ℝ}
    (hX : TendstoInProbability p X a)
    (f : ∀ n, A n → B n) (Y : ∀ n, B n → ℝ)
    (hcompat : ∀ n x, Y n (f n x) = X n x) :
    TendstoInProbability (fun n ↦ (p n).map (f n)) Y a := by
  intro δ hδ
  have hv := hX δ hδ
  convert hv using 1
  funext n
  rw [FiniteLaw.prob_map]
  congr 1
  ext x
  simp [hcompat]

end TendstoInProbability

/-- Apply an independent Bernoulli mask to a finite edge set. -/
noncomputable def retainEdgeSet {E : Type*} [Fintype E]
    (A : Finset E) (z : BooleanConfiguration E) : Finset E :=
  A.filter fun e ↦ z e = true

@[simp]
theorem mem_retainEdgeSet {E : Type*} [Fintype E]
    (A : Finset E) (z : BooleanConfiguration E) (e : E) :
    e ∈ retainEdgeSet A z ↔ e ∈ A ∧ z e = true := by
  simp [retainEdgeSet]

/-- Retain every edge of a random plant independently with probability
`ρ`.  This pushforward construction is equivalent to mixing the deletion
weights from `DeletedPlant.lean`, but is better suited to concentration. -/
noncomputable def retainedRandomPlantLaw {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (p : FiniteLaw (Finset E)) :
    FiniteLaw (Finset E) :=
  (p.product (bernoulliProductLaw ρ)).map fun z ↦ retainEdgeSet z.1 z.2

theorem retainedRandomPlantLaw_eq {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (p : FiniteLaw (Finset E)) :
    retainedRandomPlantLaw ρ p =
      (p.product (bernoulliProductLaw ρ)).map
        (fun z ↦ retainEdgeSet z.1 z.2) := rfl

theorem retainedRandomPlantLaw_prob {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (p : FiniteLaw (Finset E))
    (s : Finset (Finset E)) :
    (retainedRandomPlantLaw ρ p).prob s =
      (p.product (bernoulliProductLaw ρ)).prob
        {z | retainEdgeSet z.1 z.2 ∈ s} := by
  rw [retainedRandomPlantLaw, FiniteLaw.prob_map]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Retention multiplies every finite-set containment probability by the
corresponding Bernoulli factor. -/
theorem randomPlantContainmentProbability_retainedRandomPlantLaw
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (p : FiniteLaw (Finset E)) (S : Finset E) :
    randomPlantContainmentProbability (retainedRandomPlantLaw ρ p) S =
      ρ.p ^ S.card * randomPlantContainmentProbability p S := by
  let contains : Finset (Finset E) :=
    Finset.univ.filter fun A : Finset E ↦ S ⊆ A
  unfold randomPlantContainmentProbability
  rw [retainedRandomPlantLaw_prob]
  have hevent :
      ({z : Finset E × BooleanConfiguration E |
          retainEdgeSet z.1 z.2 ∈ contains} :
        Finset (Finset E × BooleanConfiguration E)) =
      FiniteLaw.event fun z ↦
        z.1 ∈ contains ∧ z.2 ∈ allPresentEvent S := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      FiniteLaw.mem_event, contains, mem_allPresentEvent]
    constructor
    · intro h
      exact ⟨fun e he ↦ (mem_retainEdgeSet z.1 z.2 e).mp (h he) |>.1,
        fun e he ↦ (mem_retainEdgeSet z.1 z.2 e).mp (h he) |>.2⟩
    · rintro ⟨hA, hz⟩ e he
      exact (mem_retainEdgeSet z.1 z.2 e).mpr ⟨hA he, hz e he⟩
  change (p.product (bernoulliProductLaw ρ)).prob
      {z | retainEdgeSet z.1 z.2 ∈ contains} =
    ρ.p ^ S.card * p.prob contains
  rw [hevent]
  calc
    (p.product (bernoulliProductLaw ρ)).prob
        (FiniteLaw.event fun z ↦
          z.1 ∈ contains ∧ z.2 ∈ allPresentEvent S) =
        ∑ A ∈ contains, p.mass A *
          (bernoulliProductLaw ρ).prob (allPresentEvent S) := by
      simpa only [] using FiniteLaw.product_prob_fibers p
        (bernoulliProductLaw ρ) contains (fun _ ↦ allPresentEvent S)
    _ = ρ.p ^ S.card * p.prob contains := by
      simp_rw [bernoulliProductLaw_prob_allPresent]
      unfold FiniteLaw.prob
      rw [← Finset.sum_mul]
      ring

/-- Every positive-mass retained set is a subset of some positive-mass
original set. -/
theorem retainedRandomPlantLaw_mass_pos_subset
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (p : FiniteLaw (Finset E))
    {R : Finset E} (hR : 0 < (retainedRandomPlantLaw ρ p).mass R) :
    ∃ A : Finset E, 0 < p.mass A ∧ R ⊆ A := by
  unfold retainedRandomPlantLaw at hR
  rcases FiniteLaw.exists_preimage_of_map_mass_pos _ _ hR with
    ⟨z, heq, hz⟩
  have hp : 0 < p.mass z.1 := by
    rw [FiniteLaw.product_mass] at hz
    by_contra hnot
    have hpzero : p.mass z.1 = 0 :=
      le_antisymm (le_of_not_gt hnot) (p.mass_nonneg z.1)
    rw [hpzero, zero_mul] at hz
    exact lt_irrefl 0 hz
  refine ⟨z.1, hp, ?_⟩
  rw [← heq]
  intro e he
  exact (mem_retainEdgeSet z.1 z.2 e).mp he |>.1

/-- Bernoulli count restricted to a deterministic mask. -/
def maskedBernoulliCountReal {E : Type*} [Fintype E]
    (A : Finset E) (z : BooleanConfiguration E) : ℝ :=
  ∑ e ∈ A, BernoulliParameter.bitValue (z e)

def centeredMaskedBernoulliCount {E : Type*} [Fintype E]
    (ρ : BernoulliParameter) (A : Finset E)
    (z : BooleanConfiguration E) : ℝ :=
  maskedBernoulliCountReal A z - (A.card : ℝ) * ρ.p

theorem card_retainEdgeSet_cast {E : Type*} [Fintype E]
    (A : Finset E) (z : BooleanConfiguration E) :
    ((retainEdgeSet A z).card : ℝ) = maskedBernoulliCountReal A z := by
  unfold retainEdgeSet maskedBernoulliCountReal
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro e _
  cases h : z e <;> simp [BernoulliParameter.bitValue]

theorem centeredMaskedBernoulliCount_eq_characterSum
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (A : Finset E)
    (z : BooleanConfiguration E) :
    centeredMaskedBernoulliCount ρ A z =
      ρ.sigma * ∑ e ∈ A, edgeCharacter ρ e z := by
  unfold centeredMaskedBernoulliCount maskedBernoulliCountReal
  simp_rw [bitValue_eq_p_add_sigma_mul_oneCharacter ρ]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, edgeCharacter]
  ring

private theorem maskedCharacterSum_secondMoment
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (A : Finset E) :
    bernoulliExpectation ρ
        (fun z : BooleanConfiguration E ↦
          (∑ e ∈ A, edgeCharacter ρ e z) ^ 2) = A.card := by
  unfold bernoulliExpectation
  calc
    (∑ z : BooleanConfiguration E, bernoulliProductMass ρ z *
        (∑ e ∈ A, edgeCharacter ρ e z) ^ 2) =
        ∑ z : BooleanConfiguration E, ∑ e ∈ A, ∑ f ∈ A,
          bernoulliProductMass ρ z *
            (edgeCharacter ρ e z * edgeCharacter ρ f z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ e ∈ A, ∑ f ∈ A, ∑ z : BooleanConfiguration E,
          bernoulliProductMass ρ z *
            (edgeCharacter ρ e z * edgeCharacter ρ f z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
    _ = ∑ e ∈ A, ∑ f ∈ A,
          if e = f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      have h := fourierCharacters_orthonormal ρ
        ({e} : Finset E) ({f} : Finset E)
      have he : fourierCharacter ρ ({e} : Finset E) =
          edgeCharacter ρ e := by
        funext z
        simp [fourierCharacter_eq_prod]
      have hf : fourierCharacter ρ ({f} : Finset E) =
          edgeCharacter ρ f := by
        funext z
        simp [fourierCharacter_eq_prod]
      rw [he, hf] at h
      simpa [bernoulliInner] using h
    _ = A.card := by simp

theorem bernoulliExpectation_centeredMaskedCount_sq
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (A : Finset E) :
    bernoulliExpectation ρ
        (fun z : BooleanConfiguration E ↦
          (centeredMaskedBernoulliCount ρ A z) ^ 2) =
      (A.card : ℝ) * ρ.variance := by
  simp_rw [centeredMaskedBernoulliCount_eq_characterSum ρ A, mul_pow]
  unfold bernoulliExpectation
  calc
    (∑ z : BooleanConfiguration E, bernoulliProductMass ρ z *
        (ρ.sigma ^ 2 * (∑ e ∈ A, edgeCharacter ρ e z) ^ 2)) =
        ρ.sigma ^ 2 * bernoulliExpectation ρ
          (fun z : BooleanConfiguration E ↦
            (∑ e ∈ A, edgeCharacter ρ e z) ^ 2) := by
      unfold bernoulliExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ρ.sigma ^ 2 * (A.card : ℝ) := by
      rw [maskedCharacterSum_secondMoment]
    _ = (A.card : ℝ) * ρ.variance := by
      rw [ρ.sigma_sq]
      ring

/-- Conditional Chebyshev bound for the number of retained edges of a
deterministic finite set. -/
theorem maskedBernoulliCount_chebyshev
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : BernoulliParameter) (A : Finset E) {a : ℝ} (ha : 0 < a) :
    (bernoulliProductLaw ρ).prob
        (FiniteLaw.event fun z ↦
          a ≤ |centeredMaskedBernoulliCount ρ A z|) ≤
      ((A.card : ℝ) * ρ.variance) / a ^ 2 := by
  let q := bernoulliProductLaw (E := E) ρ
  let Z : BooleanConfiguration E → ℝ := fun z ↦
    (centeredMaskedBernoulliCount ρ A z) ^ 2
  have hmarkov := q.markov Z (fun z ↦ sq_nonneg _) (sq_pos_of_pos ha)
  have hevent :
      FiniteLaw.event (fun z ↦ a ^ 2 ≤ Z z) =
        FiniteLaw.event (fun z ↦
          a ≤ |centeredMaskedBernoulliCount ρ A z|) := by
    ext z
    simp only [FiniteLaw.mem_event, Z]
    have hiff := sq_le_sq₀ (le_of_lt ha)
      (abs_nonneg (centeredMaskedBernoulliCount ρ A z))
    simpa [sq_abs] using hiff
  rw [hevent] at hmarkov
  have hexpect : q.expect Z = (A.card : ℝ) * ρ.variance := by
    simpa [q, FiniteLaw.expect, bernoulliExpectation, Z] using
      bernoulliExpectation_centeredMaskedCount_sq ρ A
  rw [hexpect] at hmarkov
  exact hmarkov

/-- Conditional Bernoulli retention is concentrated around its conditional
mean on the same scale as any tight linear-size random plant. -/
theorem retainedMask_centered_tendstoInProbability
    {E : ℕ → Type*} [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]
    (p : ∀ n, FiniteLaw (Finset (E n)))
    (ρ : BernoulliParameter) (scale : ℕ → ℕ) (a : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hplant : TendstoInProbability p
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ)) a) :
    TendstoInProbability
      (fun n ↦ (p n).product (bernoulliProductLaw ρ))
      (fun n z ↦
        ((retainEdgeSet z.1 z.2).card : ℝ) / (scale n : ℝ) -
          ρ.p * ((z.1.card : ℝ) / (scale n : ℝ))) 0 := by
  intro δ hδ
  let C : ℝ := |a| + 1
  let plantBad : (n : ℕ) → Finset (Finset (E n)) := fun n ↦
    FiniteLaw.event fun A ↦
      1 ≤ |(A.card : ℝ) / (scale n : ℝ) - a|
  let plantGood : (n : ℕ) → Finset (Finset (E n)) := fun n ↦
    Finset.univ \ plantBad n
  let conditionalBad : (n : ℕ) → Finset (E n) →
      Finset (BooleanConfiguration (E n)) := fun n A ↦
    FiniteLaw.event fun z ↦
      δ * (scale n : ℝ) ≤ |centeredMaskedBernoulliCount ρ A z|
  let bad : (n : ℕ) →
      Finset (Finset (E n) × BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun z ↦
      δ ≤ |((retainEdgeSet z.1 z.2).card : ℝ) / (scale n : ℝ) -
        ρ.p * ((z.1.card : ℝ) / (scale n : ℝ))|
  let jointPlantBad : (n : ℕ) →
      Finset (Finset (E n) × BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun z ↦ z.1 ∈ plantBad n
  let jointGoodConditionalBad : (n : ℕ) →
      Finset (Finset (E n) × BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun z ↦
      z.1 ∈ plantGood n ∧ z.2 ∈ conditionalBad n z.1
  let jointEitherBad : (n : ℕ) →
      Finset (Finset (E n) × BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun z ↦
      z.1 ∈ plantBad n ∨
        (z.1 ∈ plantGood n ∧ z.2 ∈ conditionalBad n z.1)
  let B : ℕ → ℝ := fun n ↦
    ((C * ρ.variance) / δ ^ 2) * ((scale n : ℝ))⁻¹
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually_gt_atTop 0
  have hsubset : ∀ᶠ n in atTop,
      bad n ⊆ jointEitherBad n := by
    filter_upwards [hscalePos] with n hn
    have hs : (0 : ℝ) < scale n := by exact_mod_cast hn
    intro z hz
    simp only [bad, jointEitherBad, FiniteLaw.mem_event] at hz ⊢
    by_cases hA : z.1 ∈ plantBad n
    · exact Or.inl hA
    · refine Or.inr ⟨?_, ?_⟩
      · simp [plantGood, hA]
      · rw [FiniteLaw.mem_event]
        have halgebra :
            ((retainEdgeSet z.1 z.2).card : ℝ) / (scale n : ℝ) -
                ρ.p * ((z.1.card : ℝ) / (scale n : ℝ)) =
              centeredMaskedBernoulliCount ρ z.1 z.2 / (scale n : ℝ) := by
          rw [card_retainEdgeSet_cast]
          unfold centeredMaskedBernoulliCount
          field_simp [ne_of_gt hs]
        rw [halgebra, abs_div, abs_of_pos hs] at hz
        exact (le_div_iff₀ hs).mp (by simpa [mul_comm] using hz)
  have hconditional : ∀ᶠ n in atTop,
      ((p n).product (bernoulliProductLaw ρ)).prob
          (jointGoodConditionalBad n) ≤ B n := by
    filter_upwards [hscalePos] with n hn
    have hs : (0 : ℝ) < scale n := by exact_mod_cast hn
    rw [show jointGoodConditionalBad n =
        FiniteLaw.event (fun z :
          Finset (E n) × BooleanConfiguration (E n) ↦
            z.1 ∈ plantGood n ∧ z.2 ∈ conditionalBad n z.1) by rfl,
      FiniteLaw.product_prob_fibers]
    have hterm : ∀ A ∈ plantGood n,
        (bernoulliProductLaw ρ).prob (conditionalBad n A) ≤ B n := by
      intro A hA
      have hclose :
          |(A.card : ℝ) / (scale n : ℝ) - a| < 1 := by
        have hnot : A ∉ plantBad n := by
          simpa [plantGood] using hA
        simpa [plantBad] using hnot
      have hratio_nonneg :
          0 ≤ (A.card : ℝ) / (scale n : ℝ) := by positivity
      have hratio : (A.card : ℝ) / (scale n : ℝ) ≤ C := by
        have htri :
            |(A.card : ℝ) / (scale n : ℝ)| ≤
              |(A.card : ℝ) / (scale n : ℝ) - a| + |a| := by
          simpa only [sub_add_cancel] using abs_add_le
            ((A.card : ℝ) / (scale n : ℝ) - a) a
        rw [abs_of_nonneg hratio_nonneg] at htri
        dsimp only [C]
        linarith
      have hcard : (A.card : ℝ) ≤ C * (scale n : ℝ) :=
        (div_le_iff₀ hs).mp hratio
      have hcheb := maskedBernoulliCount_chebyshev ρ A
        (mul_pos hδ hs)
      change (bernoulliProductLaw ρ).prob
          (FiniteLaw.event fun z ↦
            δ * (scale n : ℝ) ≤
              |centeredMaskedBernoulliCount ρ A z|) ≤ B n
      refine hcheb.trans ?_
      dsimp only [B]
      calc
        ((A.card : ℝ) * ρ.variance) /
              (δ * (scale n : ℝ)) ^ 2 ≤
            ((C * (scale n : ℝ)) * ρ.variance) /
              (δ * (scale n : ℝ)) ^ 2 := by
          gcongr
          exact ρ.variance_pos.le
        _ = ((C * ρ.variance) / δ ^ 2) *
              ((scale n : ℝ))⁻¹ := by
          field_simp [ne_of_gt hs, ne_of_gt hδ]
    calc
      (∑ A ∈ plantGood n, (p n).mass A *
          (bernoulliProductLaw ρ).prob (conditionalBad n A)) ≤
          ∑ A ∈ plantGood n, (p n).mass A * B n := by
        exact Finset.sum_le_sum fun A hA ↦
          mul_le_mul_of_nonneg_left (hterm A hA) ((p n).mass_nonneg A)
      _ = (p n).prob (plantGood n) * B n := by
        unfold FiniteLaw.prob
        rw [Finset.sum_mul]
      _ ≤ 1 * B n := by
        apply mul_le_mul_of_nonneg_right ((p n).prob_le_one (plantGood n))
        dsimp only [B, C]
        exact mul_nonneg
          (div_nonneg (mul_nonneg (by positivity) ρ.variance_pos.le)
            (sq_nonneg δ))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = B n := one_mul _
  have hprobBound : ∀ᶠ n in atTop,
      ((p n).product (bernoulliProductLaw ρ)).prob (bad n) ≤
        (p n).prob (plantBad n) + B n := by
    filter_upwards [hsubset, hconditional] with n hsub hcond
    have heither : jointEitherBad n =
        @Union.union
          (Finset (Finset (E n) × BooleanConfiguration (E n)))
          (@Finset.instUnion (Finset (E n) × BooleanConfiguration (E n))
            (Classical.decEq _))
          (jointPlantBad n) (jointGoodConditionalBad n) := by
      ext z
      simp [jointEitherBad, jointPlantBad, jointGoodConditionalBad]
    calc
      ((p n).product (bernoulliProductLaw ρ)).prob (bad n) ≤
          ((p n).product (bernoulliProductLaw ρ)).prob
            (jointEitherBad n) :=
        ((p n).product (bernoulliProductLaw ρ)).prob_mono hsub
      _ ≤ ((p n).product (bernoulliProductLaw ρ)).prob
              (jointPlantBad n) +
            ((p n).product (bernoulliProductLaw ρ)).prob
              (jointGoodConditionalBad n) := by
        rw [heither]
        exact FiniteLaw.prob_union_le
          ((p n).product (bernoulliProductLaw ρ))
          (jointPlantBad n) (jointGoodConditionalBad n)
      _ ≤ (p n).prob (plantBad n) + B n := by
        rw [FiniteLaw.product_prob_fst]
        exact add_le_add_left hcond _
  have hplantBad : Vanishes fun n ↦ (p n).prob (plantBad n) := by
    simpa only [plantBad] using hplant 1 (by norm_num)
  have hB : Vanishes B := by
    have hinv : Tendsto (fun n ↦ ((scale n : ℝ))⁻¹) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop.comp hscale).inv_tendsto_atTop
    have hmul : Tendsto (fun n ↦
        (C * ρ.variance / δ ^ 2) * ((scale n : ℝ))⁻¹)
        atTop (𝓝 ((C * ρ.variance / δ ^ 2) * 0)) :=
      tendsto_const_nhds.mul hinv
    simpa only [B, mul_zero] using hmul
  simpa only [bad, sub_zero] using
    (squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦
        ((p n).product (bernoulliProductLaw ρ)).prob_nonneg (bad n))
      hprobBound (hplantBad.add hB))

/-- Independent retention multiplies the limiting edge density by the
retention probability. -/
theorem retainedRandomPlant_edgeDensity_tendstoInProbability
    {E : ℕ → Type*} [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]
    (p : ∀ n, FiniteLaw (Finset (E n)))
    (ρ : BernoulliParameter) (scale : ℕ → ℕ) (a : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hplant : TendstoInProbability p
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ)) a) :
    TendstoInProbability
      (fun n ↦ retainedRandomPlantLaw ρ (p n))
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ))
      (ρ.p * a) := by
  have hplantJoint := hplant.product_fst
    (fun n ↦ bernoulliProductLaw (E := E n) ρ)
  have hsignal := hplantJoint.const_mul (c := ρ.p)
  have hnoise := retainedMask_centered_tendstoInProbability
    p ρ scale a hscale hplant
  have hsum := hsignal.add hnoise
  have hretainedJoint : TendstoInProbability
      (fun n ↦ (p n).product (bernoulliProductLaw ρ))
      (fun n z ↦
        ((retainEdgeSet z.1 z.2).card : ℝ) / (scale n : ℝ))
      (ρ.p * a) := by
    convert hsum using 1
    · funext n z
      ring
    · simp
  intro δ hδ
  have hv := hretainedJoint δ hδ
  convert hv using 1
  funext n
  rw [retainedRandomPlantLaw_prob]
  have hevent :
      ({z : Finset (E n) × BooleanConfiguration (E n) |
          retainEdgeSet z.1 z.2 ∈
            FiniteLaw.event (fun A ↦
              δ ≤ |(A.card : ℝ) / (scale n : ℝ) - ρ.p * a|)} :
          Finset (Finset (E n) × BooleanConfiguration (E n))) =
        FiniteLaw.event (fun z :
            Finset (E n) × BooleanConfiguration (E n) ↦
          δ ≤ |((retainEdgeSet z.1 z.2).card : ℝ) /
            (scale n : ℝ) - ρ.p * a|) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      FiniteLaw.mem_event]
  simpa only [] using congrArg
    (fun s ↦ ((p n).product (bernoulliProductLaw ρ)).prob s) hevent

/-! ### The retained twice-truncated plant -/

/-- Retention probability `1 - ε` associated with a fixed noise rate. -/
def retentionParameter (ε : NoiseRate) : BernoulliParameter where
  p := 1 - (ε : ℝ)
  p_pos := sub_pos.mpr ε.2.2
  p_lt_one := by linarith [ε.2.1]

@[simp]
theorem retentionParameter_p (ε : NoiseRate) :
    (retentionParameter ε).p = 1 - (ε : ℝ) := rfl

/-- Edge noise commutes exactly with an arbitrary finite mixture of forcing
likelihoods: on the latent plant it is independent retention at rate
`1-ε`. -/
theorem randomForcedLikelihood_retainedRandomPlantLaw_eq_edgeNoise
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : NoiseRate)
    (p : FiniteLaw (Finset E)) :
    randomForcedLikelihood θ (retainedRandomPlantLaw (retentionParameter ε) p) =
      edgeNoise θ (ε : ℝ) (randomForcedLikelihood θ p) := by
  let retained := retainedRandomPlantLaw (retentionParameter ε) p
  let original := randomForcedLikelihood θ p
  have hcoeff :
      fourierCoeff θ (randomForcedLikelihood θ retained) =
        fourierCoeff θ (edgeNoise θ (ε : ℝ) original) := by
    funext S
    dsimp only [retained, original]
    rw [fourierCoeff_randomForcedLikelihood,
      randomPlantContainmentProbability_retainedRandomPlantLaw,
      fourierCoeff_edgeNoise, fourierCoeff_randomForcedLikelihood,
      retentionParameter_p]
    ring
  funext x
  calc
    randomForcedLikelihood θ retained x =
        fourierSum θ
          (fourierCoeff θ (randomForcedLikelihood θ retained)) x :=
      fourierExpansion θ (randomForcedLikelihood θ retained) x
    _ = fourierSum θ
          (fourierCoeff θ (edgeNoise θ (ε : ℝ) original)) x := by
      rw [hcoeff]
    _ = edgeNoise θ (ε : ℝ) original x :=
      (fourierExpansion θ (edgeNoise θ (ε : ℝ) original) x).symm

/-- Law-valued semantic bridge: resampling the random-forced observation is
exactly the observation obtained by independently retaining the latent plant
edges and then forcing them over the unchanged Bernoulli null. -/
theorem resampleLaw_randomForcedLaw_eq_retainedRandomPlantLaw
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : NoiseRate)
    (p : FiniteLaw (Finset E)) :
    resampleLaw θ ε (randomForcedLaw θ p) =
      randomForcedLaw θ
        (retainedRandomPlantLaw (retentionParameter ε) p) := by
  apply FiniteLaw.ext_mass
  funext y
  change
    (∑ x, (bernoulliProductMass θ x * randomForcedLikelihood θ p x) *
      bernoulliNoiseTransition θ (ε : ℝ) x y) =
    bernoulliProductMass θ y *
      randomForcedLikelihood θ
        (retainedRandomPlantLaw (retentionParameter ε) p) y
  rw [randomForcedLikelihood_retainedRandomPlantLaw_eq_edgeNoise]
  unfold edgeNoise
  calc
    (∑ x, (bernoulliProductMass θ x * randomForcedLikelihood θ p x) *
        bernoulliNoiseTransition θ (ε : ℝ) x y) =
        ∑ x, (bernoulliProductMass θ x *
          bernoulliNoiseTransition θ (ε : ℝ) x y) *
            randomForcedLikelihood θ p x := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, (bernoulliProductMass θ y *
          bernoulliNoiseTransition θ (ε : ℝ) y x) *
            randomForcedLikelihood θ p x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [bernoulliNoise_detailedBalance]
    _ = bernoulliProductMass θ y *
        ∑ x, bernoulliNoiseTransition θ (ε : ℝ) y x *
          randomForcedLikelihood θ p x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- The twice-truncated plant followed by independent edge retention. -/
noncomputable def retainedTwiceTruncatedPlantLawAt
    (ε : NoiseRate) (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ) :
    FiniteLaw (Finset (AmbientEdge (m n))) :=
  retainedRandomPlantLaw (retentionParameter ε)
    (twiceTruncatedPlantLawAt lam r gamma m g n)

/-- A.3 after noise: the retained twice-truncated plant has edge density
`(1-ε)λ/2 + o_P(1)`. -/
theorem retainedTwiceTruncatedPlantLawAt_edgeDensity_tendstoInProbability
    (ε : NoiseRate) (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m g : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ))
    (hgrowth : Vanishes fun n ↦
      (((g n + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ (g n)) /
        (m n : ℝ)) :
    TendstoInProbability
      (retainedTwiceTruncatedPlantLawAt ε lam r gamma m g)
      (fun n A ↦ (A.card : ℝ) / (m n : ℝ))
      ((1 - (ε : ℝ)) * lam / 2) := by
  have hplant := twiceTruncatedPlantLawAt_edgeDensity_tendstoInProbability
    lam r gamma hlam hr hgamma m g hm hpowerScale hgrowth
  have hretained := retainedRandomPlant_edgeDensity_tendstoInProbability
    (twiceTruncatedPlantLawAt lam r gamma m g)
    (retentionParameter ε) m (lam / 2) hm hplant
  simpa only [retainedTwiceTruncatedPlantLawAt, retentionParameter_p,
    mul_div_assoc] using hretained

/-- If the normalized size of a random finite set converges to `a`, then
every fixed threshold `τ<a` is exceeded with probability tending to one.
The integer threshold is exactly `ceil(τ·scale)`. -/
theorem prob_card_ge_ceil_mul_tendsToOne
    {E : ℕ → Type*} [∀ n, Fintype (E n)]
    (p : ∀ n, FiniteLaw (Finset (E n)))
    (scale : ℕ → ℕ) (a τ : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hτ : τ < a)
    (hlimit : TendstoInProbability p
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ)) a) :
    TendsToOne fun n ↦
      (p n).prob (FiniteLaw.event fun A ↦
        ⌈τ * (scale n : ℝ)⌉₊ ≤ A.card) := by
  let δ : ℝ := (a - τ) / 2
  let high : (n : ℕ) → Finset (Finset (E n)) := fun n ↦
    FiniteLaw.event fun A ↦ ⌈τ * (scale n : ℝ)⌉₊ ≤ A.card
  let bad : (n : ℕ) → Finset (Finset (E n)) := fun n ↦
    FiniteLaw.event fun A ↦
      δ ≤ |(A.card : ℝ) / (scale n : ℝ) - a|
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hbad : Vanishes fun n ↦ (p n).prob (bad n) := by
    simpa only [bad] using hlimit δ hδ
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually_gt_atTop 0
  have hsubset : ∀ᶠ n in atTop,
      Finset.univ \ high n ⊆ bad n := by
    filter_upwards [hscalePos] with n hn
    have hs : (0 : ℝ) < scale n := by exact_mod_cast hn
    intro A hA
    have hnotHigh : ¬ ⌈τ * (scale n : ℝ)⌉₊ ≤ A.card := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, high,
        FiniteLaw.mem_event] using hA
    have hcardLtCeil : A.card < ⌈τ * (scale n : ℝ)⌉₊ :=
      Nat.lt_of_not_ge hnotHigh
    have hcardLt : (A.card : ℝ) < τ * (scale n : ℝ) :=
      Nat.lt_ceil.mp hcardLtCeil
    have hratio : (A.card : ℝ) / (scale n : ℝ) < τ := by
      exact (div_lt_iff₀ hs).2 (by simpa [mul_comm] using hcardLt)
    rw [FiniteLaw.mem_event]
    rw [abs_of_neg (sub_neg.mpr (hratio.trans hτ))]
    dsimp only [δ]
    linarith
  have hmiss : Vanishes fun n ↦
      (p n).prob (Finset.univ \ high n) := by
    exact squeeze_zero'
      (Eventually.of_forall fun n ↦
        (p n).prob_nonneg (Finset.univ \ high n))
      (hsubset.mono fun n hn ↦ (p n).prob_mono hn)
      hbad
  have hcomp : Tendsto (fun n ↦ 1 -
      (p n).prob (Finset.univ \ high n)) atTop (nhds 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hmiss : Tendsto _ atTop (nhds ((1 : ℝ) - 0)))
  change Tendsto (fun n ↦ (p n).prob (high n)) atTop (nhds 1)
  apply hcomp.congr'
  exact Eventually.of_forall fun n ↦ by
    have hprob := FiniteLaw.prob_univ_sdiff (p n) (high n)
    linarith

/-! ## Uniform injection into the ambient graph -/

/-- An injective vertex map induces an injective map of complete-graph edge
coordinates. -/
def ambientEdgeEmbeddingOfVertexEmbedding {m n : ℕ}
    (φ : Fin m ↪ Fin n) : AmbientEdge m ↪ AmbientEdge n where
  toFun e := ⟨Sym2.map φ e.1, by
    simpa only [AmbientEdge, SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
      Sym2.isDiag_map φ.injective] using e.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact Sym2.map.injective φ.injective (congrArg Subtype.val hef)

/-- Image of a finite edge set under an injective vertex map. -/
noncomputable def embedAmbientEdgeSet {m n : ℕ} (φ : Fin m ↪ Fin n)
    (A : Finset (AmbientEdge m)) : Finset (AmbientEdge n) :=
  A.map (ambientEdgeEmbeddingOfVertexEmbedding φ)

@[simp]
theorem card_embedAmbientEdgeSet {m n : ℕ} (φ : Fin m ↪ Fin n)
    (A : Finset (AmbientEdge m)) :
    (embedAmbientEdgeSet φ A).card = A.card := by
  simp [embedAmbientEdgeSet]

/-- Vertex image of an embedding, represented as a finset. -/
noncomputable def embeddingVertexSet {m n : ℕ} (φ : Fin m ↪ Fin n) :
    Finset (Fin n) :=
  Finset.univ.map φ

@[simp]
theorem card_embeddingVertexSet {m n : ℕ} (φ : Fin m ↪ Fin n) :
    (embeddingVertexSet φ).card = m := by
  simp [embeddingVertexSet]

/-- The canonical lift of a source vertex to the subtype of the image. -/
def liftToEmbeddingVertexSet {m n : ℕ} (φ : Fin m ↪ Fin n) :
    Fin m ↪ embeddingVertexSet φ where
  toFun v := ⟨φ v, by simp [embeddingVertexSet]⟩
  inj' := fun _ _ h ↦ φ.injective (congrArg Subtype.val h)

/-- Every embedded source edge has both endpoints in the image vertex set. -/
theorem embedAmbientEdgeSet_subset_ambientEdgesOn_embeddingVertexSet
    {m n : ℕ} (φ : Fin m ↪ Fin n) (A : Finset (AmbientEdge m)) :
    embedAmbientEdgeSet φ A ⊆ ambientEdgesOn (embeddingVertexSet φ) := by
  intro e he
  rw [embedAmbientEdgeSet, Finset.mem_map] at he
  rcases he with ⟨a, ha, rfl⟩
  rw [ambientEdgesOn, Finset.mem_map]
  let lift := liftToEmbeddingVertexSet φ
  let a' : (⊤ : SimpleGraph (embeddingVertexSet φ)).edgeSet :=
    ⟨Sym2.map lift a.1, by
      simpa only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
        Sym2.isDiag_map lift.injective] using a.2⟩
  refine ⟨a', Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map lift a.1) = Sym2.map φ a.1
  rw [Sym2.map_map]
  congr 1

/-- The uniform law on ambient vertex permutations. -/
noncomputable def uniformPermutationLaw (n : ℕ) :
    FiniteLaw (Equiv.Perm (Fin n)) where
  mass _ := uniformPermutationWeight n
  mass_nonneg _ := (uniformPermutationWeight_pos n).le
  sum_mass := by
    simp only [Finset.sum_const, nsmul_eq_mul, uniformPermutationWeight]
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr
        ⟨Equiv.refl (Fin n)⟩ : 0 < Fintype.card (Equiv.Perm (Fin n))).ne'
    rw [Finset.card_univ]
    field_simp

/-- Push a random plant on `m` vertices through a uniformly random injection
into `n` vertices.  Sampling a canonical inclusion followed by a uniform
ambient permutation induces the uniform law on injections. -/
noncomputable def uniformlyInjectedPlantLaw {m n : ℕ} (h : m ≤ n)
    (p : FiniteLaw (Finset (AmbientEdge m))) :
    FiniteLaw (Finset (AmbientEdge n)) :=
  (p.product (uniformPermutationLaw n)).map fun z ↦
    embedAmbientEdgeSet ((Fin.castLEEmb h).trans z.2.toEmbedding) z.1

theorem uniformlyInjectedPlantLaw_prob {m n : ℕ} (h : m ≤ n)
    (p : FiniteLaw (Finset (AmbientEdge m)))
    (s : Finset (Finset (AmbientEdge n))) :
    (uniformlyInjectedPlantLaw h p).prob s =
      (p.product (uniformPermutationLaw n)).prob
        {z | embedAmbientEdgeSet
          ((Fin.castLEEmb h).trans z.2.toEmbedding) z.1 ∈ s} := by
  rw [uniformlyInjectedPlantLaw, FiniteLaw.prob_map]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Injecting a random plant does not change its edge-count distribution. -/
theorem uniformlyInjectedPlantLaw_prob_card_ge {m n K : ℕ} (h : m ≤ n)
    (p : FiniteLaw (Finset (AmbientEdge m))) :
    (uniformlyInjectedPlantLaw h p).prob
        (FiniteLaw.event fun A ↦ K ≤ A.card) =
      p.prob (FiniteLaw.event fun A ↦ K ≤ A.card) := by
  rw [uniformlyInjectedPlantLaw, FiniteLaw.prob_map]
  simpa [FiniteLaw.event] using
    (FiniteLaw.product_prob_fst p (uniformPermutationLaw n)
      (FiniteLaw.event fun A ↦ K ≤ A.card))

/-- Uniform injection preserves convergence in probability of every
edge-count statistic. -/
theorem uniformlyInjectedPlantLaw_edgeDensity_tendstoInProbability
    (m N scale : ℕ → ℕ) (hfit : ∀ n, m n ≤ N n)
    (p : ∀ n, FiniteLaw (Finset (AmbientEdge (m n)))) (a : ℝ)
    (hlimit : TendstoInProbability p
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ)) a) :
    TendstoInProbability
      (fun n ↦ uniformlyInjectedPlantLaw (hfit n) (p n))
      (fun n A ↦ (A.card : ℝ) / (scale n : ℝ)) a := by
  intro δ hδ
  have hv := hlimit δ hδ
  convert hv using 1
  funext n
  rw [uniformlyInjectedPlantLaw_prob]
  have hevent :
      ({z : Finset (AmbientEdge (m n)) × Equiv.Perm (Fin (N n)) |
          embedAmbientEdgeSet
            ((Fin.castLEEmb (hfit n)).trans z.2.toEmbedding) z.1 ∈
              FiniteLaw.event (fun A ↦
                δ ≤ |(A.card : ℝ) / (scale n : ℝ) - a|)} :
        Finset (Finset (AmbientEdge (m n)) × Equiv.Perm (Fin (N n)))) =
      FiniteLaw.event fun z ↦
        δ ≤ |(z.1.card : ℝ) / (scale n : ℝ) - a| := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      FiniteLaw.mem_event, card_embedAmbientEdgeSet]
  rw [hevent]
  simpa [FiniteLaw.event] using
    (FiniteLaw.product_prob_fst (p n) (uniformPermutationLaw (N n))
      (FiniteLaw.event fun A ↦
        δ ≤ |(A.card : ℝ) / (scale n : ℝ) - a|))

/-- Every edge set in the support of the injected law lies inside the
complete graph on an `m`-vertex set. -/
theorem uniformlyInjectedPlantLaw_mass_pos_fits {m n : ℕ} (h : m ≤ n)
    (p : FiniteLaw (Finset (AmbientEdge m)))
    {B : Finset (AmbientEdge n)}
    (hB : 0 < (uniformlyInjectedPlantLaw h p).mass B) :
    ∃ U : Finset (Fin n), U.card = m ∧ B ⊆ ambientEdgesOn U := by
  unfold uniformlyInjectedPlantLaw at hB
  rcases FiniteLaw.exists_preimage_of_map_mass_pos _ _ hB with
    ⟨z, heq, _hz⟩
  let φ := (Fin.castLEEmb h).trans z.2.toEmbedding
  refine ⟨embeddingVertexSet φ, card_embeddingVertexSet φ, ?_⟩
  rw [← heq]
  exact embedAmbientEdgeSet_subset_ambientEdgesOn_embeddingVertexSet φ z.1

/-- Retaining edges after uniform injection preserves the same supporting
`m`-vertex set. -/
theorem retainedUniformlyInjectedPlantLaw_mass_pos_fits
    {m n : ℕ} (h : m ≤ n) (ρ : BernoulliParameter)
    (p : FiniteLaw (Finset (AmbientEdge m)))
    {B : Finset (AmbientEdge n)}
    (hB : 0 < (retainedRandomPlantLaw ρ
      (uniformlyInjectedPlantLaw h p)).mass B) :
    ∃ U : Finset (Fin n), U.card = m ∧ B ⊆ ambientEdgesOn U := by
  rcases retainedRandomPlantLaw_mass_pos_subset ρ
      (uniformlyInjectedPlantLaw h p) hB with ⟨A, hA, hBA⟩
  rcases uniformlyInjectedPlantLaw_mass_pos_fits h p hA with
    ⟨U, hUcard, hAU⟩
  exact ⟨U, hUcard, hBA.trans hAU⟩

/-! ## The scan statistic and its exact null union bound -/

/-- The maximum number of observed edges induced by an `m`-vertex set. -/
noncomputable def graphScanStatistic (n m : ℕ)
    (x : BooleanConfiguration (AmbientEdge n)) : ℕ :=
  (vertexSubsets n m).sup fun U ↦ localEdgeCount x U

/-- Rejection event `M_n ≥ K`, written in its witness form.  By
`mem_localBadEventAtSize_iff`, this is exactly the upper level set of the scan
statistic. -/
noncomputable def graphScanRejectEvent (n m K : ℕ) :
    Finset (BooleanConfiguration (AmbientEdge n)) :=
  localBadEventAtSize n m K

theorem mem_graphScanRejectEvent_iff {n m K : ℕ}
    (x : BooleanConfiguration (AmbientEdge n)) :
    x ∈ graphScanRejectEvent n m K ↔
      ∃ U : Finset (Fin n), U.card = m ∧ K ≤ localEdgeCount x U := by
  exact mem_localBadEventAtSize_iff x

/-- A fixed forcing likelihood vanishes unless every forced edge is present. -/
theorem forcedLikelihood_eq_zero_of_not_subset_present
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E)
    (x : BooleanConfiguration E)
    (hmiss : ¬∀ e ∈ A, x e = true) :
    forcedLikelihood θ A x = 0 := by
  push_neg at hmiss
  rcases hmiss with ⟨e, heA, hefalse⟩
  have hbit : BernoulliParameter.bitValue (x e) / θ.p = 0 := by
    cases hxe : x e
    · simp [BernoulliParameter.bitValue]
    · exact (hefalse hxe).elim
  unfold forcedLikelihood
  exact Finset.prod_eq_zero heA hbit

/-- If a forced set of at least `K` edges lies on `m` vertices, any
configuration containing it is accepted by the scan test. -/
theorem mem_graphScanRejectEvent_of_forcedSet
    {n m K : ℕ} {A : Finset (AmbientEdge n)}
    {x : BooleanConfiguration (AmbientEdge n)}
    (hcard : K ≤ A.card)
    (hfit : ∃ U : Finset (Fin n), U.card = m ∧ A ⊆ ambientEdgesOn U)
    (hpresent : ∀ e ∈ A, x e = true) :
    x ∈ graphScanRejectEvent n m K := by
  rcases hfit with ⟨U, hUcard, hAU⟩
  rw [mem_graphScanRejectEvent_iff]
  refine ⟨U, hUcard, hcard.trans ?_⟩
  unfold localEdgeCount
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨hAU he, hpresent e he⟩

/-- Null mass, reweighted by one fixed forcing likelihood, assigned to an
event. -/
noncomputable def forcedObservationEventMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E)
    (event : Finset (BooleanConfiguration E)) : ℝ :=
  ∑ x ∈ event, bernoulliProductMass θ x * forcedLikelihood θ A x

/-- A forcing component gives probability one to any event containing all
configurations on which its likelihood is nonzero. -/
theorem forcedObservationEventMass_eq_one
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E)
    (event : Finset (BooleanConfiguration E))
    (hsupport : ∀ x, forcedLikelihood θ A x ≠ 0 → x ∈ event) :
    forcedObservationEventMass θ A event = 1 := by
  let f : BooleanConfiguration E → ℝ := fun x ↦
    bernoulliProductMass θ x * forcedLikelihood θ A x
  have hcomp : ∑ x ∈ eventᶜ, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : x ∉ event := by simpa using hx
    have hzero : forcedLikelihood θ A x = 0 := by
      by_contra hnz
      exact hxnot (hsupport x hnz)
    simp [f, hzero]
  have hsplit := event.sum_add_sum_compl f
  have hfull : ∑ x, f x = 1 := by
    simpa only [f, bernoulliExpectation] using
      bernoulliExpectation_forcedLikelihood θ A
  unfold forcedObservationEventMass
  change ∑ x ∈ event, f x = 1
  rw [hfull, hcomp] at hsplit
  linarith

/-- Mixture-level planted power: if every positive-mass forced set lies on
`m` vertices, then scan rejection is at least the probability that the
forced set has `K` edges. -/
theorem randomForcedLaw_prob_graphScanRejectEvent_ge
    (n m K : ℕ) (θ : BernoulliParameter)
    (p : FiniteLaw (Finset (AmbientEdge n)))
    (hfits : ∀ {A : Finset (AmbientEdge n)}, 0 < p.mass A →
      ∃ U : Finset (Fin n), U.card = m ∧ A ⊆ ambientEdgesOn U) :
    p.prob (FiniteLaw.event fun A ↦ K ≤ A.card) ≤
      (randomForcedLaw θ p).prob (graphScanRejectEvent n m K) := by
  let good : Finset (Finset (AmbientEdge n)) :=
    FiniteLaw.event fun A ↦ K ≤ A.card
  let reject := graphScanRejectEvent n m K
  have hcomponent (A : Finset (AmbientEdge n)) (hA : A ∈ good) :
      p.mass A * forcedObservationEventMass θ A reject = p.mass A := by
    by_cases hpzero : p.mass A = 0
    · simp [hpzero]
    · have hp : 0 < p.mass A := lt_of_le_of_ne (p.mass_nonneg A) (Ne.symm hpzero)
      have hfit := hfits hp
      have hcard : K ≤ A.card := by simpa [good] using hA
      have hone : forcedObservationEventMass θ A reject = 1 := by
        apply forcedObservationEventMass_eq_one
        intro x hnonzero
        apply mem_graphScanRejectEvent_of_forcedSet hcard hfit
        intro e he
        by_contra hfalse
        have hz := forcedLikelihood_eq_zero_of_not_subset_present θ A x (by
          push_neg
          exact ⟨e, he, by simpa using hfalse⟩)
        exact hnonzero hz
      rw [hone, mul_one]
  unfold FiniteLaw.prob
  change (∑ A ∈ good, p.mass A) ≤
    ∑ x ∈ reject,
      bernoulliProductMass θ x * randomForcedLikelihood θ p x
  calc
    (∑ A ∈ good, p.mass A) =
        ∑ A ∈ good, p.mass A * forcedObservationEventMass θ A reject := by
      apply Finset.sum_congr rfl
      intro A hA
      exact (hcomponent A hA).symm
    _ = ∑ x ∈ reject, ∑ A ∈ good,
          p.mass A *
            (bernoulliProductMass θ x * forcedLikelihood θ A x) := by
      unfold forcedObservationEventMass
      calc
        (∑ A ∈ good, p.mass A *
            ∑ x ∈ reject,
              bernoulliProductMass θ x * forcedLikelihood θ A x) =
            ∑ A ∈ good, ∑ x ∈ reject,
              p.mass A *
                (bernoulliProductMass θ x * forcedLikelihood θ A x) := by
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]
    _ ≤ ∑ x ∈ reject, ∑ A : Finset (AmbientEdge n),
          p.mass A *
            (bernoulliProductMass θ x * forcedLikelihood θ A x) := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
        (fun A _ _ ↦ mul_nonneg (p.mass_nonneg A)
          (mul_nonneg (bernoulliProductMass_nonneg θ x)
            (forcedLikelihood_nonneg θ A x)))
    _ = ∑ x ∈ reject,
          bernoulliProductMass θ x * randomForcedLikelihood θ p x := by
      apply Finset.sum_congr rfl
      intro x _
      unfold randomForcedLikelihood
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring

/-- Planted scan power for the actual uniformly injected random plant law. -/
theorem randomForcedLaw_uniformlyInjected_prob_scan_ge
    {m n K : ℕ} (h : m ≤ n) (θ : BernoulliParameter)
    (p : FiniteLaw (Finset (AmbientEdge m))) :
    p.prob (FiniteLaw.event fun A ↦ K ≤ A.card) ≤
      (randomForcedLaw θ (uniformlyInjectedPlantLaw h p)).prob
        (graphScanRejectEvent n m K) := by
  rw [← uniformlyInjectedPlantLaw_prob_card_ge h p]
  exact randomForcedLaw_prob_graphScanRejectEvent_ge n m K θ
    (uniformlyInjectedPlantLaw h p)
    (fun {_A} hA ↦ uniformlyInjectedPlantLaw_mass_pos_fits h p hA)

/-- The exact two-level union bound in the proof of Theorem A.1:
`P_Q(M_n ≥ K) ≤ C(n,m) C(C(m,2),K) p^K`. -/
theorem erdosRenyi_prob_graphScanRejectEvent_le
    (θ : BernoulliParameter) (n m K : ℕ) :
    (erdosRenyiLaw (n := n) θ).prob (graphScanRejectEvent n m K) ≤
      (n.choose m : ℝ) * ((m.choose 2).choose K : ℝ) * θ.p ^ K := by
  exact bernoulliProductLaw_prob_localBadEventAtSize_le θ n m K

/-- The null scan tail in the regime used in Appendix A.  It is enough that
`m→∞`, `m/n→0`, and the linear threshold factor lies strictly between
one and two. -/
theorem sparseErdosRenyi_graphScanRejectEvent_vanishes
    (c τ : ℝ) (hc : 0 < c) (hτ : τ ∈ Set.Ioo (1 : ℝ) 2)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hratio : Vanishes fun n ↦ (m n : ℝ) / (n : ℝ)) :
    Vanishes fun n ↦
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob
        (graphScanRejectEvent n (m n) ⌈τ * (m n : ℝ)⌉₊) := by
  let K : ℕ → ℕ := fun n ↦ ⌈τ * (m n : ℝ)⌉₊
  let B : ℝ := localSparsityBase c
  let α : ℝ := (τ - 1) / 2
  let C : ℝ := (Real.log B + 1) / α
  have hBOne : 1 < B := by
    exact one_lt_localSparsityBase c
  have hB : 0 < B := zero_lt_one.trans hBOne
  have hlogB : 0 < Real.log B := Real.log_pos hBOne
  have hα : 0 < α := by dsimp only [α]; linarith [hτ.1]
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (add_pos_of_pos_of_nonneg hlogB zero_le_one) hα
  have hmPos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually_gt_atTop 0
  have hnPos : ∀ᶠ n in atTop, 0 < n := eventually_gt_atTop 0
  have hp : ∀ᶠ n in atTop,
      (sparseBernoulliParameter c n).p = c / (n : ℝ) :=
    eventually_sparseBernoulliParameter_p_eq hc
  have hratioSmall : ∀ᶠ n in atTop,
      (m n : ℝ) / (n : ℝ) < Real.exp (-C) := by
    exact hratio.eventually_lt_const (Real.exp_pos (-C))
  have hbound : ∀ᶠ n in atTop,
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob
          (graphScanRejectEvent n (m n) (K n)) ≤
        Real.exp (-(m n : ℝ)) := by
    filter_upwards [hmPos, hnPos, hp, hratioSmall] with n hmn hn hpN hsmall
    have hmreal : (0 : ℝ) < m n := by exact_mod_cast hmn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hratioPos : (0 : ℝ) < (m n : ℝ) / (n : ℝ) :=
      div_pos hmreal hnreal
    have hmK : m n ≤ K n := by
      have hcast : (m n : ℝ) ≤ (K n : ℝ) := by
        calc
          (m n : ℝ) ≤ τ * (m n : ℝ) := by
            nlinarith [hτ.1, hmreal.le]
          _ ≤ (K n : ℝ) := by
            exact Nat.le_ceil (τ * (m n : ℝ))
      exact_mod_cast hcast
    have hKthree : K n ≤ 3 * m n := by
      rw [Nat.ceil_le]
      push_cast
      nlinarith [hτ.2, hmreal.le]
    have hunion := erdosRenyi_prob_graphScanRejectEvent_le
      (sparseBernoulliParameter c n) n (m n) (K n)
    have hfactor := localUnionTerm_le_base_mul_ratio_pow
      (lam := c) hc.le hn hmn hmK hKthree
      (sparseBernoulliParameter c n) hpN
    have hlogRatio :
        Real.log ((m n : ℝ) / (n : ℝ)) ≤ -C := by
      have hlog := Real.log_le_log hratioPos hsmall.le
      simpa only [Real.log_exp] using hlog
    have hlogRatioNeg :
        Real.log ((m n : ℝ) / (n : ℝ)) ≤ 0 := by
      exact hlogRatio.trans (neg_nonpos.mpr hC.le)
    have hd : α * (m n : ℝ) ≤ ((K n - m n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hmK]
      have hceil := Nat.le_ceil (τ * (m n : ℝ))
      dsimp only [K]
      calc
        α * (m n : ℝ) ≤ (τ - 1) * (m n : ℝ) := by
          dsimp only [α]
          nlinarith [hτ.1, hmreal.le]
        _ = τ * (m n : ℝ) - (m n : ℝ) := by ring
        _ ≤ (⌈τ * (m n : ℝ)⌉₊ : ℝ) - (m n : ℝ) :=
          sub_le_sub_right hceil _
    have hmulD :
        ((K n - m n : ℕ) : ℝ) *
            Real.log ((m n : ℝ) / (n : ℝ)) ≤
          (α * (m n : ℝ)) *
            Real.log ((m n : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonpos_right hd hlogRatioNeg
    have hmulLog :
        (α * (m n : ℝ)) *
            Real.log ((m n : ℝ) / (n : ℝ)) ≤
          -(m n : ℝ) * (Real.log B + 1) := by
      calc
        (α * (m n : ℝ)) *
            Real.log ((m n : ℝ) / (n : ℝ)) ≤
            (α * (m n : ℝ)) * (-C) := by
              exact mul_le_mul_of_nonneg_left hlogRatio
                (mul_nonneg hα.le (Nat.cast_nonneg _))
        _ = -(m n : ℝ) * (Real.log B + 1) := by
          dsimp only [C]
          field_simp [hα.ne']
    have hlogBound :
        (m n : ℝ) * Real.log B +
            ((K n - m n : ℕ) : ℝ) *
              Real.log ((m n : ℝ) / (n : ℝ)) ≤
          -(m n : ℝ) := by
      linarith
    calc
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob
          (graphScanRejectEvent n (m n) (K n)) ≤
          (n.choose (m n) : ℝ) *
            (((m n).choose 2).choose (K n) : ℝ) *
              (sparseBernoulliParameter c n).p ^ (K n) := hunion
      _ ≤ B ^ (m n) *
          ((m n : ℝ) / (n : ℝ)) ^ (K n - m n) := hfactor
      _ ≤ Real.exp (-(m n : ℝ)) :=
        base_mul_ratio_pow_le_exp_neg hB hratioPos (m n)
          (K n - m n) hlogBound
  have hexp : Vanishes fun n ↦ Real.exp (-(m n : ℝ)) := by
    have hpow : Tendsto (fun n ↦ ((1 : ℝ) / 2) ^ (m n))
        atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).comp hm
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ Real.exp_nonneg _)
      (Eventually.of_forall fun n ↦ exp_neg_natCast_le_half_pow (m n))
      hpow
  change Vanishes fun n ↦
    (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob
      (graphScanRejectEvent n (m n) (K n))
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob_nonneg
        (graphScanRejectEvent n (m n) (K n)))
    hbound hexp

/-- Null scan tail at the exact appendix scales. -/
theorem appendix_nullScan_vanishes
    (c τ r : ℝ) (hc : 0 < c) (hτ : τ ∈ Set.Ioo (1 : ℝ) 2)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    Vanishes fun n ↦
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)).prob
        (graphScanRejectEvent n (appendixPlantSize r n)
          (appendixScanThreshold τ r n)) := by
  simpa only [appendixScanThreshold] using
    sparseErdosRenyi_graphScanRejectEvent_vanishes c τ hc hτ
      (appendixPlantSize r) (appendixPlantSize_tendsto_atTop hr.1)
      (appendixPlantSize_div_index_vanishes hr.2)

/-! ## The statistical half of Theorem A.1 -/

/-- The twice-truncated appendix plant after uniform injection into the
ambient vertex set. -/
noncomputable def appendixInjectedTruncatedPlantLaw
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    FiniteLaw (Finset (AmbientEdge n)) :=
  uniformlyInjectedPlantLaw
    (appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)
    (twiceTruncatedPlantLawAt lam r gamma
      (appendixPlantSize r) appendixCycleCutoff n)

/-- The pre-noise alternative observation law. -/
noncomputable def appendixAlternativeLaw
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  randomForcedLaw (sparseBernoulliParameter c n)
    (appendixInjectedTruncatedPlantLaw lam r gamma hr n)

theorem appendixAlternativeLaw_eq
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixAlternativeLaw c lam r gamma hr n =
      randomForcedLaw (sparseBernoulliParameter c n)
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n) := rfl

/-- The observed noised alternative used by the scan proof: sample the
twice-truncated plant, inject it uniformly, retain each planted edge with
probability `1-ε`, and superpose it on `G(n,c/n)`. -/
noncomputable def appendixNoisedAlternativeLaw
    (ε : NoiseRate) (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  randomForcedLaw (sparseBernoulliParameter c n)
    (retainedRandomPlantLaw (retentionParameter ε)
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n))

theorem appendixNoisedAlternativeLaw_eq
    (ε : NoiseRate) (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixNoisedAlternativeLaw ε c lam r gamma hr n =
      randomForcedLaw (sparseBernoulliParameter c n)
        (retainedRandomPlantLaw (retentionParameter ε)
          (appendixInjectedTruncatedPlantLaw lam r gamma hr n)) := rfl

/-- Exact bridge to the paper's noise operator: the direct generative
noised alternative is `resampleLaw` applied to the pre-noise alternative. -/
theorem resampleLaw_appendixAlternativeLaw
    (ε : NoiseRate) (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    resampleLaw (sparseBernoulliParameter c n) ε
        (appendixAlternativeLaw c lam r gamma hr n) =
      appendixNoisedAlternativeLaw ε c lam r gamma hr n := by
  rw [appendixAlternativeLaw_eq, appendixNoisedAlternativeLaw_eq]
  exact resampleLaw_randomForcedLaw_eq_retainedRandomPlantLaw
    (E := AmbientEdge n)
    (sparseBernoulliParameter c n) ε
    (appendixInjectedTruncatedPlantLaw lam r gamma hr n)

/-- Exact finite-`n` scan lower bound for the appendix alternative. -/
theorem appendixNoisedAlternativeLaw_prob_scan_ge
    (ε : NoiseRate) (c lam r gamma τ : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    (retainedRandomPlantLaw (retentionParameter ε)
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n)).prob
      (FiniteLaw.event fun A ↦ appendixScanThreshold τ r n ≤ A.card) ≤
    (appendixNoisedAlternativeLaw ε c lam r gamma hr n).prob
      (graphScanRejectEvent n (appendixPlantSize r n)
        (appendixScanThreshold τ r n)) := by
  unfold appendixNoisedAlternativeLaw
  apply randomForcedLaw_prob_graphScanRejectEvent_ge
  intro A hA
  unfold appendixInjectedTruncatedPlantLaw at hA
  exact retainedUniformlyInjectedPlantLaw_mass_pos_fits
    (appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)
    (retentionParameter ε)
    (twiceTruncatedPlantLawAt lam r gamma
      (appendixPlantSize r) appendixCycleCutoff n) hA

/-- The planted scan rejects with probability `1-o(1)` whenever its
threshold factor is below the retained density `(1-ε)λ/2`. -/
theorem appendix_plantedScan_tendsToOne
    (ε : NoiseRate) (c lam r gamma τ : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hτ : τ < (1 - (ε : ℝ)) * lam / 2)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (appendixPlantSize r n : ℝ) /
        Real.log (n : ℝ))
    (hgrowth : Vanishes fun n ↦
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          (max 1 lam) ^ (appendixCycleCutoff n)) /
        (appendixPlantSize r n : ℝ)) :
    TendsToOne fun n ↦
      (appendixNoisedAlternativeLaw ε c lam r gamma hr n).prob
        (graphScanRejectEvent n (appendixPlantSize r n)
          (appendixScanThreshold τ r n)) := by
  have hm := appendixPlantSize_tendsto_atTop hr.1
  have hsource := twiceTruncatedPlantLawAt_edgeDensity_tendstoInProbability
    lam r gamma hlam hr hgamma (appendixPlantSize r)
    appendixCycleCutoff hm hpowerScale hgrowth
  have hinjected := uniformlyInjectedPlantLaw_edgeDensity_tendstoInProbability
    (appendixPlantSize r) (fun n ↦ n) (appendixPlantSize r)
    (fun n ↦ appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)
    (twiceTruncatedPlantLawAt lam r gamma
      (appendixPlantSize r) appendixCycleCutoff) (lam / 2) hsource
  have hdensityRaw := retainedRandomPlant_edgeDensity_tendstoInProbability
    (appendixInjectedTruncatedPlantLaw lam r gamma hr)
    (retentionParameter ε) (appendixPlantSize r) (lam / 2) hm
    (by simpa only [appendixInjectedTruncatedPlantLaw] using hinjected)
  have hdensity : TendstoInProbability
      (fun n ↦ retainedRandomPlantLaw (retentionParameter ε)
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n))
      (fun n A ↦ (A.card : ℝ) / (appendixPlantSize r n : ℝ))
      ((1 - (ε : ℝ)) * lam / 2) := by
    simpa only [retentionParameter_p, mul_div_assoc] using hdensityRaw
  have hcard := prob_card_ge_ceil_mul_tendsToOne
    (fun n ↦ retainedRandomPlantLaw (retentionParameter ε)
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n))
    (appendixPlantSize r) ((1 - (ε : ℝ)) * lam / 2) τ
    hm hτ hdensity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hcard
    tendsto_const_nhds
    (fun n ↦ appendixNoisedAlternativeLaw_prob_scan_ge
      ε c lam r gamma τ hr n)
    (fun n ↦ (appendixNoisedAlternativeLaw ε c lam r gamma hr n).prob_le_one
      (graphScanRejectEvent n (appendixPlantSize r n)
        (appendixScanThreshold τ r n)))

/-- **Statistical distinguishability in paper Theorem A.1.**  For any scan
factor `1<τ<2` below the retained plant density, the exact scan event has
vanishing null probability and asymptotic power one; hence the total
variation distance between the noised alternative and `G(n,c/n)` tends to
one. -/
theorem appendix_statisticalDistinguishability
    (ε : NoiseRate) (c lam r gamma τ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hτrange : τ ∈ Set.Ioo (1 : ℝ) 2)
    (hτplant : τ < (1 - (ε : ℝ)) * lam / 2)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (appendixPlantSize r n : ℝ) /
        Real.log (n : ℝ))
    (hgrowth : Vanishes fun n ↦
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          (max 1 lam) ^ (appendixCycleCutoff n)) /
        (appendixPlantSize r n : ℝ)) :
    TendsToOne fun n ↦
      (appendixNoisedAlternativeLaw ε c lam r gamma hr n).tv
        (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)) := by
  apply totalVariation_tendsToOne_of_tests
    (appendixNoisedAlternativeLaw ε c lam r gamma hr)
    (fun n ↦ erdosRenyiLaw (n := n) (sparseBernoulliParameter c n))
    (fun n ↦ graphScanRejectEvent n (appendixPlantSize r n)
      (appendixScanThreshold τ r n))
  · exact appendix_nullScan_vanishes c τ r hc hτrange
      ⟨hr.1, hr.2.trans (by norm_num)⟩
  · exact appendix_plantedScan_tendsToOne ε c lam r gamma τ hlam hr
      hgamma hτplant hpowerScale hgrowth

/-- A canonical admissible threshold factor between one and the retained
plant density.  The extra `min 2` keeps the null-tail estimate in its
convenient `τ<2` range even when the signal is much denser. -/
noncomputable def appendixCanonicalScanFactor
    (ε : NoiseRate) (lam : ℝ) : ℝ :=
  (1 + min 2 ((1 - (ε : ℝ)) * lam / 2)) / 2

theorem appendixCanonicalScanFactor_mem_Ioo
    (ε : NoiseRate) (lam : ℝ)
    (hsuper : 1 < (1 - (ε : ℝ)) * lam / 2) :
    appendixCanonicalScanFactor ε lam ∈ Set.Ioo (1 : ℝ) 2 := by
  have hminLower : 1 < min 2 ((1 - (ε : ℝ)) * lam / 2) :=
    lt_min (by norm_num) hsuper
  have hminUpper : min 2 ((1 - (ε : ℝ)) * lam / 2) ≤ 2 :=
    min_le_left _ _
  unfold appendixCanonicalScanFactor
  constructor <;> linarith

theorem appendixCanonicalScanFactor_lt_density
    (ε : NoiseRate) (lam : ℝ)
    (hsuper : 1 < (1 - (ε : ℝ)) * lam / 2) :
    appendixCanonicalScanFactor ε lam <
      (1 - (ε : ℝ)) * lam / 2 := by
  let a : ℝ := (1 - (ε : ℝ)) * lam / 2
  by_cases ha : a ≤ 2
  · rw [appendixCanonicalScanFactor, min_eq_right ha]
    dsimp only [a] at hsuper ⊢
    linarith
  · have htwo : 2 ≤ a := le_of_not_ge ha
    rw [appendixCanonicalScanFactor, min_eq_left htwo]
    dsimp only [a] at htwo ⊢
    linarith

/-- Threshold-free form matching the statistical assertion of Theorem A.1.
The paper's condition `λ > 2/(1-ε)` supplies the canonical scan threshold
internally. -/
theorem appendix_statisticalDistinguishability_of_supercritical
    (ε : NoiseRate) (c lam r gamma : ℝ)
    (hc : 0 < c) (hlam : 0 < lam)
    (hsuper : 2 / (1 - (ε : ℝ)) < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (appendixPlantSize r n : ℝ) /
        Real.log (n : ℝ))
    (hgrowth : Vanishes fun n ↦
      (((appendixCycleCutoff n + 1 : ℕ) : ℝ) ^ 2 *
          (max 1 lam) ^ (appendixCycleCutoff n)) /
        (appendixPlantSize r n : ℝ)) :
    TendsToOne fun n ↦
      (appendixNoisedAlternativeLaw ε c lam r gamma hr n).tv
        (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n)) := by
  have hretention : 0 < 1 - (ε : ℝ) := sub_pos.mpr ε.2.2
  have hproduct : 2 < (1 - (ε : ℝ)) * lam := by
    have h := (div_lt_iff₀ hretention).mp hsuper
    simpa only [mul_comm] using h
  have hdensity : 1 < (1 - (ε : ℝ)) * lam / 2 := by linarith
  exact appendix_statisticalDistinguishability ε c lam r gamma
    (appendixCanonicalScanFactor ε lam) hc hlam hr hgamma
    (appendixCanonicalScanFactor_mem_Ioo ε lam hdensity)
    (appendixCanonicalScanFactor_lt_density ε lam hdensity)
    hpowerScale hgrowth

end

end LowDegree
