import LowDegree.Probability.BernoulliEvents
import LowDegree.Probability.BernoulliCount
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Local sparsity of a sparse Erdős--Rényi graph

This file formalizes the finite union bound and the two-range estimate in
paper Lemma A.2.  A bad configuration contains a vertex set `U` together
with a prescribed collection of too many present edges supported on `U`.
The witness formulation makes both levels of the union bound explicit.
-/

namespace LowDegree

open Filter Topology

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The inclusion of a finite vertex subset maps its complete graph into the
ambient complete graph. -/
def completeSubsetCopy {m : ℕ} (U : Finset (Fin m)) :
    (⊤ : SimpleGraph U).Copy (⊤ : SimpleGraph (Fin m)) where
  toHom :=
    { toFun := fun u ↦ u.1
      map_rel' := fun h ↦
        (SimpleGraph.top_adj _ _).2 (Subtype.val_injective.ne h.ne) }
  injective' := Subtype.val_injective

/-- Ambient edge coordinates whose two endpoints lie in `U`. -/
noncomputable def ambientEdgesOn {m : ℕ} (U : Finset (Fin m)) :
    Finset (AmbientEdge m) :=
  (Finset.univ : Finset (⊤ : SimpleGraph U).edgeSet).map
    (completeSubsetCopy U).mapEdgeSet

@[simp]
theorem card_ambientEdgesOn {m : ℕ} (U : Finset (Fin m)) :
    (ambientEdgesOn U).card = U.card.choose 2 := by
  rw [ambientEdgesOn, Finset.card_map, Finset.card_univ,
    ← SimpleGraph.edgeFinset_card]
  simpa using
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := U))

/-- Number of present edges with both endpoints in `U`. -/
noncomputable def localEdgeCount {m : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) (U : Finset (Fin m)) : ℕ :=
  ((ambientEdgesOn U).filter fun e ↦ x e = true).card

/-- Vertex subsets of a prescribed cardinality. -/
noncomputable def vertexSubsets (m s : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powersetCard s

@[simp]
theorem card_vertexSubsets (m s : ℕ) :
    (vertexSubsets m s).card = m.choose s := by
  simp [vertexSubsets]

/-- At a fixed vertex-set size `s`, the bad event is witnessed by a set of
`k` ambient edges supported on those vertices, every one of which is present.
This remains meaningful when `k > s.choose 2`, in which case it is empty. -/
noncomputable def localBadEventAtSize (m s k : ℕ) :
    Finset (BooleanConfiguration (AmbientEdge m)) :=
  (vertexSubsets m s).biUnion fun U ↦
    ((ambientEdgesOn U).powersetCard k).biUnion allPresentEvent

theorem mem_localBadEventAtSize_iff {m s k : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) :
    x ∈ localBadEventAtSize m s k ↔
      ∃ U : Finset (Fin m), U.card = s ∧ k ≤ localEdgeCount x U := by
  classical
  constructor
  · intro hx
    rw [localBadEventAtSize, Finset.mem_biUnion] at hx
    rcases hx with ⟨U, hU, hx⟩
    rw [vertexSubsets, Finset.mem_powersetCard] at hU
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨A, hA, hx⟩
    rw [Finset.mem_powersetCard] at hA
    refine ⟨U, hU.2, ?_⟩
    rw [← hA.2]
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter]
    exact ⟨hA.1 he, (mem_allPresentEvent A x).mp hx e he⟩
  · rintro ⟨U, hUcard, hk⟩
    let present : Finset (AmbientEdge m) :=
      (ambientEdgesOn U).filter fun e ↦ x e = true
    obtain ⟨A, hApresent, hAcard⟩ :=
      Finset.exists_subset_card_eq (s := present) hk
    rw [localBadEventAtSize, Finset.mem_biUnion]
    refine ⟨U, ?_, ?_⟩
    · rw [vertexSubsets, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ U, hUcard⟩
    · rw [Finset.mem_biUnion]
      refine ⟨A, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, hAcard⟩
        intro e he
        exact (Finset.mem_filter.mp (hApresent he)).1
      · rw [mem_allPresentEvent]
        intro e he
        exact (Finset.mem_filter.mp (hApresent he)).2

namespace FiniteLaw

/-- Union bound over a specified finite index set. -/
theorem prob_finset_biUnion_le {Ω I : Type*} [Fintype Ω]
    [DecidableEq Ω] [DecidableEq I]
    (q : FiniteLaw Ω)
    (s : Finset I) (event : I → Finset Ω) :
    q.prob (s.biUnion event) ≤ ∑ i ∈ s, q.prob (event i) := by
  induction s using Finset.induction_on with
  | empty => simp [FiniteLaw.prob]
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hunion :
          q.prob (event i ∪ s.biUnion event) ≤
            q.prob (event i) + q.prob (s.biUnion event) := by
        have hidentity := Finset.sum_union_inter
          (s₁ := event i) (s₂ := s.biUnion event) (f := q.mass)
        have hinter : 0 ≤ ∑ ω ∈ event i ∩ s.biUnion event, q.mass ω :=
          Finset.sum_nonneg fun ω _ ↦ q.mass_nonneg ω
        unfold FiniteLaw.prob
        linarith
      exact hunion.trans (add_le_add_left ih _)

/-- Probability of a finite complement. -/
theorem prob_univ_sdiff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (q : FiniteLaw Ω) (s : Finset Ω) :
    q.prob (Finset.univ \ s) = 1 - q.prob s := by
  have hsplit := s.sum_add_sum_compl q.mass
  unfold FiniteLaw.prob
  simp only [Finset.compl_eq_univ_sdiff] at hsplit
  rw [q.sum_mass] at hsplit
  linarith

end FiniteLaw

/-- Exact finite subset/edge-collection union bound from paper Lemma A.2. -/
theorem bernoulliProductLaw_prob_localBadEventAtSize_le
    (θ : BernoulliParameter) (m s k : ℕ) :
    (bernoulliProductLaw θ).prob (localBadEventAtSize m s k) ≤
      (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) * θ.p ^ k := by
  classical
  unfold localBadEventAtSize
  calc
    (bernoulliProductLaw θ).prob
        ((vertexSubsets m s).biUnion fun U ↦
          ((ambientEdgesOn U).powersetCard k).biUnion allPresentEvent) ≤
        ∑ U ∈ vertexSubsets m s,
          (bernoulliProductLaw θ).prob
            (((ambientEdgesOn U).powersetCard k).biUnion allPresentEvent) :=
      FiniteLaw.prob_finset_biUnion_le
        (q := bernoulliProductLaw θ) (s := vertexSubsets m s)
        (event := fun U ↦
          ((ambientEdgesOn U).powersetCard k).biUnion allPresentEvent)
    _ ≤ ∑ U ∈ vertexSubsets m s,
        ∑ A ∈ (ambientEdgesOn U).powersetCard k, θ.p ^ A.card := by
      apply Finset.sum_le_sum
      intro U _hU
      calc
        _ ≤ ∑ A ∈ (ambientEdgesOn U).powersetCard k,
            (bernoulliProductLaw θ).prob (allPresentEvent A) :=
          FiniteLaw.prob_finset_biUnion_le
            (q := bernoulliProductLaw θ)
            (s := (ambientEdgesOn U).powersetCard k)
            (event := allPresentEvent)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro A _hA
          exact bernoulliProductLaw_prob_allPresent θ A
    _ = (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) * θ.p ^ k := by
      calc
        (∑ U ∈ vertexSubsets m s,
            ∑ A ∈ (ambientEdgesOn U).powersetCard k, θ.p ^ A.card) =
            ∑ _U ∈ vertexSubsets m s,
              ((s.choose 2).choose k : ℝ) * θ.p ^ k := by
          apply Finset.sum_congr rfl
          intro U hU
          have hUcard : U.card = s :=
            (Finset.mem_powersetCard.mp hU).2
          calc
            (∑ A ∈ (ambientEdgesOn U).powersetCard k, θ.p ^ A.card) =
                ∑ _A ∈ (ambientEdgesOn U).powersetCard k, θ.p ^ k := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [(Finset.mem_powersetCard.mp hA).2]
            _ = ((s.choose 2).choose k : ℝ) * θ.p ^ k := by
              rw [Finset.sum_const, nsmul_eq_mul,
                Finset.card_powersetCard, card_ambientEdgesOn, hUcard]
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, card_vertexSubsets]
          ring

/-- First forbidden edge count for the manuscript threshold
`(1 + A / log n) s`. -/
noncomputable def localSparsityThreshold (n : ℕ) (A : ℝ) (s : ℕ) : ℕ :=
  ⌊(1 + A / Real.log (n : ℝ)) * (s : ℝ)⌋₊ + 1

theorem localSparsityThreshold_gt
    {n s : ℕ} {A : ℝ} (hslack : 0 ≤ A / Real.log (n : ℝ)) :
    s < localSparsityThreshold n A s := by
  unfold localSparsityThreshold
  have hfloor : s ≤
      ⌊(1 + A / Real.log (n : ℝ)) * (s : ℝ)⌋₊ := by
    apply Nat.le_floor
    exact le_mul_of_one_le_left (Nat.cast_nonneg s) (by linarith)
  omega

theorem localSparsityThreshold_le_three_mul
    {n s : ℕ} {A : ℝ} (hs : 1 ≤ s)
    (hslack0 : 0 ≤ A / Real.log (n : ℝ))
    (hslack1 : A / Real.log (n : ℝ) ≤ 1) :
    localSparsityThreshold n A s ≤ 3 * s := by
  unfold localSparsityThreshold
  let t : ℝ := (1 + A / Real.log (n : ℝ)) * (s : ℝ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht2s : t ≤ 2 * (s : ℝ) := by
    dsimp [t]
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg s)
  have hfloorReal : (⌊t⌋₊ : ℝ) ≤ 2 * (s : ℝ) :=
    (Nat.floor_le ht0).trans ht2s
  have hfloor : ⌊t⌋₊ ≤ 2 * s := by exact_mod_cast hfloorReal
  dsimp [t] at hfloor
  omega

theorem slack_mul_lt_threshold_sub
    {n s : ℕ} {A : ℝ} (hslack : 0 ≤ A / Real.log (n : ℝ)) :
    A / Real.log (n : ℝ) * (s : ℝ) <
      (localSparsityThreshold n A s - s : ℕ) := by
  have hsk : s ≤ localSparsityThreshold n A s :=
    (localSparsityThreshold_gt hslack).le
  rw [Nat.cast_sub hsk]
  unfold localSparsityThreshold
  have hlt := Nat.lt_floor_add_one
    ((1 + A / Real.log (n : ℝ)) * (s : ℝ))
  push_cast at hlt ⊢
  linarith

/-- Standard exponential binomial-coefficient estimate
`choose n k ≤ (e n / k)^k`, derived from Mathlib's exact factorial bound
and Stirling's lower estimate. -/
theorem natChoose_cast_le_exp_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.two_le_pi, show (1 : ℝ) ≤ k by exact_mod_cast hk]
  have hbase_nonneg : 0 ≤ (k : ℝ) / Real.exp 1 := by positivity
  have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * (k : ℝ)) *
            ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (pow_nonneg hbase_nonneg k) hsqrt
      _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) :=
      Nat.choose_le_pow_div k n
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      gcongr
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      rw [div_pow, div_pow, mul_pow]
      field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne']

/-- The second binomial factor in the local union bound has the manuscript
base `e s / 2` once the forbidden edge count is at least `s`. -/
theorem choose_chooseTwo_cast_le_exp_mul_half_pow
    (s k : ℕ) (hs : 0 < s) (hsk : s ≤ k) :
    ((s.choose 2).choose k : ℝ) ≤
      (Real.exp 1 * (s : ℝ) / 2) ^ k := by
  have hk : 0 < k := hs.trans_le hsk
  refine (natChoose_cast_le_exp_mul_div_pow (s.choose 2) k hk).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hkreal).2
  have hchooseTwo : (s.choose 2 : ℝ) ≤ (s : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by linarith : (s : ℝ) - 1 ≤ s)
      (Nat.cast_nonneg s)
  calc
    Real.exp 1 * (s.choose 2 : ℝ) ≤
        Real.exp 1 * ((s : ℝ) ^ 2 / 2) := by gcongr
    _ ≤ (Real.exp 1 * (s : ℝ) / 2) * (k : ℝ) := by
      have hskreal : (s : ℝ) ≤ k := by exact_mod_cast hsk
      calc
        Real.exp 1 * ((s : ℝ) ^ 2 / 2) =
            (Real.exp 1 * (s : ℝ) / 2) * (s : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hskreal (by positivity)

/-- Algebraic normalization of the two binomial estimates and the sparse
edge probability. -/
theorem localUnionFactor_identity
    {lam : ℝ} {m s k : ℕ} (hm : 0 < m) (hs : 0 < s) (hsk : s ≤ k) :
    (Real.exp 1 * (m : ℝ) / (s : ℝ)) ^ s *
        (Real.exp 1 * (s : ℝ) / 2) ^ k *
          (lam / (m : ℝ)) ^ k =
      (Real.exp 1) ^ s * (Real.exp 1 * lam / 2) ^ k *
        ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [pow_sub₀ _ (div_ne_zero hs0 hm0) hsk]
  field_simp [hm0, hs0]
  simp only [div_pow, mul_pow]
  field_simp [hm0, hs0]

/-- Constant `B(λ)>1` absorbing all factors that are exponential in the
vertex-set size in the manuscript union bound. -/
noncomputable def localSparsityBase (lam : ℝ) : ℝ :=
  Real.exp 1 * (max 1 (Real.exp 1 * lam / 2)) ^ 3

theorem one_lt_localSparsityBase (lam : ℝ) :
    1 < localSparsityBase lam := by
  have hexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num))
  have hfactor : 1 ≤ (max 1 (Real.exp 1 * lam / 2)) ^ 3 := by
    exact one_le_pow₀ (le_max_left _ _)
  exact hexp.trans_le <| by
    unfold localSparsityBase
    exact le_mul_of_one_le_right (Real.exp_pos 1).le hfactor

/-- The fixed-size failure term is bounded by the manuscript expression
`B^s (s/m)^(k-s)` whenever `s ≤ k ≤ 3s`. -/
theorem localUnionTerm_le_base_mul_ratio_pow
    {lam : ℝ} (hlam : 0 ≤ lam) {m s k : ℕ}
    (hm : 0 < m) (hs : 0 < s) (hsk : s ≤ k) (hks : k ≤ 3 * s)
    (θ : BernoulliParameter) (hp : θ.p = lam / (m : ℝ)) :
    (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) * θ.p ^ k ≤
      (localSparsityBase lam) ^ s *
        ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
  have hk : 0 < k := hs.trans_le hsk
  have hchooseVertices := natChoose_cast_le_exp_mul_div_pow m s hs
  have hchooseEdges :=
    choose_chooseTwo_cast_le_exp_mul_half_pow s k hs hsk
  have hprob_nonneg : 0 ≤ θ.p ^ k := pow_nonneg θ.p_pos.le k
  calc
    (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) * θ.p ^ k ≤
        (Real.exp 1 * (m : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * (s : ℝ) / 2) ^ k * θ.p ^ k := by
      gcongr
    _ = (Real.exp 1) ^ s * (Real.exp 1 * lam / 2) ^ k *
          ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
      rw [hp]
      exact localUnionFactor_identity hm hs hsk
    _ ≤ (localSparsityBase lam) ^ s *
          ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      let L : ℝ := max 1 (Real.exp 1 * lam / 2)
      have hL_one : 1 ≤ L := le_max_left _ _
      have hL_nonneg : 0 ≤ L := zero_le_one.trans hL_one
      have hC_nonneg : 0 ≤ Real.exp 1 * lam / 2 := by positivity
      have hC_le : Real.exp 1 * lam / 2 ≤ L := le_max_right _ _
      calc
        (Real.exp 1) ^ s * (Real.exp 1 * lam / 2) ^ k ≤
            (Real.exp 1) ^ s * L ^ k := by gcongr
        _ ≤ (Real.exp 1) ^ s * L ^ (3 * s) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hL_one hks) (pow_nonneg (Real.exp_pos 1).le s)
        _ = (localSparsityBase lam) ^ s := by
          unfold localSparsityBase
          dsimp [L]
          rw [mul_pow, pow_mul]

/-- A logarithmic number of summands, each of order at most `m⁻¹/²`,
has vanishing total mass.  This is the deterministic limit used in the
small-set range of Lemma A.2. -/
theorem logAffineSq_div_sqrt_vanishes
    (a : ℝ) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (a * Real.log (m n : ℝ) + 1) ^ 2 / Real.sqrt (m n : ℝ) := by
  have h2raw :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_half_pos).tendsto_div_nhds_zero
  have h2 : Tendsto
      (fun x : ℝ ↦ Real.log x ^ 2 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h2raw
  have h1raw :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) one_half_pos).tendsto_div_nhds_zero
  have h1 : Tendsto
      (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Real.sqrt_eq_rpow] using h1raw
  have hsqrtTop : Tendsto (fun x : ℝ ↦ Real.sqrt x) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop one_half_pos)
  have h0 : Tendsto (fun x : ℝ ↦ 1 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hsqrtTop
  have ha2 : Tendsto
      (fun x : ℝ ↦ a ^ 2 * (Real.log x ^ 2 / Real.sqrt x))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h2 : Tendsto
        (fun x : ℝ ↦ a ^ 2 * (Real.log x ^ 2 / Real.sqrt x))
        atTop (𝓝 ((a ^ 2) * 0)))
  have ha1 : Tendsto
      (fun x : ℝ ↦ (2 * a) * (Real.log x / Real.sqrt x))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul h1 : Tendsto
        (fun x : ℝ ↦ (2 * a) * (Real.log x / Real.sqrt x))
        atTop (𝓝 ((2 * a) * 0)))
  have hcombined : Tendsto
      (fun x : ℝ ↦
        a ^ 2 * (Real.log x ^ 2 / Real.sqrt x) +
          (2 * a) * (Real.log x / Real.sqrt x) +
            1 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [zero_add, add_assoc] using ha2.add (ha1.add h0)
  have htarget : Tendsto
      (fun x : ℝ ↦ (a * Real.log x + 1) ^ 2 / Real.sqrt x)
      atTop (𝓝 0) := by
    apply hcombined.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [Real.sqrt_pos.2 hx]
    ring
  exact htarget.comp (tendsto_natCast_atTop_atTop.comp hm)

/-- The logarithmic split constant `a` in the manuscript. -/
noncomputable def localSparsityLogWindow (lam : ℝ) : ℝ :=
  1 / (2 * Real.log (localSparsityBase lam))

theorem localSparsityLogWindow_pos (lam : ℝ) :
    0 < localSparsityLogWindow lam := by
  unfold localSparsityLogWindow
  exact one_div_pos.mpr <| mul_pos (by norm_num)
    (Real.log_pos (one_lt_localSparsityBase lam))

/-- The manuscript condition `s ≤ m^γ` implies the logarithmic gap used
in the large-set estimate. -/
theorem log_div_le_neg_one_sub_mul_log_of_le_rpow
    {m s : ℝ} {gamma : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hsm : s ≤ m ^ gamma) :
    Real.log (s / m) ≤ -(1 - gamma) * Real.log m := by
  have hlog : Real.log s ≤ Real.log (m ^ gamma) :=
    Real.log_le_log hs hsm
  rw [Real.log_rpow hm] at hlog
  rw [Real.log_div hs.ne' hm.ne']
  linarith

/-- Within the logarithmic range, the exponential factor `B^s` is at
most `√m`. -/
theorem localSparsityBase_pow_le_sqrt
    (lam : ℝ) {m s : ℕ} (hm : 0 < m)
    (hs : (s : ℝ) ≤
      localSparsityLogWindow lam * Real.log (m : ℝ)) :
    localSparsityBase lam ^ s ≤ Real.sqrt (m : ℝ) := by
  let B := localSparsityBase lam
  have hB_one : 1 < B := one_lt_localSparsityBase lam
  have hB : 0 < B := zero_lt_one.trans hB_one
  have hlogB : 0 < Real.log B := Real.log_pos hB_one
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.rpow_natCast]
  rw [Real.rpow_le_iff_le_log hB (Real.sqrt_pos.2 hmreal),
    Real.log_sqrt hmreal.le]
  calc
    (s : ℝ) * Real.log B ≤
        (localSparsityLogWindow lam * Real.log (m : ℝ)) * Real.log B := by
      gcongr
    _ = Real.log (m : ℝ) / 2 := by
      unfold localSparsityLogWindow
      dsimp [B] at hlogB ⊢
      field_simp [hlogB.ne']

theorem pow_le_self_of_unitInterval
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    x ^ d ≤ x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [pow_add, pow_one]
  exact mul_le_of_le_one_right hx0 (pow_le_one₀ hx0 hx1)

/-- Convert a logarithmic exponent estimate into the needed product bound. -/
theorem base_mul_ratio_pow_le_exp_neg
    {B ratio : ℝ} (hB : 0 < B) (hratio : 0 < ratio)
    (s d : ℕ)
    (hlog : (s : ℝ) * Real.log B +
      (d : ℝ) * Real.log ratio ≤ -(s : ℝ)) :
    B ^ s * ratio ^ d ≤ Real.exp (-(s : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hratio,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using hlog

theorem exp_neg_natCast_le_half_pow (s : ℕ) :
    Real.exp (-(s : ℝ)) ≤ ((1 : ℝ) / 2) ^ s := by
  have hehalf : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    nlinarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  rw [show -(s : ℝ) = (s : ℝ) * (-1) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos (-1)).le hehalf s

/-- Explicit choice of the manuscript constant `A=A(λ,r,γ)`. -/
noncomputable def localSparsitySlackConstant
    (lam r gamma : ℝ) : ℝ :=
  2 * (Real.log (localSparsityBase lam) + 1) /
    (r * (1 - gamma))

theorem localSparsitySlackConstant_pos
    (lam : ℝ) {r gamma : ℝ} (hr : 0 < r) (hgamma : gamma < 1) :
    0 < localSparsitySlackConstant lam r gamma := by
  unfold localSparsitySlackConstant
  have hlog : 0 < Real.log (localSparsityBase lam) :=
    Real.log_pos (one_lt_localSparsityBase lam)
  exact div_pos (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hlog zero_le_one))
    (mul_pos hr (sub_pos.mpr hgamma))

/-- The manuscript cutoff `⌊m^γ⌋`. -/
noncomputable def localSparsityPowerCutoff (m : ℕ) (gamma : ℝ) : ℕ :=
  ⌊(m : ℝ) ^ gamma⌋₊

theorem localSparsityPowerCutoff_le
    {m : ℕ} {gamma : ℝ} (hm : 0 < m) (hgamma : gamma ≤ 1) :
    localSparsityPowerCutoff m gamma ≤ m := by
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfloor :
      (localSparsityPowerCutoff m gamma : ℝ) ≤ (m : ℝ) ^ gamma := by
    unfold localSparsityPowerCutoff
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) gamma)
  have hrpow : (m : ℝ) ^ gamma ≤ (m : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmOne hgamma
  exact_mod_cast hfloor.trans hrpow

theorem localSparsityPowerCutoff_log_gap
    {m s : ℕ} {gamma : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hscutoff : s ≤ localSparsityPowerCutoff m gamma) :
    Real.log ((s : ℝ) / (m : ℝ)) ≤
      -(1 - gamma) * Real.log (m : ℝ) := by
  apply log_div_le_neg_one_sub_mul_log_of_le_rpow
  · exact_mod_cast hm
  · exact_mod_cast hs
  · exact (Nat.cast_le.mpr hscutoff).trans <| by
      unfold localSparsityPowerCutoff
      exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) gamma)

/-- The logarithmic splitting point used in the two-range union bound. -/
noncomputable def localSparsityLogSplit (lam : ℝ) (m : ℕ) : ℕ :=
  ⌊localSparsityLogWindow lam * Real.log (m : ℝ)⌋₊

theorem localSparsityLogSplit_cast_le (lam : ℝ) (m : ℕ) :
    (localSparsityLogSplit lam m : ℝ) ≤
      localSparsityLogWindow lam * Real.log (m : ℝ) := by
  unfold localSparsityLogSplit
  exact Nat.floor_le <| mul_nonneg
    (localSparsityLogWindow_pos lam).le (Real.log_natCast_nonneg m)

theorem localSparsityLogSplit_tendsto_atTop
    (lam : ℝ) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n ↦ localSparsityLogSplit lam (m n)) atTop atTop := by
  unfold localSparsityLogSplit
  apply tendsto_nat_floor_atTop.comp
  apply Tendsto.const_mul_atTop (localSparsityLogWindow_pos lam)
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hm)

/-- Failure of local sparsity: some set of between two and `cutoff`
vertices supports at least the first forbidden number of present edges. -/
noncomputable def localSparsityFailureEvent
    (n m cutoff : ℕ) (A : ℝ) :
    Finset (BooleanConfiguration (AmbientEdge m)) :=
  (Finset.Icc 2 cutoff).biUnion fun s ↦
    localBadEventAtSize m s (localSparsityThreshold n A s)

/-- The actual local-sparsity event used in paper Lemma A.2. -/
noncomputable def localSparsityEvent
    (n m cutoff : ℕ) (A : ℝ) :
    Finset (BooleanConfiguration (AmbientEdge m)) :=
  Finset.univ \ localSparsityFailureEvent n m cutoff A

theorem mem_localSparsityFailureEvent_iff
    {n m cutoff : ℕ} {A : ℝ}
    (x : BooleanConfiguration (AmbientEdge m)) :
    x ∈ localSparsityFailureEvent n m cutoff A ↔
      ∃ U : Finset (Fin m),
        2 ≤ U.card ∧ U.card ≤ cutoff ∧
          localSparsityThreshold n A U.card ≤ localEdgeCount x U := by
  classical
  constructor
  · intro hx
    rw [localSparsityFailureEvent, Finset.mem_biUnion] at hx
    rcases hx with ⟨s, hs, hx⟩
    rcases (mem_localBadEventAtSize_iff x).mp hx with ⟨U, hU, hk⟩
    refine ⟨U, ?_, ?_, ?_⟩
    · simpa [hU] using (Finset.mem_Icc.mp hs).1
    · simpa [hU] using (Finset.mem_Icc.mp hs).2
    · simpa [hU] using hk
  · rintro ⟨U, hU2, hUcutoff, hk⟩
    rw [localSparsityFailureEvent, Finset.mem_biUnion]
    refine ⟨U.card, Finset.mem_Icc.mpr ⟨hU2, hUcutoff⟩, ?_⟩
    exact (mem_localBadEventAtSize_iff x).mpr ⟨U, rfl, hk⟩

theorem mem_localSparsityEvent_iff
    {n m cutoff : ℕ} {A : ℝ}
    (x : BooleanConfiguration (AmbientEdge m)) :
    x ∈ localSparsityEvent n m cutoff A ↔
      ∀ U : Finset (Fin m),
        2 ≤ U.card → U.card ≤ cutoff →
          localEdgeCount x U < localSparsityThreshold n A U.card := by
  classical
  simp only [localSparsityEvent, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [not_congr (mem_localSparsityFailureEvent_iff x)]
  push_neg
  rfl

/-- With nonnegative slack, the integer threshold is exactly the paper's
real-valued local-density inequality. -/
theorem mem_localSparsityEvent_iff_real
    {n m cutoff : ℕ} {A : ℝ}
    (hslack : 0 ≤ A / Real.log (n : ℝ))
    (x : BooleanConfiguration (AmbientEdge m)) :
    x ∈ localSparsityEvent n m cutoff A ↔
      ∀ U : Finset (Fin m),
        2 ≤ U.card → U.card ≤ cutoff →
          (localEdgeCount x U : ℝ) ≤
            (1 + A / Real.log (n : ℝ)) * (U.card : ℝ) := by
  rw [mem_localSparsityEvent_iff]
  apply forall_congr'
  intro U
  apply imp_congr_right
  intro _hU2
  apply imp_congr_right
  intro _hUcutoff
  rw [localSparsityThreshold, Nat.lt_add_one_iff,
    Nat.le_floor_iff]
  positivity

/-- Union bound over all admissible vertex-set sizes, before any
asymptotic estimates are applied. -/
theorem bernoulliProductLaw_prob_localSparsityFailureEvent_le
    (θ : BernoulliParameter) (n m cutoff : ℕ) (A : ℝ) :
    (bernoulliProductLaw θ).prob
        (localSparsityFailureEvent n m cutoff A) ≤
      ∑ s ∈ Finset.Icc 2 cutoff,
        (m.choose s : ℝ) *
          ((s.choose 2).choose (localSparsityThreshold n A s) : ℝ) *
            θ.p ^ (localSparsityThreshold n A s) := by
  classical
  unfold localSparsityFailureEvent
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 cutoff,
        (bernoulliProductLaw θ).prob
          (localBadEventAtSize m s (localSparsityThreshold n A s)) :=
      FiniteLaw.prob_finset_biUnion_le
        (q := bernoulliProductLaw θ) (s := Finset.Icc 2 cutoff)
        (event := fun s ↦
          localBadEventAtSize m s (localSparsityThreshold n A s))
    _ ≤ _ := Finset.sum_le_sum fun s _hs ↦
      bernoulliProductLaw_prob_localBadEventAtSize_le θ m s
        (localSparsityThreshold n A s)

/-- Fixed-`n` form of the two-range estimate in paper Lemma A.2.  The
small sets have `s ≤ a log m`, while the remaining sizes are controlled by
the `m^γ` logarithmic gap. -/
theorem bernoulliProductLaw_prob_localSparsityFailureEvent_le_twoRange
    (lam r gamma : ℝ) (hlam : 0 ≤ lam) (hr : 0 < r)
    (hgamma : gamma < 1) (n m cutoff split : ℕ)
    (hn : 1 < n) (hm : 0 < m) (hcutoffm : cutoff ≤ m)
    (hsplitLog : (split : ℝ) ≤
      localSparsityLogWindow lam * Real.log (m : ℝ))
    (hcutoffLog : ∀ s ∈ Finset.Icc 2 cutoff,
      Real.log ((s : ℝ) / (m : ℝ)) ≤
        -(1 - gamma) * Real.log (m : ℝ))
    (hlogRatio : r / 2 ≤
      Real.log (m : ℝ) / Real.log (n : ℝ))
    (hslackOne : localSparsitySlackConstant lam r gamma /
      Real.log (n : ℝ) ≤ 1)
    (θ : BernoulliParameter)
    (hp : θ.p = lam / (m : ℝ)) :
    (bernoulliProductLaw θ).prob
        (localSparsityFailureEvent n m cutoff
          (localSparsitySlackConstant lam r gamma)) ≤
      ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) +
        2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
  classical
  let A := localSparsitySlackConstant lam r gamma
  let B := localSparsityBase lam
  let sizes := Finset.Icc 2 cutoff
  let term : ℕ → ℝ := fun s ↦
    (m.choose s : ℝ) *
      ((s.choose 2).choose (localSparsityThreshold n A s) : ℝ) *
        θ.p ^ (localSparsityThreshold n A s)
  let small := sizes.filter fun s ↦ s ≤ split
  let large := sizes.filter fun s ↦ ¬s ≤ split
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hApos : 0 < A := localSparsitySlackConstant_pos lam hr hgamma
  have hdelta0 : 0 ≤ A / Real.log (n : ℝ) :=
    (div_pos hApos hlogn).le
  have hBpos : 0 < B :=
    zero_lt_one.trans (one_lt_localSparsityBase lam)
  have hpenalty : Real.log B + 1 ≤
      A * (1 - gamma) *
        (Real.log (m : ℝ) / Real.log (n : ℝ)) := by
    calc
      Real.log B + 1 = A * (1 - gamma) * (r / 2) := by
        dsimp [A, B, localSparsitySlackConstant]
        field_simp [hr.ne', (sub_pos.mpr hgamma).ne']
      _ ≤ A * (1 - gamma) *
          (Real.log (m : ℝ) / Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogRatio
          (mul_nonneg hApos.le (sub_pos.mpr hgamma).le)
  have hterm (s : ℕ) (hsizes : s ∈ sizes) :
      term s ≤ B ^ s *
        ((s : ℝ) / (m : ℝ)) ^
          (localSparsityThreshold n A s - s) := by
    have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hsizes).1
    have hkLower : s ≤ localSparsityThreshold n A s :=
      (localSparsityThreshold_gt hdelta0).le
    have hkUpper : localSparsityThreshold n A s ≤ 3 * s :=
      localSparsityThreshold_le_three_mul (by omega) hdelta0 hslackOne
    exact localUnionTerm_le_base_mul_ratio_pow hlam hm (by omega)
      hkLower hkUpper θ hp
  have hsmallTerm (s : ℕ) (hs : s ∈ small) :
      term s ≤ (split + 1 : ℝ) / Real.sqrt (m : ℝ) := by
    have hsizes : s ∈ sizes := (Finset.mem_filter.mp hs).1
    have hssplit : s ≤ split := (Finset.mem_filter.mp hs).2
    have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hsizes).1
    have hsm : s ≤ m :=
      (Finset.mem_Icc.mp hsizes).2.trans hcutoffm
    have hratio0 : 0 ≤ (s : ℝ) / (m : ℝ) := by positivity
    have hratio1 : (s : ℝ) / (m : ℝ) ≤ 1 := by
      exact (div_le_one hmreal).2 (by exact_mod_cast hsm)
    have hd : 1 ≤ localSparsityThreshold n A s - s := by
      have hkgt : s < localSparsityThreshold n A s :=
        localSparsityThreshold_gt hdelta0
      omega
    have hpowRatio :
        ((s : ℝ) / (m : ℝ)) ^
            (localSparsityThreshold n A s - s) ≤
          (s : ℝ) / (m : ℝ) :=
      pow_le_self_of_unitInterval hratio0 hratio1 hd
    have hpowBase : B ^ s ≤ Real.sqrt (m : ℝ) := by
      apply localSparsityBase_pow_le_sqrt lam hm
      exact (Nat.cast_le.mpr hssplit).trans hsplitLog
    calc
      term s ≤ B ^ s *
          ((s : ℝ) / (m : ℝ)) ^
            (localSparsityThreshold n A s - s) := hterm s hsizes
      _ ≤ Real.sqrt (m : ℝ) * ((s : ℝ) / (m : ℝ)) := by
        exact mul_le_mul hpowBase hpowRatio (by positivity) (Real.sqrt_nonneg _)
      _ = (s : ℝ) / Real.sqrt (m : ℝ) := by
        have hsqrt := Real.sq_sqrt hmreal.le
        field_simp [Real.sqrt_pos.2 hmreal |>.ne']
        nlinarith
      _ ≤ (split + 1 : ℝ) / Real.sqrt (m : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact_mod_cast hssplit.trans (Nat.le_succ split)
  have hsmallCard : small.card ≤ split + 1 := by
    have hsubset : small ⊆ Finset.range (split + 1) := by
      intro s hs
      rw [Finset.mem_range]
      have hssplit : s ≤ split := (Finset.mem_filter.mp hs).2
      omega
    simpa using Finset.card_le_card hsubset
  have hsmallSum : (∑ s ∈ small, term s) ≤
      ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) := by
    calc
      (∑ s ∈ small, term s) ≤
          ∑ _s ∈ small, (split + 1 : ℝ) / Real.sqrt (m : ℝ) :=
        Finset.sum_le_sum hsmallTerm
      _ = (small.card : ℝ) *
          ((split + 1 : ℝ) / Real.sqrt (m : ℝ)) := by simp
      _ ≤ (split + 1 : ℝ) *
          ((split + 1 : ℝ) / Real.sqrt (m : ℝ)) := by
        gcongr
        exact_mod_cast hsmallCard
      _ = ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) := by
        push_cast
        ring
  have hlargeTerm (s : ℕ) (hs : s ∈ large) :
      term s ≤ ((1 : ℝ) / 2) ^ s := by
    have hsizes : s ∈ sizes := (Finset.mem_filter.mp hs).1
    have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hsizes).1
    have hsm : s ≤ m :=
      (Finset.mem_Icc.mp hsizes).2.trans hcutoffm
    have hsreal : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hratio : (0 : ℝ) < (s : ℝ) / (m : ℝ) :=
      div_pos hsreal hmreal
    have hratio1 : (s : ℝ) / (m : ℝ) ≤ 1 :=
      (div_le_one hmreal).2 (by exact_mod_cast hsm)
    have hlogRatioNonpos :
        Real.log ((s : ℝ) / (m : ℝ)) ≤ 0 :=
      Real.log_nonpos hratio.le hratio1
    let d := localSparsityThreshold n A s - s
    have hdSlack : A / Real.log (n : ℝ) * (s : ℝ) < (d : ℝ) :=
      slack_mul_lt_threshold_sub hdelta0
    have hmulSlack : (d : ℝ) * Real.log ((s : ℝ) / (m : ℝ)) ≤
        (A / Real.log (n : ℝ) * (s : ℝ)) *
          Real.log ((s : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonpos_right hdSlack.le hlogRatioNonpos
    have hdeltaS0 : 0 ≤ A / Real.log (n : ℝ) * (s : ℝ) := by
      positivity
    have hmulCutoff :
        (A / Real.log (n : ℝ) * (s : ℝ)) *
            Real.log ((s : ℝ) / (m : ℝ)) ≤
          (A / Real.log (n : ℝ) * (s : ℝ)) *
            (-(1 - gamma) * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcutoffLog s hsizes) hdeltaS0
    have hpenaltyS : (Real.log B + 1) * (s : ℝ) ≤
        (A * (1 - gamma) *
          (Real.log (m : ℝ) / Real.log (n : ℝ))) * (s : ℝ) :=
      mul_le_mul_of_nonneg_right hpenalty (Nat.cast_nonneg s)
    have hlogBound :
        (s : ℝ) * Real.log B +
            (d : ℝ) * Real.log ((s : ℝ) / (m : ℝ)) ≤ -(s : ℝ) := by
      calc
        (s : ℝ) * Real.log B +
            (d : ℝ) * Real.log ((s : ℝ) / (m : ℝ)) ≤
          (s : ℝ) * Real.log B +
            (A / Real.log (n : ℝ) * (s : ℝ)) *
              Real.log ((s : ℝ) / (m : ℝ)) := add_le_add_left hmulSlack _
        _ ≤ (s : ℝ) * Real.log B +
            (A / Real.log (n : ℝ) * (s : ℝ)) *
              (-(1 - gamma) * Real.log (m : ℝ)) :=
          add_le_add_left hmulCutoff _
        _ ≤ -(s : ℝ) := by
          have heq :
              (A / Real.log (n : ℝ) * (s : ℝ)) *
                  (-(1 - gamma) * Real.log (m : ℝ)) =
                -(A * (1 - gamma) *
                    (Real.log (m : ℝ) / Real.log (n : ℝ))) * (s : ℝ) := by
            field_simp [hlogn.ne']
          rw [heq]
          nlinarith
    calc
      term s ≤ B ^ s * ((s : ℝ) / (m : ℝ)) ^ d := hterm s hsizes
      _ ≤ Real.exp (-(s : ℝ)) :=
        base_mul_ratio_pow_le_exp_neg hBpos hratio s d hlogBound
      _ ≤ ((1 : ℝ) / 2) ^ s := exp_neg_natCast_le_half_pow s
  have hlargeSum : (∑ s ∈ large, term s) ≤
      2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
    have hsummable : Summable fun i : ℕ ↦
        if split + 1 ≤ i then ((1 : ℝ) / 2) ^ i else 0 := by
      simpa only [← Set.piecewise_eq_indicator, one_div] using
        summable_geometric_two.indicator {i : ℕ | split + 1 ≤ i}
    calc
      (∑ s ∈ large, term s) ≤
          ∑ s ∈ large, ((1 : ℝ) / 2) ^ s :=
        Finset.sum_le_sum hlargeTerm
      _ = ∑ s ∈ large,
          if split + 1 ≤ s then ((1 : ℝ) / 2) ^ s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        have hslarge : ¬s ≤ split := (Finset.mem_filter.mp hs).2
        rw [if_pos (by omega)]
      _ ≤ ∑' i : ℕ,
          if split + 1 ≤ i then ((1 : ℝ) / 2) ^ i else 0 := by
        exact hsummable.sum_le_tsum large fun i _hi ↦ by
          split_ifs <;> positivity
      _ = 2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
        simpa only [one_div] using tsum_geometric_inv_two_ge (split + 1)
  calc
    (bernoulliProductLaw θ).prob
        (localSparsityFailureEvent n m cutoff A) ≤
      ∑ s ∈ sizes, term s := by
        exact bernoulliProductLaw_prob_localSparsityFailureEvent_le
          θ n m cutoff A
    _ = (∑ s ∈ small, term s) + (∑ s ∈ large, term s) := by
      dsimp [small, large]
      rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) +
        2 * (2 : ℝ)⁻¹ ^ (split + 1) := add_le_add hsmallSum hlargeSum

/-- The deterministic envelope produced by the two manuscript ranges tends
to zero for the canonical logarithmic split. -/
theorem localSparsityTwoRangeEnvelope_vanishes
    (lam : ℝ) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Vanishes fun n ↦
      (((localSparsityLogSplit lam (m n) + 1 : ℕ) : ℝ) ^ 2 /
          Real.sqrt (m n : ℝ)) +
        2 * (2 : ℝ)⁻¹ ^ (localSparsityLogSplit lam (m n) + 1) := by
  let a := localSparsityLogWindow lam
  have hsmallTarget := logAffineSq_div_sqrt_vanishes a hm
  have hmPos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  have hsmallUpper : ∀ᶠ n in atTop,
      (((localSparsityLogSplit lam (m n) + 1 : ℕ) : ℝ) ^ 2 /
          Real.sqrt (m n : ℝ)) ≤
        (a * Real.log (m n : ℝ) + 1) ^ 2 /
          Real.sqrt (m n : ℝ) := by
    filter_upwards [hmPos] with n hmn
    have hsplit := localSparsityLogSplit_cast_le lam (m n)
    have hcastAdd :
        ((localSparsityLogSplit lam (m n) + 1 : ℕ) : ℝ) ≤
          a * Real.log (m n : ℝ) + 1 := by
      dsimp [a]
      push_cast
      linarith
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact pow_le_pow_left₀ (by positivity) hcastAdd 2
  have hsmall : Vanishes fun n ↦
      (((localSparsityLogSplit lam (m n) + 1 : ℕ) : ℝ) ^ 2 /
        Real.sqrt (m n : ℝ)) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _n ↦ by positivity
    · exact hsmallUpper
    · exact hsmallTarget
  have hsplitTop :
      Tendsto (fun n ↦ localSparsityLogSplit lam (m n)) atTop atTop :=
    localSparsityLogSplit_tendsto_atTop lam hm
  have hsplitSucc :
      Tendsto (fun n ↦ localSparsityLogSplit lam (m n) + 1)
        atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hsplitTop
  have hpow : Tendsto
      (fun n ↦ (2 : ℝ)⁻¹ ^ (localSparsityLogSplit lam (m n) + 1))
      atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).comp hsplitSucc
  have htail : Vanishes fun n ↦
      2 * (2 : ℝ)⁻¹ ^ (localSparsityLogSplit lam (m n) + 1) := by
    change Tendsto _ atTop (𝓝 0)
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  exact hsmall.add htail

/-- **Local sparsity for sparse Erdős--Rényi graphs (paper Lemma A.2).**

The sequence `mₙ` is allowed to be any faithful power-scale sequence: it
diverges and eventually satisfies `log mₙ / log n ≥ r/2`.  In particular,
this is the one-sided estimate from `mₙ = ⌊n^r⌋` needed by the proof.  With
the actual cutoff `⌊mₙ^γ⌋` and the explicit constant
`A = localSparsitySlackConstant λ r γ`, the probability that some admissible
vertex set spans more than `(1 + A / log n)` edges per vertex vanishes. -/
theorem sparseErdosRenyi_localSparsityFailure_vanishes
    (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ)) :
    Vanishes fun n ↦
      (erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n))).prob
          (localSparsityFailureEvent n (m n)
            (localSparsityPowerCutoff (m n) gamma)
            (localSparsitySlackConstant lam r gamma)) := by
  let A := localSparsitySlackConstant lam r gamma
  let split : ℕ → ℕ := fun n ↦ localSparsityLogSplit lam (m n)
  let cutoff : ℕ → ℕ := fun n ↦ localSparsityPowerCutoff (m n) gamma
  let envelope : ℕ → ℝ := fun n ↦
    (((split n + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m n : ℝ)) +
      2 * (2 : ℝ)⁻¹ ^ (split n + 1)
  have hnLarge : ∀ᶠ n in atTop, 1 < n := eventually_gt_atTop 1
  have hmPos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  have hp : ∀ᶠ n in atTop,
      (sparseBernoulliParameter lam (m n)).p = lam / (m n : ℝ) :=
    hm.eventually (eventually_sparseBernoulliParameter_p_eq hlam)
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ n : ℕ in atTop, A ≤ Real.log (n : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop A)
  have hslackOne : ∀ᶠ n : ℕ in atTop,
      A / Real.log (n : ℝ) ≤ 1 := by
    filter_upwards [hnLarge, hlogLarge] with n hn hAn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_one (Real.log_pos hnReal)).2 hAn
  have hupper : ∀ᶠ n in atTop,
      (erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n))).prob
          (localSparsityFailureEvent n (m n) (cutoff n) A) ≤
        envelope n := by
    filter_upwards [hnLarge, hmPos, hp, hpowerScale, hslackOne] with
        n hn hmn hpn hratio hslack
    have hcutoffm : cutoff n ≤ m n := by
      exact localSparsityPowerCutoff_le hmn hgamma.2.le
    have hcutoffLog : ∀ s ∈ Finset.Icc 2 (cutoff n),
        Real.log ((s : ℝ) / (m n : ℝ)) ≤
          -(1 - gamma) * Real.log (m n : ℝ) := by
      intro s hs
      apply localSparsityPowerCutoff_log_gap hmn
      · have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hs).1
        omega
      · exact (Finset.mem_Icc.mp hs).2
    exact bernoulliProductLaw_prob_localSparsityFailureEvent_le_twoRange
      lam r gamma hlam.le hr.1 hgamma.2 n (m n) (cutoff n) (split n)
      hn hmn hcutoffm (localSparsityLogSplit_cast_le lam (m n))
      hcutoffLog hratio hslack (sparseBernoulliParameter lam (m n)) hpn
  have henvelope : Vanishes envelope := by
    simpa only [envelope, split] using
      localSparsityTwoRangeEnvelope_vanishes lam hm
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      (erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n))).prob_nonneg
          (localSparsityFailureEvent n (m n)
            (localSparsityPowerCutoff (m n) gamma)
            (localSparsitySlackConstant lam r gamma))
  · simpa only [cutoff, A] using hupper
  · exact henvelope

/-- Existential form of Lemma A.2: a positive constant depending only on
`λ`, `r`, and `γ` makes the local-sparsity failure probability `o(1)`. -/
theorem exists_localSparsitySlackConstant
    (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ)) :
    ∃ A : ℝ, 0 < A ∧
      Vanishes fun n ↦
        (erdosRenyiLaw (n := m n)
          (sparseBernoulliParameter lam (m n))).prob
            (localSparsityFailureEvent n (m n)
              (localSparsityPowerCutoff (m n) gamma) A) := by
  refine ⟨localSparsitySlackConstant lam r gamma,
    localSparsitySlackConstant_pos lam hr.1 hgamma.2, ?_⟩
  exact sparseErdosRenyi_localSparsityFailure_vanishes
    lam r gamma hlam hr hgamma m hm hpowerScale

/-- Probability-`1-o(1)` form of Lemma A.2 for the actual local-sparsity
event. -/
theorem sparseErdosRenyi_localSparsity_tendsToOne
    (lam r gamma : ℝ) (hlam : 0 < lam)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ)) :
    TendsToOne fun n ↦
      (erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n))).prob
          (localSparsityEvent n (m n)
            (localSparsityPowerCutoff (m n) gamma)
            (localSparsitySlackConstant lam r gamma)) := by
  have hfailure := sparseErdosRenyi_localSparsityFailure_vanishes
    lam r gamma hlam hr hgamma m hm hpowerScale
  change Tendsto _ atTop (𝓝 1)
  change Tendsto _ atTop (𝓝 0) at hfailure
  have hcomplement : Tendsto
      (fun n ↦ (1 : ℝ) -
        (erdosRenyiLaw (n := m n)
          (sparseBernoulliParameter lam (m n))).prob
            (localSparsityFailureEvent n (m n)
              (localSparsityPowerCutoff (m n) gamma)
              (localSparsitySlackConstant lam r gamma)))
      atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hfailure : Tendsto _ atTop (𝓝 ((1 : ℝ) - 0)))
  apply hcomplement.congr'
  exact Eventually.of_forall fun n ↦ by
    unfold localSparsityEvent
    simpa using (FiniteLaw.prob_univ_sdiff
      (erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n)))
      (localSparsityFailureEvent n (m n)
        (localSparsityPowerCutoff (m n) gamma)
        (localSparsitySlackConstant lam r gamma))).symm

end

end LowDegree
