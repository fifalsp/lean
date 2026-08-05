import LowDegree.Probability.BernoulliCount
import LowDegree.Probability.BernoulliEvents
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Short-cycle pruning in the sparse Erdős--Rényi plant

This file supplies the missing first-moment estimate in paper Lemma A.3.
Cycles are represented by injective labelled embeddings of `cycleGraph k`
into the complete graph.  The actual pruned edge set is the union of all
present embedded cycles of lengths between three and a cutoff `g`.
-/

namespace LowDegree

open Filter Topology

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A labelled injection of `k` cycle vertices into an ambient set of size
`m`.  Mapping `cycleGraph k` along this injection produces a (not necessarily
induced) labelled cycle in the complete ambient graph. -/
abbrev CycleEmbedding (m k : ℕ) := Fin k ↪ Fin m

/-- Regard a vertex injection as a graph copy of the cycle graph in the
complete graph. -/
def cycleEmbeddingCopy {m k : ℕ} (f : CycleEmbedding m k) :
    (SimpleGraph.cycleGraph k).Copy (⊤ : SimpleGraph (Fin m)) where
  toHom :=
    { toFun := f
      map_rel' := fun h ↦
        (SimpleGraph.top_adj _ _).2 (f.injective.ne h.ne) }
  injective' := f.injective

/-- The ambient edge coordinates used by a labelled cycle embedding. -/
noncomputable def cycleEmbeddingEdges {m k : ℕ} (f : CycleEmbedding m k) :
    Finset (AmbientEdge m) :=
  (Finset.univ : Finset (SimpleGraph.cycleGraph k).edgeSet).map
    (cycleEmbeddingCopy f).mapEdgeSet

/-- A cycle graph of length at least three has exactly that many edges. -/
theorem card_cycleGraph_edgeFinset (j : ℕ) :
    (SimpleGraph.cycleGraph (3 + j)).edgeFinset.card = 3 + j := by
  rw [Nat.add_comm 3 j]
  have hsum :=
    SimpleGraph.sum_degrees_eq_twice_card_edges
      (G := SimpleGraph.cycleGraph (j + 3))
  simp_rw [SimpleGraph.cycleGraph_degree_three_le] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hcancel : (j + 3) * 2 =
      (SimpleGraph.cycleGraph (j + 3)).edgeFinset.card * 2 := by
    simpa [Nat.mul_comm] using hsum
  exact (Nat.mul_right_cancel (by norm_num : 0 < 2) hcancel).symm

/-- Injective mapping preserves the number of cycle edges. -/
theorem card_cycleEmbeddingEdges {m k : ℕ} (hk : 3 ≤ k)
    (f : CycleEmbedding m k) :
    (cycleEmbeddingEdges f).card = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [cycleEmbeddingEdges, Finset.card_map, Finset.card_univ,
    ← SimpleGraph.edgeFinset_card]
  exact card_cycleGraph_edgeFinset j

/-- Edges contributed by one embedded cycle when every one of its coordinates
is present; otherwise it contributes nothing to the pruning union. -/
noncomputable def presentCycleEdges {m k : ℕ}
    (x : BooleanConfiguration (AmbientEdge m)) (f : CycleEmbedding m k) :
    Finset (AmbientEdge m) :=
  if x ∈ allPresentEvent (cycleEmbeddingEdges f) then
    cycleEmbeddingEdges f
  else
    ∅

/-- The concrete set of edges deleted when every present cycle of length at
most `g` is removed.  The lower cutoff excludes the degenerate cycle graphs
of sizes zero, one, and two. -/
noncomputable def shortCycleRemovedEdges (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) : Finset (AmbientEdge m) :=
  (Finset.Icc 3 g).biUnion fun k ↦
    (Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
      presentCycleEdges x f

/-- Number of edges removed by short-cycle pruning, as a real random
variable. -/
noncomputable def shortCycleRemovedCountReal (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) : ℝ :=
  ((shortCycleRemovedEdges m g x).card : ℝ)

/-- The labelled-cycle union-bound majorant.  A present labelled `k`-cycle
contributes `k`, even when its edges overlap another cycle. -/
noncomputable def embeddedShortCycleEdgeMass (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) : ℝ :=
  ∑ k ∈ Finset.Icc 3 g,
    ∑ f : CycleEmbedding m k,
      if x ∈ allPresentEvent (cycleEmbeddingEdges f) then (k : ℝ) else 0

/-- The concrete pruning count is pointwise dominated by the labelled-cycle
majorant. -/
theorem shortCycleRemovedCountReal_le_embeddedMass (m g : ℕ)
    (x : BooleanConfiguration (AmbientEdge m)) :
    shortCycleRemovedCountReal m g x ≤ embeddedShortCycleEdgeMass m g x := by
  classical
  unfold shortCycleRemovedCountReal shortCycleRemovedEdges
  have houter :
      ((Finset.Icc 3 g).biUnion fun k ↦
          (Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card ≤
        ∑ k ∈ Finset.Icc 3 g,
          ((Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card :=
    Finset.card_biUnion_le
  have hinner :
      (∑ k ∈ Finset.Icc 3 g,
          (((Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card : ℝ)) ≤
        embeddedShortCycleEdgeMass m g x := by
    unfold embeddedShortCycleEdgeMass
    apply Finset.sum_le_sum
    intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    calc
      (((Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
          presentCycleEdges x f).card : ℝ) ≤
          ∑ f : CycleEmbedding m k, ((presentCycleEdges x f).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          ((Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card ≤
              ∑ f : CycleEmbedding m k, (presentCycleEdges x f).card)
      _ = ∑ f : CycleEmbedding m k,
          if x ∈ allPresentEvent (cycleEmbeddingEdges f) then (k : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro f _hf
        by_cases hpresent : x ∈ allPresentEvent (cycleEmbeddingEdges f)
        · simp [presentCycleEdges, hpresent, card_cycleEmbeddingEdges hk3 f]
        · simp [presentCycleEdges, hpresent]
  have houter_real :
      (((Finset.Icc 3 g).biUnion fun k ↦
          (Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card : ℝ) ≤
        ∑ k ∈ Finset.Icc 3 g,
          (((Finset.univ : Finset (CycleEmbedding m k)).biUnion fun f ↦
            presentCycleEdges x f).card : ℝ) := by
    exact_mod_cast houter
  exact houter_real.trans hinner

namespace FiniteLaw

/-- Expectation commutes with a finite sum. -/
theorem expect_finset_sum {Ω I : Type*} [Fintype Ω]
    (q : FiniteLaw Ω) (s : Finset I) (f : I → Ω → ℝ) :
    q.expect (fun ω ↦ ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, q.expect (f i) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Expectation commutes with a sum over a finite type. -/
theorem expect_fintype_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (q : FiniteLaw Ω) (f : I → Ω → ℝ) :
    q.expect (fun ω ↦ ∑ i, f i ω) = ∑ i, q.expect (f i) := by
  simpa using q.expect_finset_sum (Finset.univ : Finset I) f

/-- Expectation of a constant multiple of an event indicator. -/
theorem expect_eventIndicator_const {Ω : Type*} [Fintype Ω]
    (q : FiniteLaw Ω) (event : Finset Ω) (a : ℝ) :
    q.expect (fun ω ↦ if ω ∈ event then a else 0) =
      a * q.prob event := by
  classical
  unfold FiniteLaw.expect FiniteLaw.prob
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ : Finset Ω).filter (fun ω ↦ ω ∈ event) = event := by
    ext ω
    simp
  rw [hfilter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _hω
  ring

end FiniteLaw

/-- Exact first moment of the labelled-cycle majorant.  This is the finite
calculation behind the pruning estimate: each embedding contributes `k` and
is present with probability exactly `p^k`. -/
theorem bernoulliExpectation_embeddedShortCycleEdgeMass
    (θ : BernoulliParameter) (m g : ℕ) :
    bernoulliExpectation θ (embeddedShortCycleEdgeMass m g) =
      ∑ k ∈ Finset.Icc 3 g,
        (Fintype.card (CycleEmbedding m k) : ℝ) * (k : ℝ) * θ.p ^ k := by
  let q := bernoulliProductLaw (E := AmbientEdge m) θ
  change q.expect (embeddedShortCycleEdgeMass m g) = _
  unfold embeddedShortCycleEdgeMass
  rw [q.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [q.expect_fintype_sum]
  calc
    (∑ f : CycleEmbedding m k,
        q.expect fun x ↦
          if x ∈ allPresentEvent (cycleEmbeddingEdges f) then (k : ℝ) else 0) =
        ∑ _f : CycleEmbedding m k, (k : ℝ) * θ.p ^ k := by
      apply Finset.sum_congr rfl
      intro f _hf
      have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
      calc
        q.expect (fun x ↦
            if x ∈ allPresentEvent (cycleEmbeddingEdges f) then (k : ℝ) else 0) =
            (k : ℝ) * q.prob (allPresentEvent (cycleEmbeddingEdges f)) := by
          unfold FiniteLaw.expect FiniteLaw.prob
          simp_rw [mul_ite, mul_zero]
          rw [← Finset.sum_filter]
          have hfilter :
              (Finset.univ : Finset (BooleanConfiguration (AmbientEdge m))).filter
                  (fun x ↦ x ∈ allPresentEvent (cycleEmbeddingEdges f)) =
                allPresentEvent (cycleEmbeddingEdges f) := by
            ext x
            simp
          rw [hfilter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = (k : ℝ) * θ.p ^ k := by
          rw [bernoulliProductLaw_prob_allPresent,
            card_cycleEmbeddingEdges hk3 f]
    _ = (Fintype.card (CycleEmbedding m k) : ℝ) * (k : ℝ) * θ.p ^ k := by
      simp
      ring

/-- The actual pruning count inherits the labelled-cycle first-moment
bound. -/
theorem bernoulliExpectation_shortCycleRemovedCountReal_le
    (θ : BernoulliParameter) (m g : ℕ) :
    bernoulliExpectation θ (shortCycleRemovedCountReal m g) ≤
      ∑ k ∈ Finset.Icc 3 g,
        (Fintype.card (CycleEmbedding m k) : ℝ) * (k : ℝ) * θ.p ^ k := by
  calc
    bernoulliExpectation θ (shortCycleRemovedCountReal m g) ≤
        bernoulliExpectation θ (embeddedShortCycleEdgeMass m g) := by
      unfold bernoulliExpectation
      exact Finset.sum_le_sum fun x _hx ↦
        mul_le_mul_of_nonneg_left
          (shortCycleRemovedCountReal_le_embeddedMass m g x)
          (bernoulliProductMass_nonneg θ x)
    _ = _ := bernoulliExpectation_embeddedShortCycleEdgeMass θ m g

/-- There are at most `m^k` labelled injections of `k` vertices into an
ambient set of size `m`. -/
theorem card_cycleEmbedding_le_pow (m k : ℕ) :
    Fintype.card (CycleEmbedding m k) ≤ m ^ k := by
  rw [Fintype.card_embedding_eq]
  simpa using Nat.descFactorial_le_pow m k

/-- Under the exact sparse parameter `p=λ/m`, one labelled length-`k`
contribution is bounded by `k λ^k`. -/
theorem cycleEmbedding_firstMomentTerm_le
    {lam : ℝ} (hlam : 0 ≤ lam) {m k : ℕ} (hm : 0 < m)
    (θ : BernoulliParameter) (hp : θ.p = lam / (m : ℝ)) :
    (Fintype.card (CycleEmbedding m k) : ℝ) * (k : ℝ) * θ.p ^ k ≤
      (k : ℝ) * lam ^ k := by
  have hcard : (Fintype.card (CycleEmbedding m k) : ℝ) ≤ (m : ℝ) ^ k := by
    exact_mod_cast card_cycleEmbedding_le_pow m k
  have hm_real : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hp]
  calc
    (Fintype.card (CycleEmbedding m k) : ℝ) * (k : ℝ) *
        (lam / (m : ℝ)) ^ k ≤
        (m : ℝ) ^ k * (k : ℝ) * (lam / (m : ℝ)) ^ k := by
      gcongr
    _ = (k : ℝ) * lam ^ k := by
      rw [div_pow]
      field_simp [hm_real.ne']

/-- First-moment bound by the geometric cycle-length sum. -/
theorem expected_shortCyclePruning_removedEdges_le_cyclePowerSum
    {lam : ℝ} (hlam : 0 ≤ lam) {m g : ℕ} (hm : 0 < m)
    (θ : BernoulliParameter) (hp : θ.p = lam / (m : ℝ)) :
    bernoulliExpectation θ (shortCycleRemovedCountReal m g) ≤
      ∑ k ∈ Finset.Icc 3 g, (k : ℝ) * lam ^ k := by
  refine (bernoulliExpectation_shortCycleRemovedCountReal_le θ m g).trans ?_
  exact Finset.sum_le_sum fun k _hk ↦
    cycleEmbedding_firstMomentTerm_le hlam hm θ hp

/-- The geometric cycle-length sum is at most a simple polylogarithmic
envelope.  The `max 1 λ` handles both the subunit and superunit regimes. -/
theorem cyclePowerSum_le_envelope {lam : ℝ} (hlam : 0 ≤ lam) (g : ℕ) :
    (∑ k ∈ Finset.Icc 3 g, (k : ℝ) * lam ^ k) ≤
      ((g + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ g := by
  let L : ℝ := max 1 lam
  have hL_one : 1 ≤ L := le_max_left _ _
  have hL_nonneg : 0 ≤ L := zero_le_one.trans hL_one
  have hlamL : lam ≤ L := le_max_right _ _
  have hterm : ∀ k ∈ Finset.Icc 3 g,
      (k : ℝ) * lam ^ k ≤ (g + 1 : ℝ) * L ^ g := by
    intro k hk
    have hkg : k ≤ g := (Finset.mem_Icc.mp hk).2
    have hk_cast : (k : ℝ) ≤ (g : ℝ) + 1 := by
      exact_mod_cast hkg.trans (Nat.le_succ g)
    have hpow_base : lam ^ k ≤ L ^ k :=
      pow_le_pow_left₀ hlam hlamL k
    have hpow_exp : L ^ k ≤ L ^ g :=
      pow_le_pow_right₀ hL_one hkg
    exact mul_le_mul hk_cast (hpow_base.trans hpow_exp)
      (pow_nonneg hlam k) (by positivity)
  calc
    (∑ k ∈ Finset.Icc 3 g, (k : ℝ) * lam ^ k) ≤
        ∑ _k ∈ Finset.Icc 3 g, (g + 1 : ℝ) * L ^ g :=
      Finset.sum_le_sum hterm
    _ = ((Finset.Icc 3 g).card : ℝ) * ((g + 1 : ℝ) * L ^ g) := by
      simp
    _ ≤ (g + 1 : ℝ) * ((g + 1 : ℝ) * L ^ g) := by
      gcongr
      exact_mod_cast (show (Finset.Icc 3 g).card ≤ g + 1 by simp; omega)
    _ = ((g + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ g := by
      dsimp [L]
      push_cast
      ring

/-- Fixed-size expectation estimate in the explicit envelope used for the
asymptotic Markov argument. -/
theorem expected_shortCyclePruning_removedEdges_le_envelope
    {lam : ℝ} (hlam : 0 ≤ lam) {m g : ℕ} (hm : 0 < m)
    (θ : BernoulliParameter) (hp : θ.p = lam / (m : ℝ)) :
    bernoulliExpectation θ (shortCycleRemovedCountReal m g) ≤
      ((g + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ g :=
  (expected_shortCyclePruning_removedEdges_le_cyclePowerSum
    hlam hm θ hp).trans (cyclePowerSum_le_envelope hlam g)

/-- **Short-cycle pruning estimate in paper Lemma A.3.**

For a sparse Erdős--Rényi graph on `mₙ` vertices, the number of edges lying
in cycles of lengths at most `gₙ`, normalized by `mₙ`, converges to zero in
probability whenever the explicit deterministic envelope
`(gₙ+1)² max(1,λ)^gₙ / mₙ` vanishes.  This hypothesis is the abstract growth
condition used by the paper's choice `mₙ = ⌊n^r⌋` and logarithmic-logarithmic
cycle cutoff. -/
theorem shortCyclePruning_removedEdges_isLittleOInProbability
    (lam : ℝ) (hlam : 0 < lam) (m g : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hgrowth : Vanishes fun n ↦
      (((g n + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ (g n)) / (m n : ℝ)) :
    TendstoInProbability
      (fun n ↦ erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n)))
      (fun n x ↦
        shortCycleRemovedCountReal (m n) (g n) x / (m n : ℝ)) 0 := by
  let law : ∀ n, FiniteLaw (BooleanConfiguration (AmbientEdge (m n))) :=
    fun n ↦ erdosRenyiLaw (n := m n)
      (sparseBernoulliParameter lam (m n))
  let removed : ∀ n, BooleanConfiguration (AmbientEdge (m n)) → ℝ :=
    fun n x ↦ shortCycleRemovedCountReal (m n) (g n) x / (m n : ℝ)
  let envelope : ℕ → ℝ := fun n ↦
    ((g n + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ (g n)
  have hm_pos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  have hp : ∀ᶠ n in atTop,
      (sparseBernoulliParameter lam (m n)).p = lam / (m n : ℝ) :=
    hm.eventually (eventually_sparseBernoulliParameter_p_eq hlam)
  intro δ hδ
  have hupper : ∀ᶠ n in atTop,
      (law n).prob
          (FiniteLaw.event fun x ↦ δ ≤ |removed n x - 0|) ≤
        (envelope n / (m n : ℝ)) / δ := by
    filter_upwards [hm_pos, hp] with n hmn hpn
    have hmn_real : (0 : ℝ) < m n := by exact_mod_cast hmn
    let X : BooleanConfiguration (AmbientEdge (m n)) → ℝ := removed n
    have hX_nonneg : ∀ x, 0 ≤ X x := by
      intro x
      dsimp [X, removed, shortCycleRemovedCountReal]
      positivity
    have hmarkov := (law n).markov X hX_nonneg hδ
    have hevent :
        FiniteLaw.event (fun x ↦ δ ≤ |removed n x - 0|) =
          FiniteLaw.event (fun x ↦ δ ≤ X x) := by
      ext x
      simp only [FiniteLaw.mem_event, sub_zero]
      rw [abs_of_nonneg (hX_nonneg x)]
    rw [hevent]
    calc
      (law n).prob (FiniteLaw.event fun x ↦ δ ≤ X x) ≤
          (law n).expect X / δ := hmarkov
      _ = (bernoulliExpectation (sparseBernoulliParameter lam (m n))
            (shortCycleRemovedCountReal (m n) (g n)) /
          (m n : ℝ)) / δ := by
        congr 1
        change
          (∑ x, bernoulliProductMass (sparseBernoulliParameter lam (m n)) x *
              (shortCycleRemovedCountReal (m n) (g n) x / (m n : ℝ))) = _
        unfold bernoulliExpectation
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ ≤ (envelope n / (m n : ℝ)) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        apply div_le_div_of_nonneg_right _ hmn_real.le
        dsimp [envelope]
        exact expected_shortCyclePruning_removedEdges_le_envelope
          hlam.le hmn (sparseBernoulliParameter lam (m n)) hpn
  have hright : Vanishes fun n ↦ (envelope n / (m n : ℝ)) / δ := by
    have hscaled := Vanishes.const_mul (1 / δ) hgrowth
    apply hscaled.congr'
    filter_upwards with n
    dsimp [envelope]
    field_simp [hδ.ne']
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      (law n).prob_nonneg
        (FiniteLaw.event fun x ↦ δ ≤ |removed n x - 0|)
  · exact hupper
  · exact hright

/-- Removing every edge that lies on a cycle of length at most `gₙ` does
not change the limiting sparse Erdős--Rényi edge density under the same
explicit growth condition.  This is the short-cycle-pruning portion of paper
Lemma A.3. -/
theorem shortCyclePruned_edgeDensity_tendstoInProbability
    (lam : ℝ) (hlam : 0 < lam) (m g : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hgrowth : Vanishes fun n ↦
      (((g n + 1 : ℕ) : ℝ) ^ 2 * (max 1 lam) ^ (g n)) / (m n : ℝ)) :
    TendstoInProbability
      (fun n ↦ erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n)))
      (fun n x ↦
        (bernoulliCountReal x -
          shortCycleRemovedCountReal (m n) (g n) x) / (m n : ℝ))
      (lam / 2) := by
  have horiginal :=
    sparseErdosRenyi_edgeDensity_tendstoInProbability lam hlam m hm
  have hremoved :=
    shortCyclePruning_removedEdges_isLittleOInProbability
      lam hlam m g hm hgrowth
  simpa only [sub_div, sub_zero] using horiginal.sub hremoved

end

end LowDegree
