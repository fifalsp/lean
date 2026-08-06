import LowDegree.Supercritical
import LowDegree.SupercriticalLocalSparsity
import LowDegree.SupercriticalPruning

/-!
# Rare local-sparsity truncation after short-cycle pruning

This module joins the two concrete probabilistic inputs of paper Lemma A.3.
The first modification deletes every edge on a short cycle.  The second keeps
that pruned graph on the local-sparsity event and replaces it by the empty
graph on the complementary event.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Edge density after short-cycle pruning. -/
noncomputable def shortCyclePrunedEdgeDensity
    (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) : ℝ :=
  (bernoulliCountReal x - shortCycleRemovedCountReal (m n) (g n) x) /
    (m n : ℝ)

/-- The exact second truncation in the appendix: retain the short-cycle-pruned
plant on the local-sparsity event and otherwise replace it by the empty
graph.  At the level needed by Lemma A.3, this records its normalized edge
count. -/
noncomputable def locallyTruncatedPrunedEdgeDensityAt
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ)
    (x : BooleanConfiguration (AmbientEdge (m n))) : ℝ :=
  if x ∈ localSparsityEvent n (m n)
      (localSparsityPowerCutoff (m n) gamma)
      (localSparsitySlackConstant lam r gamma) then
    shortCyclePrunedEdgeDensity m g n x
  else 0

/-- The rare local-sparsity truncation changes the normalized pruned edge
count only on the local-sparsity failure event. -/
theorem pruned_ne_locallyTruncated_subset_failure
    (lam r gamma : ℝ) (m g : ℕ → ℕ) (n : ℕ) :
    FiniteLaw.event (fun x : BooleanConfiguration (AmbientEdge (m n)) ↦
      shortCyclePrunedEdgeDensity m g n x ≠
        locallyTruncatedPrunedEdgeDensityAt lam r gamma m g n x) ⊆
      localSparsityFailureEvent n (m n)
        (localSparsityPowerCutoff (m n) gamma)
        (localSparsitySlackConstant lam r gamma) := by
  intro x hx
  rw [FiniteLaw.mem_event] at hx
  unfold locallyTruncatedPrunedEdgeDensityAt at hx
  by_cases hgood : x ∈ localSparsityEvent n (m n)
      (localSparsityPowerCutoff (m n) gamma)
      (localSparsitySlackConstant lam r gamma)
  · simp [hgood] at hx
  · unfold localSparsityEvent at hgood
    simpa using hgood

/-- **Paper Lemma A.3 (edge-density form).**

For any sequence satisfying the paper's power-scale and explicit pruning
envelope conditions, the twice-truncated sparse Erdős--Rényi plant retains
edge density `λ/2` in probability.  The paper's choices
`mₙ = ⌊nʳ⌋` and `gₙ = max(3,⌊log log n⌋)` discharge these two growth
hypotheses. -/
theorem locallyTruncatedPruned_edgeDensity_tendstoInProbability
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
      (fun n ↦ erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n)))
      (locallyTruncatedPrunedEdgeDensityAt lam r gamma m g)
      (lam / 2) := by
  let law : ∀ n, FiniteLaw (BooleanConfiguration (AmbientEdge (m n))) :=
    fun n ↦ erdosRenyiLaw (n := m n)
      (sparseBernoulliParameter lam (m n))
  have hpruned : TendstoInProbability law
      (shortCyclePrunedEdgeDensity m g) (lam / 2) := by
    simpa only [shortCyclePrunedEdgeDensity] using
      shortCyclePruned_edgeDensity_tendstoInProbability
        lam hlam m g hm hgrowth
  have hfailure := sparseErdosRenyi_localSparsityFailure_vanishes
    lam r gamma hlam hr hgamma m hm hpowerScale
  have hne : Vanishes fun n ↦
      (law n).prob (FiniteLaw.event fun x ↦
        shortCyclePrunedEdgeDensity m g n x ≠
          locallyTruncatedPrunedEdgeDensityAt lam r gamma m g n x) := by
    apply squeeze_zero
    · exact fun n ↦ (law n).prob_nonneg _
    · intro n
      exact (law n).prob_mono
        (pruned_ne_locallyTruncated_subset_failure lam r gamma m g n)
    · exact hfailure
  exact hpruned.congr_of_ne_vanishes hne

end

end LowDegree
