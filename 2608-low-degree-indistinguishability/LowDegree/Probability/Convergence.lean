import LowDegree.Asymptotics.Basic
import LowDegree.Probability.Finite

/-!
# Convergence in probability for varying finite sample spaces

The random graphs in the appendix live on a different finite space for each
`n`.  This module records convergence in probability directly through their
finite laws, avoiding an unnecessary common ambient probability space.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.decEq

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Event cut out by a decidable predicate. -/
noncomputable def event (p : Ω → Prop) : Finset Ω := by
  classical
  exact Finset.univ.filter p

@[simp]
theorem mem_event {p : Ω → Prop} (ω : Ω) : ω ∈ event p ↔ p ω := by
  classical
  simp [event]

theorem prob_nonneg (q : FiniteLaw Ω) (s : Finset Ω) : 0 ≤ q.prob s :=
  Finset.sum_nonneg fun ω _ ↦ q.mass_nonneg ω

theorem prob_mono (q : FiniteLaw Ω) {s t : Finset Ω} (hst : s ⊆ t) :
    q.prob s ≤ q.prob t := by
  unfold prob
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun ω _ _ ↦ q.mass_nonneg ω)

theorem prob_union_le (q : FiniteLaw Ω) (s t : Finset Ω) :
    q.prob (s ∪ t) ≤ q.prob s + q.prob t := by
  have hidentity := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := q.mass)
  have hinter : 0 ≤ ∑ ω ∈ s ∩ t, q.mass ω :=
    Finset.sum_nonneg fun ω _ ↦ q.mass_nonneg ω
  unfold prob
  linarith

/-- Finite Markov inequality in the normalization used for the random-graph
pruning argument. -/
theorem markov
    (q : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    q.prob (event fun ω ↦ a ≤ X ω) ≤ q.expect X / a := by
  let bad : Finset Ω := event fun ω ↦ a ≤ X ω
  have hweighted : a * q.prob bad ≤ q.expect X := by
    calc
      a * q.prob bad = ∑ ω ∈ bad, q.mass ω * a := by
        simp only [prob, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ ≤ ∑ ω ∈ bad, q.mass ω * X ω := by
        exact Finset.sum_le_sum fun ω hω ↦
          mul_le_mul_of_nonneg_left ((mem_event ω).mp hω)
            (q.mass_nonneg ω)
      _ ≤ ∑ ω, q.mass ω * X ω := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
          (fun ω _ _ ↦ mul_nonneg (q.mass_nonneg ω) (hX ω))
      _ = q.expect X := rfl
  exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using hweighted)

end FiniteLaw

/-- Convergence in probability for real random variables on varying finite
sample spaces. -/
def TendstoInProbability
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (law : ∀ n, FiniteLaw (Ω n))
    (X : ∀ n, Ω n → ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, Vanishes (fun n ↦
    (law n).prob (FiniteLaw.event fun ω ↦ δ ≤ |X n ω - a|))

namespace TendstoInProbability

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
variable {law : ∀ n, FiniteLaw (Ω n)}
variable {X Y : ∀ n, Ω n → ℝ} {a b : ℝ}

theorem const (law : ∀ n, FiniteLaw (Ω n)) (a : ℝ) :
    TendstoInProbability law (fun _ _ ↦ a) a := by
  intro δ hδ
  change Tendsto (fun n ↦
    (law n).prob (FiniteLaw.event fun _ : Ω n ↦ δ ≤ |a - a|))
      atTop (𝓝 0)
  convert tendsto_const_nhds using 1
  funext n
  simp [FiniteLaw.event, FiniteLaw.prob, hδ.not_ge]

/-- Convergence in probability is unchanged by modifications made on an
event whose probability vanishes. -/
theorem congr_of_ne_vanishes
    (hX : TendstoInProbability law X a)
    (hne : Vanishes (fun n ↦
      (law n).prob (FiniteLaw.event fun ω ↦ X n ω ≠ Y n ω))) :
    TendstoInProbability law Y a := by
  intro δ hδ
  let badX : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦ δ ≤ |X n ω - a|
  let changed : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦ X n ω ≠ Y n ω
  let badY : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦ δ ≤ |Y n ω - a|
  have hsubset : ∀ n, badY n ⊆ changed n ∪ badX n := by
    intro n ω hω
    simp only [badY, changed, badX, FiniteLaw.mem_event,
      Finset.mem_union] at hω ⊢
    by_cases hxy : X n ω = Y n ω
    · exact Or.inr (by simpa [hxy] using hω)
    · exact Or.inl hxy
  have hbound : ∀ n,
      (law n).prob (badY n) ≤
        (law n).prob (changed n) + (law n).prob (badX n) := by
    intro n
    exact le_trans ((law n).prob_mono (hsubset n))
      ((law n).prob_union_le (changed n) (badX n))
  have hnonneg : ∀ n, 0 ≤ (law n).prob (badY n) :=
    fun n ↦ (law n).prob_nonneg (badY n)
  have hright : Vanishes (fun n ↦
      (law n).prob (changed n) + (law n).prob (badX n)) := by
    exact hne.add (hX δ hδ)
  exact squeeze_zero hnonneg hbound hright

theorem add
    (hX : TendstoInProbability law X a)
    (hY : TendstoInProbability law Y b) :
    TendstoInProbability law (fun n ω ↦ X n ω + Y n ω) (a + b) := by
  intro δ hδ
  let badX : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦ δ / 2 ≤ |X n ω - a|
  let badY : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦ δ / 2 ≤ |Y n ω - b|
  let badSum : (n : ℕ) → Finset (Ω n) := fun n ↦
    FiniteLaw.event fun ω ↦
      δ ≤ |(X n ω + Y n ω) - (a + b)|
  have hsubset : ∀ n, badSum n ⊆ badX n ∪ badY n := by
    intro n ω hω
    simp only [badSum, badX, badY, FiniteLaw.mem_event,
      Finset.mem_union] at hω ⊢
    by_contra hnot
    have hnot' := not_or.mp hnot
    have hxlt : |X n ω - a| < δ / 2 := lt_of_not_ge hnot'.1
    have hylt : |Y n ω - b| < δ / 2 := lt_of_not_ge hnot'.2
    have htriangle :
        |(X n ω + Y n ω) - (a + b)| ≤
          |X n ω - a| + |Y n ω - b| := by
      convert abs_add_le (X n ω - a) (Y n ω - b) using 1 <;> ring
    linarith
  have hbound : ∀ n,
      (law n).prob (badSum n) ≤
        (law n).prob (badX n) + (law n).prob (badY n) := by
    intro n
    exact le_trans ((law n).prob_mono (hsubset n))
      ((law n).prob_union_le (badX n) (badY n))
  have hnonneg : ∀ n, 0 ≤ (law n).prob (badSum n) :=
    fun n ↦ (law n).prob_nonneg (badSum n)
  have hright : Vanishes (fun n ↦
      (law n).prob (badX n) + (law n).prob (badY n)) :=
    (hX (δ / 2) (half_pos hδ)).add
      (hY (δ / 2) (half_pos hδ))
  exact squeeze_zero hnonneg hbound hright

theorem neg (hX : TendstoInProbability law X a) :
    TendstoInProbability law (fun n ω ↦ -X n ω) (-a) := by
  intro δ hδ
  simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hX δ hδ

theorem sub
    (hX : TendstoInProbability law X a)
    (hY : TendstoInProbability law Y b) :
    TendstoInProbability law (fun n ω ↦ X n ω - Y n ω) (a - b) := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

end TendstoInProbability

end

end LowDegree
