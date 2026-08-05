import LowDegree.Fourier
import LowDegree.Probability.Convergence

/-!
# Cylinder events on a finite Bernoulli cube

The random-graph union bounds repeatedly use that a prescribed collection of
edges is present with probability `p^k`.  This file proves that identity for
the concrete finite Bernoulli law and records a finite union bound over a
family of cylinder events.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The cylinder event on which every coordinate in `A` is present. -/
def allPresentEvent (A : Finset E) : Finset (BooleanConfiguration E) :=
  FiniteLaw.event fun x ↦ ∀ e ∈ A, x e = true

@[simp]
theorem mem_allPresentEvent (A : Finset E) (x : BooleanConfiguration E) :
    x ∈ allPresentEvent A ↔ ∀ e ∈ A, x e = true := by
  simp [allPresentEvent]

private theorem sum_prod_configuration (g : E → Bool → ℝ) :
    ∑ x : BooleanConfiguration E, ∏ e, g e (x e) =
      ∏ e, ∑ b : Bool, g e b := by
  simpa using (Fintype.prod_sum g).symm

/-- A fixed set of Bernoulli coordinates is simultaneously present with
probability exactly `p^|A|`. -/
theorem bernoulliProductLaw_prob_allPresent
    (θ : BernoulliParameter) (A : Finset E) :
    (bernoulliProductLaw θ).prob (allPresentEvent A) = θ.p ^ A.card := by
  classical
  let g : E → Bool → ℝ := fun e b ↦
    if e ∈ A then
      if b = true then θ.bitMass b else 0
    else θ.bitMass b
  have hterm (x : BooleanConfiguration E) :
      (if ∀ e ∈ A, x e = true then bernoulliProductMass θ x else 0) =
        ∏ e, g e (x e) := by
    by_cases hx : ∀ e ∈ A, x e = true
    · rw [if_pos hx]
      unfold bernoulliProductMass
      apply Finset.prod_congr rfl
      intro e _he
      by_cases heA : e ∈ A
      · simp [g, heA, hx e heA]
      · simp [g, heA]
    · rw [if_neg hx]
      push_neg at hx
      obtain ⟨e, heA, hefalse⟩ := hx
      have hbit : x e = false := by
        cases hxe : x e
        · rfl
        · exact (hefalse hxe).elim
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [g, heA, hbit]
  unfold FiniteLaw.prob allPresentEvent FiniteLaw.event
  rw [Finset.sum_filter]
  simp only [bernoulliProductLaw]
  simp_rw [hterm]
  rw [sum_prod_configuration]
  calc
    (∏ e : E, ∑ b : Bool, g e b) =
        ∏ e : E, if e ∈ A then θ.p else 1 := by
      apply Finset.prod_congr rfl
      intro e _he
      by_cases heA : e ∈ A
      · rw [if_pos heA]
        rw [Fintype.sum_bool]
        simp [g, heA, BernoulliParameter.bitMass]
      · rw [if_neg heA]
        simpa [g, heA, add_comm] using θ.sum_bitMass
    _ = θ.p ^ A.card := by
      rw [Finset.prod_ite_mem]
      simp

/-- Probability of a union of finitely many events is bounded by the sum of
their probabilities. -/
theorem FiniteLaw.prob_biUnion_le
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq Ω] [DecidableEq I]
    (q : FiniteLaw Ω) (event : I → Finset Ω) :
    q.prob (Finset.univ.biUnion event) ≤ ∑ i, q.prob (event i) := by
  induction (Finset.univ : Finset I) using Finset.induction_on with
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

/-- Union bound for a finite family of prescribed-present coordinate sets. -/
theorem bernoulliProductLaw_prob_biUnion_allPresent_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (θ : BernoulliParameter) (A : I → Finset E) :
    (bernoulliProductLaw θ).prob
        (Finset.univ.biUnion fun i ↦ allPresentEvent (A i)) ≤
      ∑ i, θ.p ^ (A i).card := by
  calc
    _ ≤ ∑ i, (bernoulliProductLaw θ).prob (allPresentEvent (A i)) :=
      (bernoulliProductLaw θ).prob_biUnion_le _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact bernoulliProductLaw_prob_allPresent θ (A i)

end

end LowDegree
