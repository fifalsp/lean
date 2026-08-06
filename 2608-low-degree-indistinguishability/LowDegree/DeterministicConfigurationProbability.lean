import LowDegree.DeterministicConfigurationSelection
import LowDegree.Probability.Convergence

/-!
# Finite probability space for configuration permutations

The configuration estimates can be carried out entirely in the repository's
finite-law framework.  This module supplies the uniform law and the exact
positive-probability selection step; no measure-theoretic probability space
is needed.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace FiniteLaw

variable {Omega : Type*} [Fintype Omega]

/-- The uniform law on a nonempty finite type. -/
noncomputable def uniform [Nonempty Omega] : FiniteLaw Omega where
  mass _ := (Fintype.card Omega : ℝ)⁻¹
  mass_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_mass := by
    have hcard : (Fintype.card Omega : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

@[simp] theorem uniform_mass [Nonempty Omega] (omega : Omega) :
    (uniform : FiniteLaw Omega).mass omega = (Fintype.card Omega : ℝ)⁻¹ :=
  rfl

/-- Under the uniform law, probability is normalized finite cardinality. -/
theorem uniform_prob [Nonempty Omega] (s : Finset Omega) :
    (uniform : FiniteLaw Omega).prob s =
      (s.card : ℝ) / (Fintype.card Omega : ℝ) := by
  simp [FiniteLaw.prob, uniform, div_eq_mul_inv]

theorem prob_univ (q : FiniteLaw Omega) : q.prob Finset.univ = 1 := by
  simpa [FiniteLaw.prob] using q.sum_mass

/-- An event with probability strictly below one omits at least one outcome. -/
theorem exists_notMem_of_prob_lt_one (q : FiniteLaw Omega)
    (bad : Finset Omega) (hbad : q.prob bad < 1) :
    ∃ omega : Omega, omega ∉ bad := by
  by_contra hnone
  push_neg at hnone
  have hbadUniv : bad = Finset.univ := by
    ext omega
    simp [hnone omega]
  rw [hbadUniv, q.prob_univ] at hbad
  exact lt_irrefl 1 hbad

/-- Union-bound selection for three failure events, the exact form used for
local sparsity, short-cycle loss, and projection defect. -/
theorem exists_notMem_three_of_sum_prob_lt_one (q : FiniteLaw Omega)
    (badLocal badCycle badDefect : Finset Omega)
    (hbad : q.prob badLocal + q.prob badCycle + q.prob badDefect < 1) :
    ∃ omega : Omega,
      omega ∉ badLocal ∧ omega ∉ badCycle ∧ omega ∉ badDefect := by
  have hunion :
      q.prob (badLocal ∪ badCycle ∪ badDefect) < 1 := by
    calc
      q.prob (badLocal ∪ badCycle ∪ badDefect) ≤
          q.prob (badLocal ∪ badCycle) + q.prob badDefect :=
        q.prob_union_le _ _
      _ ≤ q.prob badLocal + q.prob badCycle + q.prob badDefect := by
        linarith [q.prob_union_le badLocal badCycle]
      _ < 1 := hbad
  obtain ⟨omega, homega⟩ := q.exists_notMem_of_prob_lt_one
    (badLocal ∪ badCycle ∪ badDefect) hunion
  simp only [Finset.mem_union, not_or] at homega
  exact ⟨omega, homega.1.1, homega.1.2, homega.2⟩

end FiniteLaw

/-- Uniformly relabel the canonical pairing of the `m(2d)` half-edges. -/
noncomputable def configurationPermutationLaw (m d : ℕ) :
    FiniteLaw (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  FiniteLaw.uniform

/-- The configuration-valued random variable associated with the uniform
permutation presentation. -/
def randomConfiguration (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    Configuration m (d + d) :=
  Configuration.ofPermutation m d sigma

/-- The partner obtained by conjugating a fixed pairing by a relabelling. -/
def conjugatedPartner {Omega : Type*} (pairing sigma : Equiv.Perm Omega)
    (h : Omega) : Omega :=
  sigma (pairing (sigma.symm h))

theorem conjugatedPartner_ne {Omega : Type*}
    (pairing sigma : Equiv.Perm Omega)
    (hpairing : ∀ h, pairing h ≠ h) (h : Omega) :
    conjugatedPartner pairing sigma h ≠ h := by
  intro heq
  apply hpairing (sigma.symm h)
  apply sigma.injective
  simpa [conjugatedPartner] using heq

theorem conjugatedPartner_mul {Omega : Type*}
    (pairing sigma tau : Equiv.Perm Omega) (h : Omega) :
    conjugatedPartner pairing (tau * sigma) (tau h) =
      tau (conjugatedPartner pairing sigma h) := by
  have hinv : (tau * sigma).symm (tau h) = sigma.symm h := by
    apply (tau * sigma).injective
    simp
  simp [conjugatedPartner, hinv]

/-- Event that two prescribed labels form a pair after uniformly
conjugating `pairing`. -/
noncomputable def conjugatePairEvent {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (a b : Omega) :
    Finset (Equiv.Perm Omega) :=
  FiniteLaw.event fun sigma ↦ conjugatedPartner pairing sigma a = b

/-- Simultaneously relabelling both prescribed endpoints does not change
the number of permutation presentations realizing the pair. -/
theorem conjugatePairEvent_card_equivariant
    {Omega : Type*} [Fintype Omega]
    (pairing tau : Equiv.Perm Omega) (a b : Omega) :
    (conjugatePairEvent pairing a b).card =
      (conjugatePairEvent pairing (tau a) (tau b)).card := by
  classical
  apply Finset.card_bij'
      (fun sigma _ ↦ tau * sigma)
      (fun rho _ ↦ tau.symm * rho)
  · intro sigma hsigma
    rw [conjugatePairEvent, FiniteLaw.mem_event] at hsigma ⊢
    rw [conjugatedPartner_mul, hsigma]
  · intro rho hrho
    rw [conjugatePairEvent, FiniteLaw.mem_event] at hrho ⊢
    simpa [conjugatedPartner_mul] using congrArg tau.symm hrho
  · intro sigma hsigma
    change tau.symm * (tau * sigma) = sigma
    rw [← Equiv.Perm.inv_def]
    simp
  · intro rho hrho
    change tau * (tau.symm * rho) = rho
    rw [← Equiv.Perm.inv_def]
    simp

/-- For a fixed first endpoint, all allowed second endpoints occur equally
often under uniform relabelling. -/
theorem conjugatePairEvent_card_eq_of_ne
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (a b c : Omega)
    (hab : a ≠ b) (hac : a ≠ c) :
    (conjugatePairEvent pairing a b).card =
      (conjugatePairEvent pairing a c).card := by
  classical
  have h := conjugatePairEvent_card_equivariant pairing (Equiv.swap b c) a b
  simpa [Equiv.swap_apply_of_ne_of_ne hab hac] using h

/-- Exact counting identity behind the one-prescribed-pair probability:
there are `|Omega|-1` equiprobable possible partners of `a`. -/
theorem card_sub_one_mul_conjugatePairEvent
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (hpairing : ∀ h, pairing h ≠ h)
    (a b : Omega) (hab : a ≠ b) :
    (Fintype.card Omega - 1) * (conjugatePairEvent pairing a b).card =
      Fintype.card (Equiv.Perm Omega) := by
  classical
  let partnerAt : Equiv.Perm Omega → Omega :=
    fun sigma ↦ conjugatedPartner pairing sigma a
  have hmaps : Set.MapsTo partnerAt
      (Finset.univ : Finset (Equiv.Perm Omega))
      (Finset.univ.erase a : Finset Omega) := by
    intro sigma hsigma
    have hne : partnerAt sigma ≠ a :=
      conjugatedPartner_ne pairing sigma hpairing a
    simpa only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff,
      Set.mem_univ, Set.mem_singleton_iff, true_and] using hne
  have hfibers := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : Fintype.card (Equiv.Perm Omega) =
      ∑ c ∈ Finset.univ.erase a,
        (conjugatePairEvent pairing a c).card := by
    simpa [partnerAt, conjugatePairEvent, FiniteLaw.event] using hfibers
  calc
    (Fintype.card Omega - 1) * (conjugatePairEvent pairing a b).card =
        (Finset.univ.erase a).card *
          (conjugatePairEvent pairing a b).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    _ = ∑ c ∈ Finset.univ.erase a,
          (conjugatePairEvent pairing a b).card := by simp
    _ = ∑ c ∈ Finset.univ.erase a,
          (conjugatePairEvent pairing a c).card := by
      apply Finset.sum_congr rfl
      intro c hc
      exact conjugatePairEvent_card_eq_of_ne pairing a b c hab
        (Finset.ne_of_mem_erase hc).symm
    _ = Fintype.card (Equiv.Perm Omega) := hsum.symm

/-- Exact probability that a uniformly relabelled fixed-point-free pairing
contains one prescribed pair.  This is the first factor in every pairing
product used in Appendix A.4--A.5. -/
theorem uniform_prob_conjugatePairEvent
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (hpairing : ∀ h, pairing h ≠ h)
    (a b : Omega) (hab : a ≠ b) :
    (FiniteLaw.uniform : FiniteLaw (Equiv.Perm Omega)).prob
        (conjugatePairEvent pairing a b) =
      1 / (Fintype.card Omega - 1 : ℕ) := by
  rw [FiniteLaw.uniform_prob]
  have hcard : 1 < Fintype.card Omega :=
    Fintype.one_lt_card_iff.mpr ⟨a, pairing a, (hpairing a).symm⟩
  have hleft : ((Fintype.card Omega - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hcard).ne'
  have hright : (Fintype.card (Equiv.Perm Omega) : ℝ) ≠ 0 := by
    positivity
  have hcount := card_sub_one_mul_conjugatePairEvent
    pairing hpairing a b hab
  have hcountReal :
      ((Fintype.card Omega - 1 : ℕ) : ℝ) *
          ((conjugatePairEvent pairing a b).card : ℝ) =
        (Fintype.card (Equiv.Perm Omega) : ℝ) := by
    exact_mod_cast hcount
  apply (div_eq_div_iff hright hleft).2
  nlinarith [hcountReal]

@[simp] theorem randomConfiguration_partner (m d : ℕ)
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) (h) :
    (randomConfiguration m d sigma).partner h =
      conjugatedPartner (Configuration.standardConfiguration m d).partner sigma h :=
  rfl

/-- One prescribed pair event for the configuration model. -/
noncomputable def configurationPairEvent
    (m d : ℕ) (a b : ConfigurationHalfEdge m (d + d)) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  conjugatePairEvent (Configuration.standardConfiguration m d).partner a b

end

end LowDegree
