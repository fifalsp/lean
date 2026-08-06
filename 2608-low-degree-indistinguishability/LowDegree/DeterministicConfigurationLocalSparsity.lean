import LowDegree.DeterministicConfigurationModelBridge
import LowDegree.SupercriticalCanonicalScales

/-!
# Prescribed pairs in the finite configuration model

This file supplies the reusable exact counting lemma behind the local
sparsity, short-cycle, and projection-defect estimates.  If `k` disjoint
ordered pairs are prescribed on a finite label set of size `N`, a uniformly
conjugated fixed-point-free involution contains all of them with probability

`1 / ((N - 1) * (N - 3) * ... * (N - (2k - 1)))`.

The proof is finite and elementary.  After `k` pairs have been exposed, the
first endpoint of a new pair has exactly `N - (2k + 1)` possible partners.
Left multiplication by a transposition gives a bijection between all of the
corresponding fibres.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The flattened list of endpoints of a list of ordered pairs. -/
def prescribedPairEndpoints {Omega : Type*} (pairs : List (Omega × Omega)) : List Omega :=
  pairs.flatMap fun p => [p.1, p.2]

@[simp] theorem prescribedPairEndpoints_nil {Omega : Type*} :
    prescribedPairEndpoints ([] : List (Omega × Omega)) = [] :=
  rfl

@[simp] theorem prescribedPairEndpoints_cons {Omega : Type*}
    (a b : Omega) (pairs : List (Omega × Omega)) :
    prescribedPairEndpoints ((a, b) :: pairs) =
      a :: b :: prescribedPairEndpoints pairs :=
  rfl

@[simp] theorem length_prescribedPairEndpoints {Omega : Type*}
    (pairs : List (Omega × Omega)) :
    (prescribedPairEndpoints pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
      simp [prescribedPairEndpoints]
      omega

/-- Event that every ordered pair in `pairs` is a block of the conjugated
pairing.  Pair orientation is immaterial, but retaining it is convenient for
cycle and edge enumerations. -/
noncomputable def conjugatePairsEvent {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (pairs : List (Omega × Omega)) :
    Finset (Equiv.Perm Omega) :=
  FiniteLaw.event fun sigma =>
    ∀ p ∈ pairs, conjugatedPartner pairing sigma p.1 = p.2

@[simp] theorem mem_conjugatePairsEvent {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (pairs : List (Omega × Omega))
    (sigma : Equiv.Perm Omega) :
    sigma ∈ conjugatePairsEvent pairing pairs ↔
      ∀ p ∈ pairs, conjugatedPartner pairing sigma p.1 = p.2 := by
  simp [conjugatePairsEvent]

@[simp] theorem conjugatePairsEvent_nil {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) :
    conjugatePairsEvent pairing [] = Finset.univ := by
  ext sigma
  simp

theorem conjugatedPartner_involutive {Omega : Type*}
    (pairing sigma : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing) :
    Function.Involutive (conjugatedPartner pairing sigma) := by
  intro a
  simp only [conjugatedPartner]
  rw [Equiv.symm_apply_apply, hpairing]
  exact sigma.apply_symm_apply a

theorem conjugatedPartner_eq_iff_eq {Omega : Type*}
    (pairing sigma : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing) (a b : Omega) :
    conjugatedPartner pairing sigma a = b ↔
      conjugatedPartner pairing sigma b = a := by
  constructor <;> intro h
  · rw [← h, conjugatedPartner_involutive pairing sigma hpairing]
  · rw [← h, conjugatedPartner_involutive pairing sigma hpairing]

/-- Labels still available as a partner for a fresh first endpoint after the
pairs in `pairs` have been prescribed. -/
def availablePairPartners {Omega : Type*} [Fintype Omega]
    (a : Omega) (pairs : List (Omega × Omega)) : Finset Omega :=
  (prescribedPairEndpoints pairs).toFinsetᶜ.erase a

@[simp] theorem mem_availablePairPartners {Omega : Type*} [Fintype Omega]
    (a c : Omega) (pairs : List (Omega × Omega)) :
    c ∈ availablePairPartners a pairs ↔
      c ≠ a ∧ c ∉ prescribedPairEndpoints pairs := by
  simp [availablePairPartners]

theorem card_availablePairPartners {Omega : Type*} [Fintype Omega]
    (a : Omega) (pairs : List (Omega × Omega))
    (ha : a ∉ prescribedPairEndpoints pairs)
    (hpairs : (prescribedPairEndpoints pairs).Nodup) :
    (availablePairPartners a pairs).card =
      Fintype.card Omega - (2 * pairs.length + 1) := by
  have ha' : a ∈ (prescribedPairEndpoints pairs).toFinsetᶜ := by
    simpa using ha
  rw [availablePairPartners, Finset.card_erase_of_mem ha', Finset.card_compl,
    List.toFinset_card_of_nodup hpairs, length_prescribedPairEndpoints]
  omega

/-- If all old pairs occur, the partner of a fresh endpoint cannot be any
old endpoint. -/
theorem conjugatedPartner_not_mem_endpoints
    {Omega : Type*} [Fintype Omega]
    (pairing sigma : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (pairs : List (Omega × Omega)) (a : Omega)
    (ha : a ∉ prescribedPairEndpoints pairs)
    (hsigma : sigma ∈ conjugatePairsEvent pairing pairs) :
    conjugatedPartner pairing sigma a ∉ prescribedPairEndpoints pairs := by
  intro hmem
  rw [prescribedPairEndpoints, List.mem_flatMap] at hmem
  rcases hmem with ⟨p, hp, hendpoint⟩
  have hpPair := (mem_conjugatePairsEvent pairing pairs sigma).mp hsigma p hp
  simp at hendpoint
  rcases hendpoint with hfirst | hsecond
  · have haeq : a = p.2 := by
      calc
        a = conjugatedPartner pairing sigma
              (conjugatedPartner pairing sigma a) :=
            (conjugatedPartner_involutive pairing sigma hpairing a).symm
        _ = conjugatedPartner pairing sigma p.1 := by rw [hfirst]
        _ = p.2 := hpPair
    apply ha
    rw [haeq, prescribedPairEndpoints, List.mem_flatMap]
    exact ⟨p, hp, by simp⟩
  · have hpReverse : conjugatedPartner pairing sigma p.2 = p.1 :=
      (conjugatedPartner_eq_iff_eq pairing sigma hpairing p.1 p.2).mp hpPair
    have haeq : a = p.1 := by
      calc
        a = conjugatedPartner pairing sigma
              (conjugatedPartner pairing sigma a) :=
            (conjugatedPartner_involutive pairing sigma hpairing a).symm
        _ = conjugatedPartner pairing sigma p.2 := by rw [hsecond]
        _ = p.1 := hpReverse
    apply ha
    rw [haeq, prescribedPairEndpoints, List.mem_flatMap]
    exact ⟨p, hp, by simp⟩

/-- Changing the prescribed partner of a fresh endpoint among the available
labels does not change the cardinality of the simultaneous-pair event. -/
theorem conjugatePairsEvent_cons_card_eq_of_available
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega) (pairs : List (Omega × Omega))
    (a b c : Omega)
    (hb : b ∈ availablePairPartners a pairs)
    (hc : c ∈ availablePairPartners a pairs) :
    (conjugatePairsEvent pairing ((a, b) :: pairs)).card =
      (conjugatePairsEvent pairing ((a, c) :: pairs)).card := by
  classical
  let tau : Equiv.Perm Omega := Equiv.swap b c
  have hab : a ≠ b := (mem_availablePairPartners a b pairs).mp hb |>.1.symm
  have hac : a ≠ c := (mem_availablePairPartners a c pairs).mp hc |>.1.symm
  have hbOld : b ∉ prescribedPairEndpoints pairs :=
    (mem_availablePairPartners a b pairs).mp hb |>.2
  have hcOld : c ∉ prescribedPairEndpoints pairs :=
    (mem_availablePairPartners a c pairs).mp hc |>.2
  have htauA : tau a = a := by
    exact Equiv.swap_apply_of_ne_of_ne hab hac
  have htauOld : ∀ p ∈ pairs, tau p.1 = p.1 ∧ tau p.2 = p.2 := by
    intro p hp
    have hp1 : p.1 ∈ prescribedPairEndpoints pairs := by
      rw [prescribedPairEndpoints, List.mem_flatMap]
      exact ⟨p, hp, by simp⟩
    have hp2 : p.2 ∈ prescribedPairEndpoints pairs := by
      rw [prescribedPairEndpoints, List.mem_flatMap]
      exact ⟨p, hp, by simp⟩
    constructor
    · exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hbOld (h ▸ hp1)) (fun h => hcOld (h ▸ hp1))
    · exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hbOld (h ▸ hp2)) (fun h => hcOld (h ▸ hp2))
  apply Finset.card_bij'
      (fun sigma _ => tau * sigma)
      (fun rho _ => tau * rho)
  · intro sigma hsigma
    rw [mem_conjugatePairsEvent] at hsigma ⊢
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with hpHead | hpOld
    · rcases hpHead with ⟨rfl, rfl⟩
      calc
        conjugatedPartner pairing (tau * sigma) a =
            conjugatedPartner pairing (tau * sigma) (tau a) := by rw [htauA]
        _ = tau (conjugatedPartner pairing sigma a) :=
          conjugatedPartner_mul pairing sigma tau a
        _ = tau b := by rw [hsigma (a, b) (by simp)]
        _ = c := by simp [tau]
    · obtain ⟨hp1, hp2⟩ := htauOld p hpOld
      calc
        conjugatedPartner pairing (tau * sigma) p.1 =
            conjugatedPartner pairing (tau * sigma) (tau p.1) := by rw [hp1]
        _ = tau (conjugatedPartner pairing sigma p.1) :=
          conjugatedPartner_mul pairing sigma tau p.1
        _ = tau p.2 := by rw [hsigma p (by simp [hpOld])]
        _ = p.2 := hp2
  · intro rho hrho
    rw [mem_conjugatePairsEvent] at hrho ⊢
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with hpHead | hpOld
    · rcases hpHead with ⟨rfl, rfl⟩
      calc
        conjugatedPartner pairing (tau * rho) a =
            conjugatedPartner pairing (tau * rho) (tau a) := by rw [htauA]
        _ = tau (conjugatedPartner pairing rho a) :=
          conjugatedPartner_mul pairing rho tau a
        _ = tau c := by rw [hrho (a, c) (by simp)]
        _ = b := by simp [tau]
    · obtain ⟨hp1, hp2⟩ := htauOld p hpOld
      calc
        conjugatedPartner pairing (tau * rho) p.1 =
            conjugatedPartner pairing (tau * rho) (tau p.1) := by rw [hp1]
        _ = tau (conjugatedPartner pairing rho p.1) :=
          conjugatedPartner_mul pairing rho tau p.1
        _ = tau p.2 := by rw [hrho p (by simp [hpOld])]
        _ = p.2 := hp2
  · intro sigma hsigma
    simp [tau]
  · intro rho hrho
    simp [tau]

/-- Exact one-step exposure recursion for simultaneous prescribed pairs. -/
theorem card_available_mul_conjugatePairsEvent_cons
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (pairs : List (Omega × Omega)) (a b : Omega)
    (hdisjoint : (prescribedPairEndpoints ((a, b) :: pairs)).Nodup) :
    (Fintype.card Omega - (2 * pairs.length + 1)) *
        (conjugatePairsEvent pairing ((a, b) :: pairs)).card =
      (conjugatePairsEvent pairing pairs).card := by
  have hd : (a :: b :: prescribedPairEndpoints pairs).Nodup := by
    simpa using hdisjoint
  have hnodup : (prescribedPairEndpoints pairs).Nodup := hd.tail.tail
  have ha : a ∉ prescribedPairEndpoints pairs := by
    intro haMem
    exact (List.nodup_cons.mp hd).1 (by simp [haMem])
  have hab : a ≠ b := by
    exact fun h => (List.nodup_cons.mp hd).1 (by simp [h])
  have hb : b ∉ prescribedPairEndpoints pairs := by
    exact (List.nodup_cons.mp hd.tail).1
  have hbAvail : b ∈ availablePairPartners a pairs := by
    exact (mem_availablePairPartners a b pairs).2 ⟨hab.symm, hb⟩
  let partnerAt : Equiv.Perm Omega → Omega :=
    fun sigma => conjugatedPartner pairing sigma a
  have hmaps : Set.MapsTo partnerAt
      (conjugatePairsEvent pairing pairs)
      (availablePairPartners a pairs) := by
    intro sigma hsigma
    apply (mem_availablePairPartners a _ pairs).2
    exact ⟨conjugatedPartner_ne pairing sigma hpairing_ne a,
      conjugatedPartner_not_mem_endpoints pairing sigma hpairing
        pairs a ha hsigma⟩
  have hfibers := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (c : Omega) :
      {sigma ∈ conjugatePairsEvent pairing pairs | partnerAt sigma = c} =
        conjugatePairsEvent pairing ((a, c) :: pairs) := by
    ext sigma
    simp only [Finset.mem_filter, mem_conjugatePairsEvent, List.mem_cons,
      forall_eq_or_imp, Prod.forall, partnerAt]
    tauto
  have hsum :
      (conjugatePairsEvent pairing pairs).card =
        ∑ c ∈ availablePairPartners a pairs,
          (conjugatePairsEvent pairing ((a, c) :: pairs)).card := by
    simpa only [hfiber] using hfibers
  rw [← card_availablePairPartners a pairs ha hnodup]
  calc
    (availablePairPartners a pairs).card *
          (conjugatePairsEvent pairing ((a, b) :: pairs)).card =
        ∑ c ∈ availablePairPartners a pairs,
          (conjugatePairsEvent pairing ((a, b) :: pairs)).card := by simp
    _ = ∑ c ∈ availablePairPartners a pairs,
          (conjugatePairsEvent pairing ((a, c) :: pairs)).card := by
      apply Finset.sum_congr rfl
      intro c hc
      exact conjugatePairsEvent_cons_card_eq_of_available
        pairing pairs a b c hbAvail hc
    _ = (conjugatePairsEvent pairing pairs).card := hsum.symm

/-- Odd descending denominator appearing in the `k`-pair probability. -/
def prescribedPairDenominator (N k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k, (N - (2 * j + 1))

@[simp] theorem prescribedPairDenominator_zero (N : ℕ) :
    prescribedPairDenominator N 0 = 1 := by
  simp [prescribedPairDenominator]

theorem prescribedPairDenominator_succ (N k : ℕ) :
    prescribedPairDenominator N (k + 1) =
      prescribedPairDenominator N k * (N - (2 * k + 1)) := by
  simp [prescribedPairDenominator, Finset.prod_range_succ]

/-- Integer cardinality identity for `k` simultaneous disjoint prescribed
pairs. -/
theorem prescribedPairDenominator_mul_event_card
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (pairs : List (Omega × Omega))
    (hdisjoint : (prescribedPairEndpoints pairs).Nodup) :
    prescribedPairDenominator (Fintype.card Omega) pairs.length *
        (conjugatePairsEvent pairing pairs).card =
      Fintype.card (Equiv.Perm Omega) := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
      rcases p with ⟨a, b⟩
      have htail : (prescribedPairEndpoints pairs).Nodup := by
        simpa using hdisjoint.tail.tail
      have hstep := card_available_mul_conjugatePairsEvent_cons
        pairing hpairing hpairing_ne pairs a b hdisjoint
      rw [List.length_cons, prescribedPairDenominator_succ]
      calc
        prescribedPairDenominator (Fintype.card Omega) pairs.length *
              (Fintype.card Omega - (2 * pairs.length + 1)) *
              (conjugatePairsEvent pairing ((a, b) :: pairs)).card =
            prescribedPairDenominator (Fintype.card Omega) pairs.length *
              ((Fintype.card Omega - (2 * pairs.length + 1)) *
                (conjugatePairsEvent pairing ((a, b) :: pairs)).card) := by
                  rw [Nat.mul_assoc]
        _ = prescribedPairDenominator (Fintype.card Omega) pairs.length *
              (conjugatePairsEvent pairing pairs).card := by rw [hstep]
        _ = Fintype.card (Equiv.Perm Omega) := ih htail

theorem prescribedPairDenominator_pos
    {Omega : Type*} [Fintype Omega]
    (pairs : List (Omega × Omega))
    (hdisjoint : (prescribedPairEndpoints pairs).Nodup) :
    0 < prescribedPairDenominator (Fintype.card Omega) pairs.length := by
  unfold prescribedPairDenominator
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have hlen : 2 * pairs.length ≤ Fintype.card Omega := by
    rw [← length_prescribedPairEndpoints]
    exact hdisjoint.length_le_card
  omega

/-- Under the standard exposure guard `4k ≤ N`, every odd descending
factor in the prescribed-pair denominator is at least `N/2`. -/
theorem half_card_pow_le_prescribedPairDenominator_cast
    (N k : ℕ) (hguard : 4 * k ≤ N) :
    ((N : ℝ) / 2) ^ k ≤ (prescribedPairDenominator N k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hguardTail : 4 * k ≤ N := by omega
      have hfactorNat : 2 * (2 * k + 1) ≤ N := by omega
      have hfactor : (N : ℝ) / 2 ≤ (N - (2 * k + 1) : ℕ) := by
        have hcast : (2 * (2 * k + 1) : ℝ) ≤ N := by exact_mod_cast hfactorNat
        have hsub : ((N - (2 * k + 1) : ℕ) : ℝ) =
            (N : ℝ) - (2 * k + 1 : ℕ) := by
          rw [Nat.cast_sub (by omega)]
        have hkcast : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by
          push_cast
          rfl
        rw [hsub, hkcast]
        linarith [hcast]
      rw [prescribedPairDenominator_succ, Nat.cast_mul, pow_succ]
      exact mul_le_mul (ih hguardTail) hfactor (by positivity) (by positivity)

theorem prescribedPairDenominator_inv_le_two_div_pow
    (N k : ℕ) (hN : 0 < N) (hguard : 4 * k ≤ N) :
    ((prescribedPairDenominator N k : ℕ) : ℝ)⁻¹ ≤
      (2 / (N : ℝ)) ^ k := by
  have hhalf : 0 < ((N : ℝ) / 2) ^ k := by positivity
  rw [show ((prescribedPairDenominator N k : ℕ) : ℝ)⁻¹ =
      1 / (prescribedPairDenominator N k : ℝ) by simp [one_div]]
  calc
    1 / (prescribedPairDenominator N k : ℝ) ≤
        1 / (((N : ℝ) / 2) ^ k) :=
      one_div_le_one_div_of_le hhalf
        (half_card_pow_le_prescribedPairDenominator_cast N k hguard)
    _ = (2 / (N : ℝ)) ^ k := by
      rw [one_div, ← inv_pow]
      congr 1
      field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']

/-- Exact probability product for `k` disjoint prescribed pairs under a
uniformly conjugated fixed-point-free involution. -/
theorem uniform_prob_conjugatePairsEvent
    {Omega : Type*} [Fintype Omega]
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (pairs : List (Omega × Omega))
    (hdisjoint : (prescribedPairEndpoints pairs).Nodup) :
    (FiniteLaw.uniform : FiniteLaw (Equiv.Perm Omega)).prob
        (conjugatePairsEvent pairing pairs) =
      ((prescribedPairDenominator (Fintype.card Omega) pairs.length : ℕ) : ℝ)⁻¹ := by
  rw [FiniteLaw.uniform_prob]
  have hdenNat := prescribedPairDenominator_pos pairs hdisjoint
  have hden :
      ((prescribedPairDenominator (Fintype.card Omega) pairs.length : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  have hperm : (Fintype.card (Equiv.Perm Omega) : ℝ) ≠ 0 := by positivity
  have hcount := prescribedPairDenominator_mul_event_card
    pairing hpairing hpairing_ne pairs hdisjoint
  have hcountReal :
      ((prescribedPairDenominator (Fintype.card Omega) pairs.length : ℕ) : ℝ) *
          ((conjugatePairsEvent pairing pairs).card : ℝ) =
        (Fintype.card (Equiv.Perm Omega) : ℝ) := by
    exact_mod_cast hcount
  field_simp
  nlinarith

/-- Finite union bound for a family of `k`-pair witnesses indexed by a
finite type.  Dense-subset, cycle, and defect witnesses can all be encoded
in this form. -/
theorem uniform_prob_univ_biUnion_conjugatePairsEvent_le
    {Omega I : Type*} [Fintype Omega] [Fintype I]
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (pairs : I → List (Omega × Omega)) (k : ℕ)
    (hlength : ∀ i, (pairs i).length = k)
    (hdisjoint : ∀ i, (prescribedPairEndpoints (pairs i)).Nodup) :
    (FiniteLaw.uniform : FiniteLaw (Equiv.Perm Omega)).prob
        (Finset.univ.biUnion fun i => conjugatePairsEvent pairing (pairs i)) ≤
      (Fintype.card I : ℝ) *
        ((prescribedPairDenominator (Fintype.card Omega) k : ℕ) : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ i,
        (FiniteLaw.uniform : FiniteLaw (Equiv.Perm Omega)).prob
          (conjugatePairsEvent pairing (pairs i)) :=
      FiniteLaw.prob_biUnion_le _ _
    _ = ∑ _i : I,
        ((prescribedPairDenominator (Fintype.card Omega) k : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [uniform_prob_conjugatePairsEvent pairing hpairing hpairing_ne
        (pairs i) (hdisjoint i), hlength i]
    _ = _ := by simp

/-- Simultaneous prescribed-pair event specialized to the configuration
model's labelled half-edges. -/
noncomputable def configurationPairsEvent
    (m d : ℕ)
    (pairs : List
      (ConfigurationHalfEdge m (d + d) × ConfigurationHalfEdge m (d + d))) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  conjugatePairsEvent (Configuration.standardConfiguration m d).partner pairs

@[simp] theorem mem_configurationPairsEvent
    (m d : ℕ)
    (pairs : List
      (ConfigurationHalfEdge m (d + d) × ConfigurationHalfEdge m (d + d)))
    (sigma : Equiv.Perm (ConfigurationHalfEdge m (d + d))) :
    sigma ∈ configurationPairsEvent m d pairs ↔
      ∀ p ∈ pairs, (randomConfiguration m d sigma).partner p.1 = p.2 := by
  simp [configurationPairsEvent]

set_option maxHeartbeats 1000000 in
/-- Exact product formula specialized to the `D=2d` configuration model.
The larger heartbeat allowance is confined to elaborating this wrapper once;
downstream cycle and defect modules can then use its compact signature. -/
theorem configurationPermutationLaw_prob_configurationPairsEvent
    (m d : ℕ)
    (pairs : List
      (ConfigurationHalfEdge m (d + d) × ConfigurationHalfEdge m (d + d)))
    (hdisjoint : (prescribedPairEndpoints pairs).Nodup) :
    (configurationPermutationLaw m d).prob
        (configurationPairsEvent m d pairs) =
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ)⁻¹ := by
  unfold configurationPermutationLaw
  rw [FiniteLaw.uniform_prob]
  rw [← Nat.card_eq_fintype_card]
  have hdenNat :
      0 < prescribedPairDenominator (m * (d + d)) pairs.length := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      prescribedPairDenominator_pos pairs hdisjoint
  have hden :
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  have hperm :
      (Nat.card
        (Equiv.Perm (ConfigurationHalfEdge m (d + d))) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos
      (α := Equiv.Perm (ConfigurationHalfEdge m (d + d)))).ne'
  have hcount := prescribedPairDenominator_mul_event_card
    (Configuration.standardConfiguration m d).partner
    (Configuration.standardConfiguration m d).partner_involutive
    (Configuration.standardConfiguration m d).partner_ne
    pairs hdisjoint
  have hcountInvariant :
      prescribedPairDenominator (m * (d + d)) pairs.length *
          (configurationPairsEvent m d pairs).card =
        Nat.card (Equiv.Perm (ConfigurationHalfEdge m (d + d))) := by
    have hcountNat := hcount
    simp only [← Nat.card_eq_fintype_card] at hcountNat
    simpa only [configurationPairsEvent, Nat.card_prod,
      Nat.card_fin] using hcountNat
  have hcountReal :
      ((prescribedPairDenominator (m * (d + d)) pairs.length : ℕ) : ℝ) *
          ((configurationPairsEvent m d pairs).card : ℝ) =
        (Nat.card
          (Equiv.Perm (ConfigurationHalfEdge m (d + d))) : ℝ) := by
    exact_mod_cast hcountInvariant
  apply (div_eq_iff hperm).2
  rw [inv_mul_eq_div]
  field_simp [hden] at hcountReal ⊢
  nlinarith

/-! ## Finite socket witnesses for dense induced subgraphs -/

/-- Vertex subsets of cardinality `s`, represented as a finite type. -/
abbrev ConfigurationVertexSet (m s : ℕ) :=
  {U : Finset (Fin m) // U ∈ vertexSubsets m s}

/-- Collections of `k` distinct ambient vertex-edges supported on `U`. -/
abbrev ConfigurationVertexEdgeSet {m s : ℕ}
    (U : ConfigurationVertexSet m s) (k : ℕ) :=
  {A : Finset (AmbientEdge m) //
    A ∈ (ambientEdgesOn U.1).powersetCard k}

/-- A finite union-bound witness: a size-`s` vertex set, `k` distinct
vertex-edges on that set, and one ordered choice of a `D`-socket at each
endpoint of every edge. -/
abbrev ConfigurationSocketWitness (m D s k : ℕ) :=
  Σ U : ConfigurationVertexSet m s,
    Σ A : ConfigurationVertexEdgeSet U k,
      A.1 → Fin D × Fin D

/-- The prescribed half-edge pairs associated with a socket witness. -/
noncomputable def ConfigurationSocketWitness.pairs
    {m D s k : ℕ} (W : ConfigurationSocketWitness m D s k) :
    List (ConfigurationHalfEdge m D × ConfigurationHalfEdge m D) :=
  (Finset.univ : Finset W.2.1).toList.map fun e =>
    (((e.1.1.out.1, (W.2.2 e).1),
      (e.1.1.out.2, (W.2.2 e).2)))

@[simp] theorem ConfigurationSocketWitness.length_pairs
    {m D s k : ℕ} (W : ConfigurationSocketWitness m D s k) :
    W.pairs.length = k := by
  rw [ConfigurationSocketWitness.pairs, List.length_map,
    Finset.length_toList, Finset.card_univ, Fintype.card_coe]
  exact (Finset.mem_powersetCard.mp W.2.1.2).2

/-- The number of socket witnesses is exactly the elementary union-bound
count `choose(m,s) * choose(choose(s,2),k) * D^(2k)`. -/
theorem card_configurationSocketWitness (m D s k : ℕ) :
    Fintype.card (ConfigurationSocketWitness m D s k) =
      m.choose s * (s.choose 2).choose k * (D * D) ^ k := by
  classical
  simp only [ConfigurationSocketWitness, ConfigurationVertexSet,
    ConfigurationVertexEdgeSet, Fintype.card_sigma]
  calc
    (∑ U : { U // U ∈ vertexSubsets m s },
        ∑ A : { A // A ∈ (ambientEdgesOn U.1).powersetCard k },
          Fintype.card (A.1 → Fin D × Fin D)) =
      ∑ _U : { U // U ∈ vertexSubsets m s },
        ∑ _A : { A // A ∈
            (ambientEdgesOn (show Finset (Fin m) from _U.1)).powersetCard k },
          (D * D) ^ k := by
      apply Finset.sum_congr rfl
      intro U _hU
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_coe]
      congr 1
      exact (Finset.mem_powersetCard.mp A.2).2
    _ = m.choose s * (s.choose 2).choose k * (D * D) ^ k := by
      have hUcard : ∀ U : { U // U ∈ vertexSubsets m s }, U.1.card = s := by
        intro U
        exact (Finset.mem_powersetCard.mp U.2).2
      simp [hUcard, card_vertexSubsets, Nat.mul_assoc]

/-- Socket witnesses with no repeated half-edge endpoint.  Only these can
occur in a perfect matching; retaining them as a subtype can only decrease
the union-bound witness count. -/
abbrev DisjointConfigurationSocketWitness (m D s k : ℕ) :=
  {W : ConfigurationSocketWitness m D s k //
    (prescribedPairEndpoints W.pairs).Nodup}

theorem card_disjointConfigurationSocketWitness_le (m D s k : ℕ) :
    Fintype.card (DisjointConfigurationSocketWitness m D s k) ≤
      m.choose s * (s.choose 2).choose k * (D * D) ^ k := by
  rw [← card_configurationSocketWitness]
  exact Fintype.card_subtype_le _

/-- Union of all disjoint socket-witness events at a fixed vertex-set size
and edge threshold. -/
noncomputable def configurationSocketWitnessUnionEvent
    (m d s k : ℕ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  Finset.univ.biUnion fun W :
      DisjointConfigurationSocketWitness m (d + d) s k =>
    configurationPairsEvent m d W.1.pairs

/-- Paper-facing fixed-size finite union bound.  The first two factors
enumerate the vertex set and its distinct vertex edges, the socket power
chooses one configuration half-edge at each endpoint, and the last factor
is the exact odd descending matching probability. -/
theorem configurationPermutationLaw_prob_socketWitnessUnionEvent_le
    (m d s k : ℕ) :
    (configurationPermutationLaw m d).prob
        (configurationSocketWitnessUnionEvent m d s k) ≤
      (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) *
        (((d + d) * (d + d) : ℕ) : ℝ) ^ k *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
  unfold configurationSocketWitnessUnionEvent
  calc
    _ ≤ ∑ W : DisjointConfigurationSocketWitness m (d + d) s k,
        (configurationPermutationLaw m d).prob
          (configurationPairsEvent m d W.1.pairs) :=
      FiniteLaw.prob_biUnion_le _ _
    _ = ∑ _W : DisjointConfigurationSocketWitness m (d + d) s k,
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro W _hW
      rw [configurationPermutationLaw_prob_configurationPairsEvent
        m d W.1.pairs W.2, W.1.length_pairs]
    _ = (Fintype.card
          (DisjointConfigurationSocketWitness m (d + d) s k) : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
      simp
    _ ≤ ((m.choose s * (s.choose 2).choose k *
          (((d + d) * (d + d)) ^ k) : ℕ) : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_disjointConfigurationSocketWitness_le
          m (d + d) s k
      · positivity
    _ = _ := by
      push_cast
      ring

/-- Distinct blocks of a fixed-point-free involution have disjoint endpoint
lists.  This converts injectivity of unordered matching blocks into the
`Nodup` premise of the exact prescribed-pair theorem. -/
theorem nodup_prescribedPairEndpoints_of_pairBlock_injective_list
    {I Omega : Type*}
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (indices : List I) (hindices : indices.Nodup)
    (first : I → Omega)
    (hinjective : Function.Injective fun i => s(first i, pairing (first i))) :
    (prescribedPairEndpoints
      (indices.map fun i =>
        (first i, pairing (first i)))).Nodup := by
  rw [prescribedPairEndpoints, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    simpa [eq_comm] using hpairing_ne (first i)
  · refine hindices.imp ?_
    intro i j hij
    change List.Disjoint [first i, pairing (first i)]
      [first j, pairing (first j)]
    rw [List.disjoint_left]
    intro x hxi hxj
    simp at hxi hxj
    apply hij
    apply hinjective
    change s(first i, pairing (first i)) =
      s(first j, pairing (first j))
    rcases hxi with rfl | rfl <;> rcases hxj with h | h
    · rw [h]
    · rw [h, hpairing]
      exact Sym2.eq_swap
    · rw [← h, hpairing]
      exact Sym2.eq_swap
    · have hfirst : first i = first j := pairing.injective h
      rw [hfirst]

theorem nodup_prescribedPairEndpoints_of_pairBlock_injective
    {I Omega : Type*} [Fintype I]
    (pairing : Equiv.Perm Omega)
    (hpairing : Function.Involutive pairing)
    (hpairing_ne : ∀ a, pairing a ≠ a)
    (first : I → Omega)
    (hinjective : Function.Injective fun i => s(first i, pairing (first i))) :
    (prescribedPairEndpoints
      ((Finset.univ : Finset I).toList.map fun i =>
        (first i, pairing (first i)))).Nodup :=
  nodup_prescribedPairEndpoints_of_pairBlock_injective_list
    pairing hpairing hpairing_ne _ (Finset.nodup_toList _) first hinjective

/-- Vertex edges of the projected simple graph whose endpoints both lie in
`U`, represented in the ambient complete-graph edge type. -/
noncomputable def configurationProjectedEdgesOn
    {m D : ℕ} (C : Configuration m D) (U : Finset (Fin m)) :
    Finset (AmbientEdge m) :=
  (ambientEdgesOn U).filter fun e =>
    C.projectedGraph.Adj e.1.out.1 e.1.out.2

theorem mem_ambientEdgesOn_iff_endpoints_mem
    {m : ℕ} (U : Finset (Fin m)) (e : AmbientEdge m) :
    e ∈ ambientEdgesOn U ↔ e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U := by
  simp only [ambientEdgesOn, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    change ((Sym2.map (fun u : U => u.1) a.1).out.1 ∈ U) ∧
      ((Sym2.map (fun u : U => u.1) a.1).out.2 ∈ U)
    have hout := (Sym2.map (fun u : U => u.1) a.1).out_eq
    induction a.1 using Sym2.ind with
    | _ u v =>
      constructor
      · have hmem := Sym2.out_fst_mem s((u : Fin m), (v : Fin m))
        rw [Sym2.mem_iff] at hmem
        rcases hmem with hmem | hmem
        · simpa [hmem] using u.2
        · simpa [hmem] using v.2
      · have hmem := Sym2.out_snd_mem s((u : Fin m), (v : Fin m))
        rw [Sym2.mem_iff] at hmem
        rcases hmem with hmem | hmem
        · simpa [hmem] using u.2
        · simpa [hmem] using v.2
  · intro he
    let u : U := ⟨e.1.out.1, he.1⟩
    let v : U := ⟨e.1.out.2, he.2⟩
    have huv : u ≠ v := by
      intro h
      have houtEq : e.1.out.1 = e.1.out.2 := congrArg Subtype.val h
      have hnotdiag := (⊤ : SimpleGraph (Fin m)).not_isDiag_of_mem_edgeSet e.2
      rw [← e.1.out_eq, Sym2.mk_isDiag_iff] at hnotdiag
      exact hnotdiag houtEq
    let a : (⊤ : SimpleGraph U).edgeSet :=
      ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := (⊤ : SimpleGraph U))).2
        ((SimpleGraph.top_adj _ _).2 huv)⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change Sym2.map (fun x : U => x.1) s(u, v) = e.1
    rw [Sym2.map_pair_eq]
    exact e.1.out_eq

/-- Fixed-size local-density failure event for the projected graph. -/
noncomputable def configurationLocalBadEventAtSize
    (m d s k : ℕ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  FiniteLaw.event fun sigma =>
    ∃ U : Finset (Fin m), U.card = s ∧
      k ≤ (configurationProjectedEdgesOn
        (randomConfiguration m d sigma) U).card

/-- Every fixed-size projected-graph density failure supplies a disjoint
socket witness. -/
theorem configurationLocalBadEventAtSize_subset_socketWitnessUnionEvent
    (m d s k : ℕ) :
    configurationLocalBadEventAtSize m d s k ⊆
      configurationSocketWitnessUnionEvent m d s k := by
  classical
  intro sigma hsigma
  rw [configurationLocalBadEventAtSize, FiniteLaw.mem_event] at hsigma
  rcases hsigma with ⟨U, hUcard, hk⟩
  let C : Configuration m (d + d) := randomConfiguration m d sigma
  let present : Finset (AmbientEdge m) := configurationProjectedEdgesOn C U
  obtain ⟨A, hApresent, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := present) hk
  let Us : ConfigurationVertexSet m s :=
    ⟨U, by
      rw [vertexSubsets, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ U, hUcard⟩⟩
  have hAambient : A ⊆ ambientEdgesOn U := by
    intro e he
    exact (Finset.mem_filter.mp (hApresent he)).1
  let As : ConfigurationVertexEdgeSet Us k :=
    ⟨A, by
      rw [Finset.mem_powersetCard]
      exact ⟨hAambient, hAcard⟩⟩
  have hedge (e : As.1) :
      C.projectedGraph.Adj e.1.1.out.1 e.1.1.out.2 := by
    exact (Finset.mem_filter.mp (hApresent e.2)).2
  let firstSocket : As.1 → Fin (d + d) :=
    fun e => Classical.choose ((C.projectedGraph_adj _ _).mp (hedge e)).2
  have hfirstSocket (e : As.1) :
      C.socketNeighbor e.1.1.out.1 (firstSocket e) = e.1.1.out.2 :=
    Classical.choose_spec ((C.projectedGraph_adj _ _).mp (hedge e)).2
  let sockets : As.1 → Fin (d + d) × Fin (d + d) :=
    fun e =>
      (firstSocket e,
        (C.partner (e.1.1.out.1, firstSocket e)).2)
  let W : ConfigurationSocketWitness m (d + d) s k :=
    ⟨Us, As, sockets⟩
  let first : As.1 → ConfigurationHalfEdge m (d + d) :=
    fun e => (e.1.1.out.1, firstSocket e)
  have hpartner (e : As.1) :
      C.partner (first e) =
        (e.1.1.out.2, (sockets e).2) := by
    apply Prod.ext
    · exact hfirstSocket e
    · rfl
  have hblockInjective : Function.Injective fun e : As.1 =>
      s(first e, C.partner (first e)) := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    rw [← e.1.1.out_eq, ← f.1.1.out_eq]
    have hmapped := congrArg (Sym2.map Configuration.vertex) hef
    simpa only [Sym2.map_mk, hpartner, first, Configuration.vertex] using hmapped
  have hgeneric :
      (prescribedPairEndpoints
        ((Finset.univ : Finset As.1).toList.map fun e =>
          (first e, C.partner (first e)))).Nodup :=
    nodup_prescribedPairEndpoints_of_pairBlock_injective
      C.partner C.partner_involutive C.partner_ne first hblockInjective
  have hpairs : W.pairs =
      (Finset.univ : Finset As.1).toList.map fun e =>
        (first e, C.partner (first e)) := by
    unfold W ConfigurationSocketWitness.pairs
    apply List.map_congr_left
    intro e he
    apply Prod.ext
    · rfl
    · exact hpartner e |>.symm
  have hWdisjoint : (prescribedPairEndpoints W.pairs).Nodup := by
    rw [hpairs]
    exact hgeneric
  let Wgood : DisjointConfigurationSocketWitness m (d + d) s k :=
    ⟨W, hWdisjoint⟩
  rw [configurationSocketWitnessUnionEvent, Finset.mem_biUnion]
  refine ⟨Wgood, Finset.mem_univ _, ?_⟩
  rw [mem_configurationPairsEvent]
  intro p hp
  rw [hpairs] at hp
  rcases List.mem_map.mp hp with ⟨e, he, rfl⟩
  change C.partner (first e) = C.partner (first e)
  rfl

/-- The finite probability estimate for a fixed vertex-set size, now stated
for the actual projected configuration graph. -/
theorem configurationPermutationLaw_prob_localBadEventAtSize_le
    (m d s k : ℕ) :
    (configurationPermutationLaw m d).prob
        (configurationLocalBadEventAtSize m d s k) ≤
      (m.choose s : ℝ) * ((s.choose 2).choose k : ℝ) *
        (((d + d) * (d + d) : ℕ) : ℝ) ^ k *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
  exact ((configurationPermutationLaw m d).prob_mono
    (configurationLocalBadEventAtSize_subset_socketWitnessUnionEvent
      m d s k)).trans
    (configurationPermutationLaw_prob_socketWitnessUnionEvent_le m d s k)

/-! ## Exact multigraph internal-edge witnesses -/

/-- Half-edges incident to a specified vertex set. -/
abbrev ConfigurationHalfEdgeOn
    {m s : ℕ} (U : ConfigurationVertexSet m s) (D : ℕ) :=
  {h : ConfigurationHalfEdge m D // h.1 ∈ U.1}

/-- The evident equivalence between half-edges on `U` and `U × Fin D`. -/
def configurationHalfEdgeOnEquiv
    {m s D : ℕ} (U : ConfigurationVertexSet m s) :
    ConfigurationHalfEdgeOn U D ≃ U.1 × Fin D where
  toFun h := (⟨h.1.1, h.2⟩, h.1.2)
  invFun p := ⟨(p.1.1, p.2), p.1.2⟩
  left_inv h := by cases h; rfl
  right_inv p := by cases p with | mk u i => cases u; rfl

@[simp] theorem card_configurationHalfEdgeOn
    {m s D : ℕ} (U : ConfigurationVertexSet m s) :
    Fintype.card (ConfigurationHalfEdgeOn U D) = s * D := by
  rw [Fintype.card_congr (configurationHalfEdgeOnEquiv U),
    Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
  rw [(Finset.mem_powersetCard.mp U.2).2]

/-- All `k`-subsets of the possible off-diagonal socket pairs on `U`. -/
abbrev ConfigurationInternalPairSet
    {m s : ℕ} (U : ConfigurationVertexSet m s) (D k : ℕ) :=
  {A : Finset (Sym2 (ConfigurationHalfEdgeOn U D)) //
    A ∈ (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)).edgeFinset.powersetCard k}

/-- A multigraph internal-edge union-bound witness. -/
abbrev ConfigurationInternalPairWitness (m D s k : ℕ) :=
  Σ U : ConfigurationVertexSet m s,
    ConfigurationInternalPairSet U D k

/-- Orient each socket pair canonically and forget the proof that its
endpoints lie over `U`. -/
noncomputable def ConfigurationInternalPairWitness.pairs
    {m D s k : ℕ} (W : ConfigurationInternalPairWitness m D s k) :
    List (ConfigurationHalfEdge m D × ConfigurationHalfEdge m D) :=
  (Finset.univ : Finset W.2.1).toList.map fun e =>
    (e.1.out.1.1, e.1.out.2.1)

@[simp] theorem ConfigurationInternalPairWitness.length_pairs
    {m D s k : ℕ} (W : ConfigurationInternalPairWitness m D s k) :
    W.pairs.length = k := by
  rw [ConfigurationInternalPairWitness.pairs, List.length_map,
    Finset.length_toList, Finset.card_univ, Fintype.card_coe]
  exact (Finset.mem_powersetCard.mp W.2.2).2

theorem card_configurationInternalPairWitness (m D s k : ℕ) :
    Fintype.card (ConfigurationInternalPairWitness m D s k) =
      m.choose s * ((s * D).choose 2).choose k := by
  classical
  simp only [ConfigurationInternalPairWitness, ConfigurationInternalPairSet,
    ConfigurationVertexSet, Fintype.card_sigma]
  calc
    (∑ U : { U // U ∈ vertexSubsets m s },
        Fintype.card { A // A ∈
          (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)).edgeFinset.powersetCard k }) =
      ∑ _U : { U // U ∈ vertexSubsets m s },
        ((s * D).choose 2).choose k := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Fintype.card_coe, Finset.card_powersetCard,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
        card_configurationHalfEdgeOn]
    _ = _ := by
      simp [card_vertexSubsets]

/-- Disjoint multigraph-pair witnesses.  Perfect matchings can realize only
this subtype. -/
abbrev DisjointConfigurationInternalPairWitness (m D s k : ℕ) :=
  {W : ConfigurationInternalPairWitness m D s k //
    (prescribedPairEndpoints W.pairs).Nodup}

theorem card_disjointConfigurationInternalPairWitness_le (m D s k : ℕ) :
    Fintype.card (DisjointConfigurationInternalPairWitness m D s k) ≤
      m.choose s * ((s * D).choose 2).choose k := by
  rw [← card_configurationInternalPairWitness]
  exact Fintype.card_subtype_le _

noncomputable def configurationInternalPairWitnessUnionEvent
    (m d s k : ℕ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  Finset.univ.biUnion fun W :
      DisjointConfigurationInternalPairWitness m (d + d) s k =>
    configurationPairsEvent m d W.1.pairs

theorem configurationPermutationLaw_prob_internalPairWitnessUnionEvent_le
    (m d s k : ℕ) :
    (configurationPermutationLaw m d).prob
        (configurationInternalPairWitnessUnionEvent m d s k) ≤
      (m.choose s : ℝ) * (((s * (d + d)).choose 2).choose k : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
  unfold configurationInternalPairWitnessUnionEvent
  calc
    _ ≤ ∑ W : DisjointConfigurationInternalPairWitness m (d + d) s k,
        (configurationPermutationLaw m d).prob
          (configurationPairsEvent m d W.1.pairs) :=
      FiniteLaw.prob_biUnion_le _ _
    _ = ∑ _W : DisjointConfigurationInternalPairWitness m (d + d) s k,
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro W _hW
      rw [configurationPermutationLaw_prob_configurationPairsEvent
        m d W.1.pairs W.2, W.1.length_pairs]
    _ = (Fintype.card
          (DisjointConfigurationInternalPairWitness m (d + d) s k) : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by simp
    _ ≤ ((m.choose s * (((s * (d + d)).choose 2).choose k) : ℕ) : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_disjointConfigurationInternalPairWitness_le
          m (d + d) s k
      · positivity
    _ = _ := by push_cast; ring

/-- Matching blocks with both half-edge endpoints incident to `U`.  Its
cardinality is exactly the number of edges of the induced configuration
multigraph, with loops and parallel edges counted with multiplicity. -/
noncomputable def configurationInternalPairBlocks
    {m D s : ℕ} (C : Configuration m D)
    (U : ConfigurationVertexSet m s) :
    Finset (Sym2 (ConfigurationHalfEdgeOn U D)) :=
  (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)).edgeFinset.filter fun e =>
    C.partner e.out.1.1 = e.out.2.1

noncomputable def configurationInternalPairCount
    {m D s : ℕ} (C : Configuration m D)
    (U : ConfigurationVertexSet m s) : ℕ :=
  (configurationInternalPairBlocks C U).card

@[simp] theorem mem_configurationInternalPairBlocks
    {m D s : ℕ} (C : Configuration m D)
    (U : ConfigurationVertexSet m s)
    (e : Sym2 (ConfigurationHalfEdgeOn U D)) :
    e ∈ configurationInternalPairBlocks C U ↔
      e ∈ (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)).edgeFinset ∧
        C.partner e.out.1.1 = e.out.2.1 := by
  simp [configurationInternalPairBlocks]

/-- Fixed-size failure event for the actual configuration multigraph. -/
noncomputable def configurationInternalLocalBadEventAtSize
    (m d s k : ℕ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  FiniteLaw.event fun sigma =>
    ∃ U : ConfigurationVertexSet m s,
      k ≤ configurationInternalPairCount (randomConfiguration m d sigma) U

/-- A dense induced configuration multigraph supplies a disjoint family of
`k` realized socket pairs. -/
theorem configurationInternalLocalBadEventAtSize_subset_witnessUnionEvent
    (m d s k : ℕ) :
    configurationInternalLocalBadEventAtSize m d s k ⊆
      configurationInternalPairWitnessUnionEvent m d s k := by
  classical
  intro sigma hsigma
  rw [configurationInternalLocalBadEventAtSize, FiniteLaw.mem_event] at hsigma
  rcases hsigma with ⟨U, hk⟩
  let C : Configuration m (d + d) := randomConfiguration m d sigma
  let present := configurationInternalPairBlocks C U
  obtain ⟨A, hApresent, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := present) hk
  let As : ConfigurationInternalPairSet U (d + d) k :=
    ⟨A, by
      rw [Finset.mem_powersetCard]
      exact ⟨fun e he =>
        (Finset.mem_filter.mp (hApresent he)).1, hAcard⟩⟩
  let W : ConfigurationInternalPairWitness m (d + d) s k := ⟨U, As⟩
  have hactual (e : As.1) :
      C.partner e.1.out.1.1 = e.1.out.2.1 :=
    (Finset.mem_filter.mp (hApresent e.2)).2
  let first : As.1 → ConfigurationHalfEdge m (d + d) :=
    fun e => e.1.out.1.1
  have hblockInjective : Function.Injective fun e : As.1 =>
      s(first e, C.partner (first e)) := by
    intro e f hef
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    calc
      Sym2.map Subtype.val e.1 =
          s(first e, C.partner (first e)) := by
        rw [← e.1.out_eq, Sym2.map_pair_eq, hactual]
      _ = s(first f, C.partner (first f)) := hef
      _ = Sym2.map Subtype.val f.1 := by
        rw [← f.1.out_eq, Sym2.map_pair_eq, hactual]
  have hgeneric :
      (prescribedPairEndpoints
        ((Finset.univ : Finset As.1).toList.map fun e =>
          (first e, C.partner (first e)))).Nodup :=
    nodup_prescribedPairEndpoints_of_pairBlock_injective
      C.partner C.partner_involutive C.partner_ne first hblockInjective
  have hpairs : W.pairs =
      (Finset.univ : Finset As.1).toList.map fun e =>
        (first e, C.partner (first e)) := by
    unfold W ConfigurationInternalPairWitness.pairs
    apply List.map_congr_left
    intro e he
    apply Prod.ext
    · rfl
    · exact (hactual e).symm
  have hWdisjoint : (prescribedPairEndpoints W.pairs).Nodup := by
    rw [hpairs]
    exact hgeneric
  let Wgood : DisjointConfigurationInternalPairWitness m (d + d) s k :=
    ⟨W, hWdisjoint⟩
  rw [configurationInternalPairWitnessUnionEvent, Finset.mem_biUnion]
  refine ⟨Wgood, Finset.mem_univ _, ?_⟩
  rw [mem_configurationPairsEvent]
  intro p hp
  rw [hpairs] at hp
  rcases List.mem_map.mp hp with ⟨e, he, rfl⟩
  change C.partner (first e) = C.partner (first e)
  rfl

/-- Exact fixed-size union bound in the notation of manuscript Lemma A.4. -/
theorem configurationPermutationLaw_prob_internalLocalBadEventAtSize_le
    (m d s k : ℕ) :
    (configurationPermutationLaw m d).prob
        (configurationInternalLocalBadEventAtSize m d s k) ≤
      (m.choose s : ℝ) * (((s * (d + d)).choose 2).choose k : ℝ) *
        ((prescribedPairDenominator (m * (d + d)) k : ℕ) : ℝ)⁻¹ := by
  exact ((configurationPermutationLaw m d).prob_mono
    (configurationInternalLocalBadEventAtSize_subset_witnessUnionEvent
      m d s k)).trans
    (configurationPermutationLaw_prob_internalPairWitnessUnionEvent_le
      m d s k)

/-- Stirling bound for choosing `k` socket pairs among the `sD` half-edges
over a fixed vertex set.  The assumption `s ≤ k` supplies the factorial
gain that changes the naive quadratic `s²` factor into a linear one. -/
theorem choose_mul_chooseTwo_cast_le_exp_degree_sq_mul_half_pow
    (D s k : ℕ) (hs : 0 < s) (hsk : s ≤ k) :
    (((s * D).choose 2).choose k : ℝ) ≤
      (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) ^ k := by
  have hk : 0 < k := hs.trans_le hsk
  refine (natChoose_cast_le_exp_mul_div_pow ((s * D).choose 2) k hk).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hkreal).2
  have hx : 0 ≤ ((s : ℝ) * (D : ℝ)) := by positivity
  have hchoose : (((s * D).choose 2 : ℕ) : ℝ) ≤
      (((s : ℝ) * (D : ℝ)) ^ 2) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    nlinarith
  have hskreal : (s : ℝ) ≤ k := by exact_mod_cast hsk
  calc
    Real.exp 1 * (((s * D).choose 2 : ℕ) : ℝ) ≤
        Real.exp 1 * ((((s : ℝ) * (D : ℝ)) ^ 2) / 2) := by gcongr
    _ = (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) * (s : ℝ) := by ring
    _ ≤ (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) * (k : ℝ) := by
      gcongr

/-- Normalize the exact configuration-model union term to the same
`B^s (s/m)^(k-s)` expression used by the existing two-range local-sparsity
machinery, with effective Bernoulli intensity `2D`. -/
theorem configurationInternalUnionTerm_le_base_mul_ratio_pow
    (D : ℕ) (hD : 0 < D) {m s k : ℕ}
    (hm : 0 < m) (hs : 0 < s) (hsk : s ≤ k) (hks : k ≤ 3 * s)
    (hguard : 4 * k ≤ m * D) :
    (m.choose s : ℝ) * (((s * D).choose 2).choose k : ℝ) *
        ((prescribedPairDenominator (m * D) k : ℕ) : ℝ)⁻¹ ≤
      (localSparsityBase (2 * (D : ℝ))) ^ s *
        ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
  have hchooseVertices := natChoose_cast_le_exp_mul_div_pow m s hs
  have hchoosePairs :=
    choose_mul_chooseTwo_cast_le_exp_degree_sq_mul_half_pow D s k hs hsk
  have hmD : 0 < m * D := Nat.mul_pos hm hD
  have hdenom := prescribedPairDenominator_inv_le_two_div_pow
    (m * D) k hmD hguard
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hscale :
      (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) *
          (2 / ((m * D : ℕ) : ℝ)) =
        (Real.exp 1 * (s : ℝ) / 2) *
          ((2 * (D : ℝ)) / (m : ℝ)) := by
    push_cast
    field_simp [hm0, hD0]
  have hscalePow :
      (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) ^ k *
          (2 / ((m * D : ℕ) : ℝ)) ^ k =
        (Real.exp 1 * (s : ℝ) / 2) ^ k *
          ((2 * (D : ℝ)) / (m : ℝ)) ^ k := by
    rw [← mul_pow, hscale, mul_pow]
  calc
    (m.choose s : ℝ) * (((s * D).choose 2).choose k : ℝ) *
          ((prescribedPairDenominator (m * D) k : ℕ) : ℝ)⁻¹ ≤
        (Real.exp 1 * (m : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * (D : ℝ) ^ 2 * (s : ℝ) / 2) ^ k *
            (2 / ((m * D : ℕ) : ℝ)) ^ k := by
      gcongr
    _ = (Real.exp 1 * (m : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * (s : ℝ) / 2) ^ k *
            ((2 * (D : ℝ)) / (m : ℝ)) ^ k := by
      rw [mul_assoc, hscalePow, ← mul_assoc]
    _ = (Real.exp 1) ^ s *
          (Real.exp 1 * (2 * (D : ℝ)) / 2) ^ k *
            ((s : ℝ) / (m : ℝ)) ^ (k - s) :=
      localUnionFactor_identity hm hs hsk
    _ ≤ (localSparsityBase (2 * (D : ℝ))) ^ s *
          ((s : ℝ) / (m : ℝ)) ^ (k - s) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      let L : ℝ := max 1 (Real.exp 1 * (2 * (D : ℝ)) / 2)
      have hL_one : 1 ≤ L := le_max_left _ _
      have hL_nonneg : 0 ≤ L := zero_le_one.trans hL_one
      have hC_nonneg : 0 ≤ Real.exp 1 * (2 * (D : ℝ)) / 2 := by positivity
      have hC_le : Real.exp 1 * (2 * (D : ℝ)) / 2 ≤ L := le_max_right _ _
      calc
        (Real.exp 1) ^ s *
            (Real.exp 1 * (2 * (D : ℝ)) / 2) ^ k ≤
          (Real.exp 1) ^ s * L ^ k := by gcongr
        _ ≤ (Real.exp 1) ^ s * L ^ (3 * s) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hL_one hks) (pow_nonneg (Real.exp_pos 1).le s)
        _ = (localSparsityBase (2 * (D : ℝ))) ^ s := by
          unfold localSparsityBase
          dsimp [L]
          rw [mul_pow, pow_mul]

/-- Failure of configuration-multigraph local sparsity over all vertex-set
sizes between `2` and `cutoff`. -/
noncomputable def configurationInternalLocalFailureEvent
    (n m d cutoff : ℕ) (A : ℝ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  (Finset.Icc 2 cutoff).biUnion fun s =>
    configurationInternalLocalBadEventAtSize m d s
      (localSparsityThreshold n A s)

noncomputable def configurationInternalLocalSparsityEvent
    (n m d cutoff : ℕ) (A : ℝ) :
    Finset (Equiv.Perm (ConfigurationHalfEdge m (d + d))) :=
  Finset.univ \ configurationInternalLocalFailureEvent n m d cutoff A

/-- Union bound over all admissible vertex-set sizes, before asymptotic
estimates. -/
theorem configurationPermutationLaw_prob_internalLocalFailureEvent_le
    (n m d cutoff : ℕ) (A : ℝ) :
    (configurationPermutationLaw m d).prob
        (configurationInternalLocalFailureEvent n m d cutoff A) ≤
      ∑ s ∈ Finset.Icc 2 cutoff,
        (m.choose s : ℝ) *
          (((s * (d + d)).choose 2).choose
            (localSparsityThreshold n A s) : ℝ) *
          ((prescribedPairDenominator (m * (d + d))
            (localSparsityThreshold n A s) : ℕ) : ℝ)⁻¹ := by
  unfold configurationInternalLocalFailureEvent
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 cutoff,
        (configurationPermutationLaw m d).prob
          (configurationInternalLocalBadEventAtSize m d s
            (localSparsityThreshold n A s)) :=
      FiniteLaw.prob_finset_biUnion_le
        (q := configurationPermutationLaw m d)
        (s := Finset.Icc 2 cutoff)
        (event := fun s => configurationInternalLocalBadEventAtSize m d s
          (localSparsityThreshold n A s))
    _ ≤ _ := Finset.sum_le_sum fun s _hs =>
      configurationPermutationLaw_prob_internalLocalBadEventAtSize_le
        m d s (localSparsityThreshold n A s)

/-- Abstract numerical two-range estimate.  This is the analytic core shared
by Erdős--Rényi and configuration-model local sparsity once their fixed-size
union terms have been normalized to `B^s(s/m)^(k-s)`. -/
theorem localSparsityNumericalSum_le_twoRange
    (lam r gamma : ℝ) (hr : 0 < r) (hgamma : gamma < 1)
    (n m cutoff split : ℕ) (hn : 1 < n) (hm : 0 < m)
    (hcutoffm : cutoff ≤ m)
    (hsplitLog : (split : ℝ) ≤
      localSparsityLogWindow lam * Real.log (m : ℝ))
    (hcutoffLog : ∀ s ∈ Finset.Icc 2 cutoff,
      Real.log ((s : ℝ) / (m : ℝ)) ≤
        -(1 - gamma) * Real.log (m : ℝ))
    (hlogRatio : r / 2 ≤
      Real.log (m : ℝ) / Real.log (n : ℝ))
    (hslackOne : localSparsitySlackConstant lam r gamma /
      Real.log (n : ℝ) ≤ 1)
    (term : ℕ → ℝ)
    (hterm : ∀ s ∈ Finset.Icc 2 cutoff,
      term s ≤ localSparsityBase lam ^ s *
        ((s : ℝ) / (m : ℝ)) ^
          (localSparsityThreshold n
            (localSparsitySlackConstant lam r gamma) s - s)) :
    (∑ s ∈ Finset.Icc 2 cutoff, term s) ≤
      ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) +
        2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
  classical
  let A := localSparsitySlackConstant lam r gamma
  let B := localSparsityBase lam
  let sizes := Finset.Icc 2 cutoff
  let small := sizes.filter fun s => s ≤ split
  let large := sizes.filter fun s => ¬s ≤ split
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hApos : 0 < A := localSparsitySlackConstant_pos lam hr hgamma
  have hdelta0 : 0 ≤ A / Real.log (n : ℝ) :=
    (div_pos hApos hlogn).le
  have hBpos : 0 < B := zero_lt_one.trans (one_lt_localSparsityBase lam)
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
  have hsmallTerm (s : ℕ) (hs : s ∈ small) :
      term s ≤ (split + 1 : ℝ) / Real.sqrt (m : ℝ) := by
    have hsizes : s ∈ sizes := (Finset.mem_filter.mp hs).1
    have hssplit : s ≤ split := (Finset.mem_filter.mp hs).2
    have hsm : s ≤ m := (Finset.mem_Icc.mp hsizes).2.trans hcutoffm
    have hratio0 : 0 ≤ (s : ℝ) / (m : ℝ) := by positivity
    have hratio1 : (s : ℝ) / (m : ℝ) ≤ 1 :=
      (div_le_one hmreal).2 (by exact_mod_cast hsm)
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
      term s ≤ B ^ s * ((s : ℝ) / (m : ℝ)) ^
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
    calc
      small.card ≤ (Finset.range (split + 1)).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_range]
        exact Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hs).2
      _ = split + 1 := Finset.card_range _
  have hsmallSum : (∑ s ∈ small, term s) ≤
      ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) := by
    calc
      _ ≤ ∑ _s ∈ small, (split + 1 : ℝ) / Real.sqrt (m : ℝ) :=
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
    have hsm : s ≤ m := (Finset.mem_Icc.mp hsizes).2.trans hcutoffm
    have hsreal : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hratio : (0 : ℝ) < (s : ℝ) / (m : ℝ) := div_pos hsreal hmreal
    have hratio1 : (s : ℝ) / (m : ℝ) ≤ 1 :=
      (div_le_one hmreal).2 (by exact_mod_cast hsm)
    have hlogRatioNonpos : Real.log ((s : ℝ) / (m : ℝ)) ≤ 0 :=
      Real.log_nonpos hratio.le hratio1
    let d := localSparsityThreshold n A s - s
    have hdSlack : A / Real.log (n : ℝ) * (s : ℝ) < (d : ℝ) :=
      slack_mul_lt_threshold_sub hdelta0
    have hmulSlack : (d : ℝ) * Real.log ((s : ℝ) / (m : ℝ)) ≤
        (A / Real.log (n : ℝ) * (s : ℝ)) *
          Real.log ((s : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonpos_right hdSlack.le hlogRatioNonpos
    have hdeltaS0 : 0 ≤ A / Real.log (n : ℝ) * (s : ℝ) := by positivity
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
        _ ≤ (s : ℝ) * Real.log B +
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
    have hsummable : Summable fun i : ℕ =>
        if split + 1 ≤ i then ((1 : ℝ) / 2) ^ i else 0 := by
      simpa only [← Set.piecewise_eq_indicator, one_div] using
        summable_geometric_two.indicator {i : ℕ | split + 1 ≤ i}
    calc
      _ ≤ ∑ s ∈ large, ((1 : ℝ) / 2) ^ s :=
        Finset.sum_le_sum hlargeTerm
      _ = ∑ s ∈ large,
          if split + 1 ≤ s then ((1 : ℝ) / 2) ^ s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [if_pos (by
          have := (Finset.mem_filter.mp hs).2
          omega)]
      _ ≤ ∑' i : ℕ,
          if split + 1 ≤ i then ((1 : ℝ) / 2) ^ i else 0 := by
        exact hsummable.sum_le_tsum large fun i _hi => by
          split_ifs <;> positivity
      _ = 2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
        simpa only [one_div] using tsum_geometric_inv_two_ge (split + 1)
  change (∑ s ∈ sizes, term s) ≤ _
  calc
    _ = (∑ s ∈ small, term s) + (∑ s ∈ large, term s) := by
      dsimp [small, large]
      rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ _ := add_le_add hsmallSum hlargeSum

/-- Collapsing loops and parallel configuration pairs cannot increase the
number of induced edges: every projected simple edge injects into a distinct
internal matching block. -/
theorem card_configurationProjectedEdgesOn_le_internalPairCount
    {m D s : ℕ} (C : Configuration m D)
    (U : ConfigurationVertexSet m s) :
    (configurationProjectedEdgesOn C U.1).card ≤
      configurationInternalPairCount C U := by
  classical
  let E := configurationProjectedEdgesOn C U.1
  have hedge (e : E) :
      C.projectedGraph.Adj e.1.1.out.1 e.1.1.out.2 :=
    (Finset.mem_filter.mp e.2).2
  have hendpoints (e : E) :
      e.1.1.out.1 ∈ U.1 ∧ e.1.1.out.2 ∈ U.1 :=
    (mem_ambientEdgesOn_iff_endpoints_mem U.1 e.1).mp
      (Finset.mem_filter.mp e.2).1
  let socket : E → Fin D := fun e =>
    Classical.choose ((C.projectedGraph_adj _ _).mp (hedge e)).2
  have hsocket (e : E) :
      C.socketNeighbor e.1.1.out.1 (socket e) = e.1.1.out.2 :=
    Classical.choose_spec ((C.projectedGraph_adj _ _).mp (hedge e)).2
  let first : E → ConfigurationHalfEdgeOn U D := fun e =>
    ⟨(e.1.1.out.1, socket e), (hendpoints e).1⟩
  let second : E → ConfigurationHalfEdgeOn U D := fun e =>
    ⟨C.partner (first e).1, by
      change C.socketNeighbor e.1.1.out.1 (socket e) ∈ U.1
      rw [hsocket e]
      exact (hendpoints e).2⟩
  let block : E → Sym2 (ConfigurationHalfEdgeOn U D) := fun e =>
    s(first e, second e)
  have hblock_mem (e : E) : block e ∈ configurationInternalPairBlocks C U := by
    rw [mem_configurationInternalPairBlocks]
    constructor
    · rw [SimpleGraph.mem_edgeFinset]
      change s(first e, second e) ∈
        (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)).edgeSet
      apply (SimpleGraph.mem_edgeSet (G :=
        (⊤ : SimpleGraph (ConfigurationHalfEdgeOn U D)))).2
      apply (SimpleGraph.top_adj _ _).2
      intro heq
      have hval := congrArg (fun h : ConfigurationHalfEdgeOn U D => h.1.1) heq
      change e.1.1.out.1 = C.socketNeighbor e.1.1.out.1 (socket e) at hval
      rw [hsocket e] at hval
      exact (hedge e).ne hval
    · have hout := (block e).out_eq
      change s((block e).out.1, (block e).out.2) =
        s(first e, second e) at hout
      rw [Sym2.eq_iff] at hout
      rcases hout with hout | hout
      · rw [hout.1, hout.2]
      · rw [hout.1, hout.2]
        exact C.partner_involutive (first e).1
  have hblock_injective : Function.Injective block := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    have hmapped := congrArg
      (Sym2.map fun h : ConfigurationHalfEdgeOn U D => h.1.1) hef
    change Sym2.map (fun h : ConfigurationHalfEdgeOn U D => h.1.1)
        s(first e, second e) =
      Sym2.map (fun h : ConfigurationHalfEdgeOn U D => h.1.1)
        s(first f, second f) at hmapped
    simp only [Sym2.map_pair_eq, first, second] at hmapped
    change s(e.1.1.out.1,
        C.socketNeighbor e.1.1.out.1 (socket e)) =
      s(f.1.1.out.1,
        C.socketNeighbor f.1.1.out.1 (socket f)) at hmapped
    rw [hsocket e, hsocket f] at hmapped
    rw [← e.1.1.out_eq, ← f.1.1.out_eq]
    exact hmapped
  have hinj : Function.Injective fun e : E =>
      (⟨block e, hblock_mem e⟩ : configurationInternalPairBlocks C U) := by
    intro e f hef
    exact hblock_injective (congrArg Subtype.val hef)
  change E.card ≤ (configurationInternalPairBlocks C U).card
  simpa only [Fintype.card_coe] using
    (Fintype.card_le_of_injective _ hinj)

/-- The induced-edge count used by the deterministic paper interface is the
same projected-simple count represented above in ambient edge coordinates.
For the event comparison below, the forward cardinal inequality is enough. -/
theorem deterministicInducedEdgeCount_le_configurationProjectedEdgesOn_card
    {m D : ℕ} (C : Configuration m D) (U : Finset (Fin m)) :
    deterministicInducedEdgeCount C.projectedGraph U ≤
      (configurationProjectedEdgesOn C U).card := by
  classical
  let G := C.projectedGraph
  let rawEmbedding : Sym2 {v // v ∈ (U : Set (Fin m))} ↪ Sym2 (Fin m) :=
    (Function.Embedding.subtype (U : Set (Fin m))).sym2Map
  have hrawG (e : (G.induce (U : Set (Fin m))).edgeSet) :
      rawEmbedding e.1 ∈ G.edgeSet := by
    have h := (SimpleGraph.Copy.induce G
      (U : Set (Fin m))).mapEdgeSet e |>.property
    change rawEmbedding e.1 ∈ G.edgeSet at h
    exact h
  let f : (G.induce (U : Set (Fin m))).edgeSet ↪ AmbientEdge m :=
    { toFun := fun e =>
        ⟨rawEmbedding e.1,
          (SimpleGraph.edgeSet_subset_edgeSet.mpr
            (show G ≤ (⊤ : SimpleGraph (Fin m)) from le_top)) (hrawG e)⟩
      inj' := by
        intro e e' h
        apply Subtype.ext
        exact rawEmbedding.injective (congrArg Subtype.val h) }
  have hfmem (e : (G.induce (U : Set (Fin m))).edgeSet) :
      f e ∈ configurationProjectedEdgesOn C U := by
    rw [configurationProjectedEdgesOn, Finset.mem_filter]
    constructor
    · unfold ambientEdgesOn
      rw [Finset.mem_map]
      have heTop : e.1 ∈ (⊤ : SimpleGraph U).edgeSet :=
        (SimpleGraph.edgeSet_subset_edgeSet.mpr
          (show G.induce (U : Set (Fin m)) ≤
            (⊤ : SimpleGraph U) from le_top)) e.2
      let a : (⊤ : SimpleGraph U).edgeSet := ⟨e.1, heTop⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change Sym2.map (fun u : U => u.1) e.1 = rawEmbedding e.1
      rfl
    · have heG : rawEmbedding e.1 ∈ G.edgeSet := hrawG e
      rw [← (rawEmbedding e.1).out_eq,
        SimpleGraph.mem_edgeSet] at heG
      exact heG
  let fp : (G.induce (U : Set (Fin m))).edgeSet ↪
      configurationProjectedEdgesOn C U :=
    { toFun := fun e => ⟨f e, hfmem e⟩
      inj' := fun _e _e' h => f.injective (congrArg Subtype.val h) }
  unfold deterministicInducedEdgeCount
  rw [SimpleGraph.edgeFinset_card]
  change Fintype.card (G.induce (U : Set (Fin m))).edgeSet ≤ _
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective fp fp.injective

/-- The projected-simple fixed-size bad event is contained in the exact
multigraph bad event from Lemma A.4. -/
theorem configurationLocalBadEventAtSize_subset_internal
    (m d s k : ℕ) :
    configurationLocalBadEventAtSize m d s k ⊆
      configurationInternalLocalBadEventAtSize m d s k := by
  classical
  intro sigma hsigma
  rw [configurationLocalBadEventAtSize, FiniteLaw.mem_event] at hsigma
  rw [configurationInternalLocalBadEventAtSize, FiniteLaw.mem_event]
  rcases hsigma with ⟨U, hUcard, hk⟩
  let Us : ConfigurationVertexSet m s :=
    ⟨U, by
      rw [vertexSubsets, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ U, hUcard⟩⟩
  refine ⟨Us, hk.trans ?_⟩
  exact card_configurationProjectedEdgesOn_le_internalPairCount
    (randomConfiguration m d sigma) Us

/-- The paper-facing projected-simple bad event is contained in the exact
configuration-multigraph failure event at the power cutoff. -/
theorem configurationBadLocalEvent_subset_internalLocalFailureEvent
    (d : ℕ) (r gamma A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    configurationBadLocalEvent d r gamma A n ⊆
      configurationInternalLocalFailureEvent n (appendixPlantSize r n) d
        (localSparsityPowerCutoff (appendixPlantSize r n) gamma) A := by
  classical
  intro sigma hsigma
  rw [configurationBadLocalEvent, FiniteLaw.mem_event] at hsigma
  rcases hsigma with ⟨U, hn, hUtwo, hUsize, hdense⟩
  rw [configurationInternalLocalFailureEvent, Finset.mem_biUnion]
  refine ⟨U.card, Finset.mem_Icc.mpr ⟨hUtwo, ?_⟩, ?_⟩
  · unfold localSparsityPowerCutoff
    exact Nat.le_floor hUsize
  · rw [configurationInternalLocalBadEventAtSize, FiniteLaw.mem_event]
    let Us : ConfigurationVertexSet (appendixPlantSize r n) U.card :=
      ⟨U, by
        rw [vertexSubsets, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ U, rfl⟩⟩
    refine ⟨Us, ?_⟩
    let t : ℝ :=
      (1 + A / Real.log (n : ℝ)) * (U.card : ℝ)
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have hfloorlt : ⌊t⌋₊ <
        deterministicInducedEdgeCount
          (randomConfiguration (appendixPlantSize r n) d sigma).projectedGraph U :=
      (Nat.floor_lt ht0).2 hdense
    have hkInduced : localSparsityThreshold n A U.card ≤
        deterministicInducedEdgeCount
          (randomConfiguration (appendixPlantSize r n) d sigma).projectedGraph U := by
      unfold localSparsityThreshold
      change ⌊t⌋₊ + 1 ≤ _
      omega
    exact hkInduced.trans <|
      (deterministicInducedEdgeCount_le_configurationProjectedEdgesOn_card
        (randomConfiguration (appendixPlantSize r n) d sigma) U).trans <|
        card_configurationProjectedEdgesOn_le_internalPairCount
          (randomConfiguration (appendixPlantSize r n) d sigma) Us

/-! ## Asymptotic form of configuration-model local sparsity -/

/-- A power cutoff with exponent strictly below one is a vanishing fraction
of any size sequence tending to infinity. -/
theorem localSparsityPowerCutoff_div_vanishes
    {gamma : ℝ} (hgamma : gamma < 1) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Vanishes fun n =>
      (localSparsityPowerCutoff (m n) gamma : ℝ) / (m n : ℝ) := by
  have hmReal : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have htarget : Vanishes fun n =>
      (m n : ℝ) ^ (-(1 - gamma)) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hgamma)).comp hmReal
  apply squeeze_zero'
  · exact Eventually.of_forall fun _n => by positivity
  · filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hmn
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast hmn
    have hcut :
        (localSparsityPowerCutoff (m n) gamma : ℝ) ≤
          (m n : ℝ) ^ gamma := by
      unfold localSparsityPowerCutoff
      exact Nat.floor_le (Real.rpow_nonneg hmpos.le gamma)
    calc
      (localSparsityPowerCutoff (m n) gamma : ℝ) / (m n : ℝ) ≤
          (m n : ℝ) ^ gamma / (m n : ℝ) :=
        div_le_div_of_nonneg_right hcut hmpos.le
      _ = (m n : ℝ) ^ gamma / (m n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (m n : ℝ) ^ (gamma - 1) := by
        rw [← Real.rpow_sub hmpos]
      _ = (m n : ℝ) ^ (-(1 - gamma)) := by ring_nf
  · exact htarget

/-- Consequently, every fixed multiple of the power cutoff eventually fits
inside any fixed positive multiple of the ambient size. -/
theorem eventually_const_mul_localSparsityPowerCutoff_le
    (C D : ℕ) (hD : 0 < D) {gamma : ℝ} (hgamma : gamma < 1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop,
      C * localSparsityPowerCutoff (m n) gamma ≤ m n * D := by
  have hratio := localSparsityPowerCutoff_div_vanishes hgamma m hm
  have hscaled : Vanishes fun n =>
      (C : ℝ) *
        ((localSparsityPowerCutoff (m n) gamma : ℝ) / (m n : ℝ)) :=
    hratio.const_mul C
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hlt : ∀ᶠ n in atTop,
      (C : ℝ) *
          ((localSparsityPowerCutoff (m n) gamma : ℝ) / (m n : ℝ)) <
        (D : ℝ) :=
    hscaled.eventually (Iio_mem_nhds hDreal)
  filter_upwards [hm.eventually (eventually_gt_atTop 0), hlt] with n hmn hnlt
  have hmpos : (0 : ℝ) < m n := by exact_mod_cast hmn
  have hdiv :
      ((C : ℝ) * (localSparsityPowerCutoff (m n) gamma : ℝ)) /
          (m n : ℝ) < (D : ℝ) := by
    convert hnlt using 1 <;> ring
  have hreal :
      (C : ℝ) * (localSparsityPowerCutoff (m n) gamma : ℝ) ≤
        (m n : ℝ) * (D : ℝ) :=
    by simpa only [mul_comm] using ((div_lt_iff₀ hmpos).mp hdiv).le
  exact_mod_cast hreal

/-- Fixed-`n` two-range estimate for the configuration multigraph.  The
extra finite guard says that every prescribed matching block used in the
union bound lies in the first half of the available half-edges. -/
theorem configurationPermutationLaw_prob_internalLocalFailureEvent_le_twoRange
    (d : ℕ) (hd : 0 < d) (r gamma : ℝ) (hr : 0 < r)
    (hgamma : gamma < 1) (n m cutoff split : ℕ)
    (hn : 1 < n) (hm : 0 < m) (hcutoffm : cutoff ≤ m)
    (hsplitLog : (split : ℝ) ≤
      localSparsityLogWindow (2 * ((d + d : ℕ) : ℝ)) *
        Real.log (m : ℝ))
    (hcutoffLog : ∀ s ∈ Finset.Icc 2 cutoff,
      Real.log ((s : ℝ) / (m : ℝ)) ≤
        -(1 - gamma) * Real.log (m : ℝ))
    (hlogRatio : r / 2 ≤
      Real.log (m : ℝ) / Real.log (n : ℝ))
    (hslackOne :
      localSparsitySlackConstant (2 * ((d + d : ℕ) : ℝ)) r gamma /
        Real.log (n : ℝ) ≤ 1)
    (hguard : 12 * cutoff ≤ m * (d + d)) :
    (configurationPermutationLaw m d).prob
        (configurationInternalLocalFailureEvent n m d cutoff
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma)) ≤
      ((split + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m : ℝ) +
        2 * (2 : ℝ)⁻¹ ^ (split + 1) := by
  classical
  let D := d + d
  let lam : ℝ := 2 * (D : ℝ)
  let A := localSparsitySlackConstant lam r gamma
  let term : ℕ → ℝ := fun s =>
    (m.choose s : ℝ) *
      (((s * D).choose 2).choose (localSparsityThreshold n A s) : ℝ) *
      ((prescribedPairDenominator (m * D)
        (localSparsityThreshold n A s) : ℕ) : ℝ)⁻¹
  have hsum :
      (configurationPermutationLaw m d).prob
          (configurationInternalLocalFailureEvent n m d cutoff A) ≤
        ∑ s ∈ Finset.Icc 2 cutoff, term s := by
    simpa only [D, A, term] using
      configurationPermutationLaw_prob_internalLocalFailureEvent_le
        n m d cutoff A
  refine hsum.trans ?_
  apply localSparsityNumericalSum_le_twoRange
    lam r gamma hr hgamma n m cutoff split hn hm hcutoffm
    (by simpa only [lam, D] using hsplitLog)
    hcutoffLog hlogRatio (by simpa only [lam, D] using hslackOne)
  intro s hsizes
  have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hsizes).1
  have hApos : 0 < A := localSparsitySlackConstant_pos lam hr hgamma
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hdelta0 : 0 ≤ A / Real.log (n : ℝ) :=
    (div_pos hApos (Real.log_pos hnreal)).le
  have hkLower : s ≤ localSparsityThreshold n A s :=
    (localSparsityThreshold_gt hdelta0).le
  have hkUpper : localSparsityThreshold n A s ≤ 3 * s :=
    localSparsityThreshold_le_three_mul (by omega) hdelta0
      (by simpa only [A, lam, D] using hslackOne)
  have hsCutoff : s ≤ cutoff := (Finset.mem_Icc.mp hsizes).2
  have hpairGuard :
      4 * localSparsityThreshold n A s ≤ m * D := by
    calc
      4 * localSparsityThreshold n A s ≤ 4 * (3 * s) :=
        Nat.mul_le_mul_left 4 hkUpper
      _ ≤ 12 * cutoff := by omega
      _ ≤ m * D := by simpa only [D] using hguard
  exact configurationInternalUnionTerm_le_base_mul_ratio_pow
    D (by dsimp [D]; omega) hm (by omega) hkLower hkUpper hpairGuard

/-- **Configuration-model local sparsity (paper Lemma A.4, bad-event
form).**  For every faithful power-scale size sequence, the probability
that some set of at most `⌊m^γ⌋` vertices spans too many configuration
blocks tends to zero.  Loops and parallel blocks are counted with their full
multiplicity here, so this is stronger than the projected-simple statement. -/
theorem configurationInternalLocalSparsityFailure_vanishes
    (d : ℕ) (hd : 0 < d) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hpowerScale : ∀ᶠ n in atTop,
      r / 2 ≤ Real.log (m n : ℝ) / Real.log (n : ℝ)) :
    Vanishes fun n =>
      (configurationPermutationLaw (m n) d).prob
        (configurationInternalLocalFailureEvent n (m n) d
          (localSparsityPowerCutoff (m n) gamma)
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma)) := by
  let lam : ℝ := 2 * ((d + d : ℕ) : ℝ)
  let A := localSparsitySlackConstant lam r gamma
  let split : ℕ → ℕ := fun n => localSparsityLogSplit lam (m n)
  let cutoff : ℕ → ℕ := fun n =>
    localSparsityPowerCutoff (m n) gamma
  let envelope : ℕ → ℝ := fun n =>
    (((split n + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt (m n : ℝ)) +
      2 * (2 : ℝ)⁻¹ ^ (split n + 1)
  have hnLarge : ∀ᶠ n in atTop, 1 < n := eventually_gt_atTop 1
  have hmPos : ∀ᶠ n in atTop, 0 < m n :=
    hm.eventually (eventually_gt_atTop 0)
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ n : ℕ in atTop, A ≤ Real.log (n : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop A)
  have hslackOne : ∀ᶠ n : ℕ in atTop,
      A / Real.log (n : ℝ) ≤ 1 := by
    filter_upwards [hnLarge, hlogLarge] with n hn hAn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_one (Real.log_pos hnReal)).2 hAn
  have hguard : ∀ᶠ n in atTop,
      12 * cutoff n ≤ m n * (d + d) := by
    simpa only [cutoff] using
      eventually_const_mul_localSparsityPowerCutoff_le
        12 (d + d) (by omega) hgamma.2 m hm
  have hupper : ∀ᶠ n in atTop,
      (configurationPermutationLaw (m n) d).prob
          (configurationInternalLocalFailureEvent n (m n) d
            (cutoff n) A) ≤ envelope n := by
    filter_upwards [hnLarge, hmPos, hpowerScale, hslackOne, hguard] with
        n hn hmn hratio hslack hpairGuard
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
    simpa only [lam, A, split, envelope] using
      configurationPermutationLaw_prob_internalLocalFailureEvent_le_twoRange
        d hd r gamma hr.1 hgamma.2 n (m n) (cutoff n) (split n)
        hn hmn hcutoffm (localSparsityLogSplit_cast_le lam (m n))
        hcutoffLog hratio (by simpa only [A] using hslack) hpairGuard
  have henvelope : Vanishes envelope := by
    simpa only [envelope, split] using
      localSparsityTwoRangeEnvelope_vanishes lam hm
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      (configurationPermutationLaw (m n) d).prob_nonneg
        (configurationInternalLocalFailureEvent n (m n) d
          (localSparsityPowerCutoff (m n) gamma)
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma))
  · simpa only [cutoff, A, lam] using hupper
  · exact henvelope

/-- Positivity of the explicit Appendix A.4 slack constant. -/
theorem appendixConfigurationLocalSparsitySlackConstant_pos
    (d : ℕ) {r gamma : ℝ} (hr : 0 < r) (hgamma : gamma < 1) :
    0 < localSparsitySlackConstant
      (2 * ((d + d : ℕ) : ℝ)) r gamma :=
  localSparsitySlackConstant_pos _ hr hgamma

/-- **Appendix Lemma A.4 (paper-facing bad-event form).**  For the canonical
plant size `mₙ = ⌊nʳ⌋`, the probability of violating the projected-simple
local-sparsity inequality tends to zero. -/
theorem appendixConfigurationBadLocal_probability_vanishes
    (d : ℕ) (hd : 0 < d) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    Vanishes fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (configurationBadLocalEvent d r gamma
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma) n) := by
  let A := localSparsitySlackConstant
    (2 * ((d + d : ℕ) : ℝ)) r gamma
  have hA : 0 < A :=
    appendixConfigurationLocalSparsitySlackConstant_pos d hr.1 hgamma.2
  have hinternal := configurationInternalLocalSparsityFailure_vanishes
    d hd r gamma hr hgamma (appendixPlantSize r)
      (appendixPlantSize_tendsto_atTop hr.1)
      (eventually_appendixPlantSize_log_ratio_ge_half hr.1)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) d).prob_nonneg
        (configurationBadLocalEvent d r gamma
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma) n)
  · exact Eventually.of_forall fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) d).prob_mono
        (configurationBadLocalEvent_subset_internalLocalFailureEvent
          d r gamma A hA.le n)
  · simpa only [A] using hinternal

/-- Equivalent probability-`1-o(1)` complement form of Appendix Lemma A.4. -/
theorem appendixConfigurationLocalSparsity_probability_tendsto_one
    (d : ℕ) (hd : 0 < d) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    TendsToOne fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) d).prob
        (Finset.univ \ configurationBadLocalEvent d r gamma
          (localSparsitySlackConstant
            (2 * ((d + d : ℕ) : ℝ)) r gamma) n) := by
  have hbad := appendixConfigurationBadLocal_probability_vanishes
    d hd r gamma hr hgamma
  change Tendsto _ atTop (𝓝 1)
  change Tendsto _ atTop (𝓝 0) at hbad
  have hcomplement : Tendsto
      (fun n => (1 : ℝ) -
        (configurationPermutationLaw (appendixPlantSize r n) d).prob
          (configurationBadLocalEvent d r gamma
            (localSparsitySlackConstant
              (2 * ((d + d : ℕ) : ℝ)) r gamma) n))
      atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hbad : Tendsto _ atTop (𝓝 ((1 : ℝ) - 0)))
  apply hcomplement.congr'
  exact Eventually.of_forall fun n => by
    simpa using (FiniteLaw.prob_univ_sdiff
      (configurationPermutationLaw (appendixPlantSize r n) d)
      (configurationBadLocalEvent d r gamma
        (localSparsitySlackConstant
          (2 * ((d + d : ℕ) : ℝ)) r gamma) n)).symm

/-- Appendix A.4 in the manuscript's total-degree notation: `D` is even,
and the implementation uses two socket blocks of size `D/2`.  The identity
`D / 2 + D / 2 = D`, also exposed as `evenTotalDegree_half_add_half` in the
short-cycle companion module, certifies that these configurations have the
paper's total degree `D`. -/
theorem appendixA4_evenDegree_badLocal_probability_vanishes
    (D : ℕ) (hD : Even D) (hD6 : 6 ≤ D) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    Vanishes fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) (D / 2)).prob
        (configurationBadLocalEvent (D / 2) r gamma
          (localSparsitySlackConstant (2 * (D : ℝ)) r gamma) n) := by
  have hhalf : D / 2 + D / 2 = D := by
    obtain ⟨d, rfl⟩ := hD
    omega
  have hdhalf : 0 < D / 2 := by omega
  simpa only [hhalf] using
    appendixConfigurationBadLocal_probability_vanishes
      (D / 2) hdhalf r gamma hr hgamma

/-- Probability-`1-o(1)` complement of the even-total-degree form. -/
theorem appendixA4_evenDegree_localSparsity_probability_tendsto_one
    (D : ℕ) (hD : Even D) (hD6 : 6 ≤ D) (r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    TendsToOne fun n =>
      (configurationPermutationLaw (appendixPlantSize r n) (D / 2)).prob
        (Finset.univ \ configurationBadLocalEvent (D / 2) r gamma
          (localSparsitySlackConstant (2 * (D : ℝ)) r gamma) n) := by
  have hhalf : D / 2 + D / 2 = D := by
    obtain ⟨d, rfl⟩ := hD
    omega
  have hdhalf : 0 < D / 2 := by omega
  simpa only [hhalf] using
    appendixConfigurationLocalSparsity_probability_tendsto_one
      (D / 2) hdhalf r gamma hr hgamma

end

end LowDegree
