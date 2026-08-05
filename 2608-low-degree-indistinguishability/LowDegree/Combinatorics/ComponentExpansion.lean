import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite connected-component cluster expansion

This file formalizes the combinatorial/analytic engine of paper Lemma 4.4.
An active finite object is encoded injectively by a nonempty ordered list of
connected objects, and its weight is bounded by the product of their weights.
The total active mass is therefore bounded by the geometric series in the
connected mass.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Abstract data supplied by the connected-component decomposition of a
finite family of graph isomorphism classes. -/
structure ComponentEncoding (A : Type*) where
  active : A → Prop
  connected : A → Prop
  components : A → List A
  components_nonempty : ∀ a : {a // active a},
    components a.1 ≠ []
  component_connected : ∀ a : {a // active a},
    ∀ b ∈ components a.1, connected b
  components_injective : Set.InjOn components {a | active a}

namespace ComponentEncoding

variable {A : Type*} [Fintype A] (C : ComponentEncoding A)

abbrev ConnectedObject := {a : A // C.connected a}
abbrev ActiveObject := {a : A // C.active a}

/-- The sigma type of all finite ordered tuples of connected objects. -/
abbrev ConnectedTuple := Σ m : ℕ, Fin m → C.ConnectedObject

/-- Encode an active object by its ordered connected-component tuple. -/
noncomputable def componentTuple (a : C.ActiveObject) : C.ConnectedTuple :=
  ⟨(C.components a.1).length, fun i ↦
    ⟨(C.components a.1).get i,
      C.component_connected a _ (List.get_mem _ _)⟩⟩

private def eraseConnectedTuple (z : C.ConnectedTuple) :
    Σ m : ℕ, Fin m → A :=
  ⟨z.1, fun i ↦ (z.2 i).1⟩

/-- Injectivity of the component list gives injectivity of the typed tuple
encoding. -/
theorem componentTuple_injective : Function.Injective C.componentTuple := by
  intro a b hab
  apply Subtype.ext
  apply C.components_injective a.2 b.2
  apply List.equivSigmaTuple.injective
  have h := congrArg C.eraseConnectedTuple hab
  simpa [componentTuple, eraseConnectedTuple, List.equivSigmaTuple] using h

/-- Product weight of a connected tuple, with the empty tuple assigned zero.
The zero convention removes the constant term from the geometric series. -/
noncomputable def tupleWeight (weight : A → ℝ)
    (z : C.ConnectedTuple) : ℝ :=
  if z.1 = 0 then 0 else ∏ i, weight (z.2 i).1

/-- Sum of nonnegative weights over all connected objects. -/
noncomputable def connectedMass (weight : A → ℝ) : ℝ :=
  ∑ a : C.ConnectedObject, weight a.1

private theorem sum_tupleWeight_fiber
    (weight : A → ℝ) (m : ℕ) :
    (∑ f : Fin m → C.ConnectedObject,
        C.tupleWeight weight ⟨m, f⟩) =
      if m = 0 then 0 else C.connectedMass weight ^ m := by
  by_cases hm : m = 0
  · subst m
    simp [tupleWeight]
  · simp only [tupleWeight, hm, if_false]
    rw [connectedMass]
    simpa using
      (Finset.sum_pow' (s := (Finset.univ : Finset C.ConnectedObject))
        (f := fun a ↦ weight a.1) m).symm

private theorem tupleWeight_nonneg
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a)
    (z : C.ConnectedTuple) : 0 ≤ C.tupleWeight weight z := by
  unfold tupleWeight
  split
  · exact le_rfl
  · exact Finset.prod_nonneg fun i _ ↦ hweight (z.2 i).1

/-- **Finite component cluster expansion (paper Lemma 4.4).**

If every active object is injectively determined by a nonempty ordered list
of connected components and its weight is at most the product of the
component weights, then its total mass is at most `θ/(1-θ)`, where `θ`
is the total connected mass. -/
theorem sum_active_le_geometric_connectedMass
    (weight : A → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hfactor : ∀ a : C.ActiveObject,
      weight a.1 ≤
        ∏ i : Fin (C.components a.1).length,
          weight ((C.components a.1).get i))
    (hmass : C.connectedMass weight < 1) :
    (∑ a : C.ActiveObject, weight a.1) ≤
      C.connectedMass weight / (1 - C.connectedMass weight) := by
  let θ := C.connectedMass weight
  have hθ0 : 0 ≤ θ := by
    dsimp [θ, connectedMass]
    exact Finset.sum_nonneg fun a _ ↦ hweight a.1
  have hgeom : Summable (fun m : ℕ ↦ θ ^ m) :=
    summable_geometric_of_lt_one hθ0 hmass
  let tail : ℕ → ℝ := fun m ↦ if m = 0 then 0 else θ ^ m
  have htail_nonneg (m : ℕ) : 0 ≤ tail m := by
    dsimp [tail]
    split
    · exact le_rfl
    · exact pow_nonneg hθ0 _
  have htail_le (m : ℕ) : tail m ≤ θ ^ m := by
    dsimp [tail]
    split
    · exact pow_nonneg hθ0 _
    · exact le_rfl
  have htail : Summable tail :=
    Summable.of_nonneg_of_le htail_nonneg htail_le hgeom
  have htuple : Summable (C.tupleWeight weight) := by
    apply (summable_sigma_of_nonneg
      (C.tupleWeight_nonneg weight hweight)).2
    constructor
    · intro m
      exact summable_of_finite_support (Set.toFinite _)
    · have hout : (fun m : ℕ ↦
          ∑' f : Fin m → C.ConnectedObject,
            C.tupleWeight weight ⟨m, f⟩) = tail := by
        funext m
        rw [tsum_fintype, C.sum_tupleWeight_fiber]
      rw [hout]
      exact htail
  have htupleSum : (∑' z : C.ConnectedTuple, C.tupleWeight weight z) =
      θ / (1 - θ) := by
    rw [htuple.tsum_sigma]
    simp_rw [tsum_fintype, C.sum_tupleWeight_fiber]
    change (∑' m : ℕ, tail m) = _
    rw [htail.tsum_eq_zero_add]
    simp only [tail, if_pos, zero_add, Nat.succ_ne_zero,
      if_false]
    have hshift : (∑' m : ℕ, θ ^ (m + 1)) =
        θ / (1 - θ) := by
      rw [show (∑' m : ℕ, θ ^ (m + 1)) =
          θ * ∑' m : ℕ, θ ^ m by
        simp_rw [pow_succ']
        exact tsum_mul_left]
      rw [tsum_geometric_of_lt_one hθ0 hmass]
      field_simp
    exact hshift
  have hencode (a : C.ActiveObject) :
      weight a.1 ≤ C.tupleWeight weight (C.componentTuple a) := by
    have hlen : (C.components a.1).length ≠ 0 :=
      Nat.ne_of_gt (List.length_pos_iff.mpr (C.components_nonempty a))
    simp only [tupleWeight, componentTuple, hlen, if_false]
    exact hfactor a
  have hactive : Summable (fun a : C.ActiveObject ↦ weight a.1) :=
    summable_of_finite_support (Set.toFinite _)
  calc
    (∑ a : C.ActiveObject, weight a.1) =
        ∑' a : C.ActiveObject, weight a.1 := by rw [tsum_fintype]
    _ ≤ ∑' z : C.ConnectedTuple, C.tupleWeight weight z :=
      hactive.tsum_le_tsum_of_inj C.componentTuple
        C.componentTuple_injective
        (fun z _hz ↦ C.tupleWeight_nonneg weight hweight z)
        hencode htuple
    _ = θ / (1 - θ) := htupleSum
    _ = C.connectedMass weight /
        (1 - C.connectedMass weight) := rfl

end ComponentEncoding

end

end LowDegree
