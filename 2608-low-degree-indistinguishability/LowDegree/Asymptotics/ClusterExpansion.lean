import LowDegree.Asymptotics.Basic
import LowDegree.Combinatorics.ComponentExpansion

/-!
# Asymptotic connected-component cluster expansion

This module combines the finite component encoding with the asymptotic
`o(1)` conclusion of paper Lemma 4.4.  Unlike the earlier analytic shell, the
geometric majorization is derived here from an injective component
decomposition and a pointwise product bound.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A vanishing real sequence is eventually strictly below one. -/
private theorem Vanishes.eventually_lt_one {x : ℕ → ℝ}
    (hx : Vanishes x) : ∀ᶠ n in atTop, x n < 1 :=
  (tendsto_order.1 hx).2 1 zero_lt_one

/-- **Paper Lemma 4.4, component-encoding form.**

At each `n`, active objects are injectively encoded by a nonempty ordered
list of connected components.  Nonnegative weights factor submultiplicatively
over that list.  If the connected mass is `o(1)`, then the total nonempty mass
is `o(1)`.  The printed low-degree premise is retained explicitly even though
the component argument does not consume it. -/
theorem clusterExpansion_vanishes
    {A : ℕ → Type*} [∀ n, Fintype (A n)]
    (C : ∀ n, ComponentEncoding (A n))
    (weight : ∀ n, A n → ℝ)
    (lowDegreeNormSq : ℕ → ℝ)
    (_hlow : TendsToOne lowDegreeNormSq)
    (hweight : ∀ n a, 0 ≤ weight n a)
    (hfactor : ∀ n (a : (C n).ActiveObject),
      weight n a.1 ≤
        ∏ i : Fin ((C n).components a.1).length,
          weight n (((C n).components a.1).get i))
    (hconnected : Vanishes fun n ↦ (C n).connectedMass (weight n)) :
    Vanishes fun n ↦ ∑ a : (C n).ActiveObject, weight n a.1 := by
  let θ : ℕ → ℝ := fun n ↦ (C n).connectedMass (weight n)
  let total : ℕ → ℝ := fun n ↦
    ∑ a : (C n).ActiveObject, weight n a.1
  have hθ : Vanishes θ := hconnected
  have hlt : ∀ᶠ n in atTop, θ n < 1 := hθ.eventually_lt_one
  have htotal_nonneg : ∀ n, 0 ≤ total n := by
    intro n
    exact Finset.sum_nonneg fun a _ ↦ hweight n a.1
  have hmajorize : ∀ᶠ n in atTop,
      total n ≤ θ n / (1 - θ n) := by
    filter_upwards [hlt] with n hn
    exact (C n).sum_active_le_geometric_connectedMass
      (weight n) (hweight n) (hfactor n) hn
  have hden : Tendsto (fun n ↦ 1 - θ n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hθ
  have hfrac : Vanishes (fun n ↦ θ n / (1 - θ n)) := by
    simpa only [zero_div] using
      hθ.div hden (by norm_num : (1 : ℝ) ≠ 0)
  exact squeeze_zero' (Eventually.of_forall htotal_nonneg) hmajorize hfrac

end

end LowDegree
