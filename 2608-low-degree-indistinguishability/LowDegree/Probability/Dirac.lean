import LowDegree.Probability.Convergence

/-!
# Point masses on finite sample spaces

The deterministic appendix repeatedly regards one fixed finite graph as a
random object with a point-mass law.  This file supplies that elementary
bridge and records that ordinary convergence of deterministic statistics is
the same as convergence in probability under the corresponding point masses.
-/

namespace LowDegree

open Filter Topology

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

namespace FiniteLaw

variable {Omega : Type*} [Fintype Omega]

/-- The probability law concentrated at one point. -/
noncomputable def dirac (omega : Omega) : FiniteLaw Omega where
  mass x := if x = omega then 1 else 0
  mass_nonneg x := by split <;> norm_num
  sum_mass := by simp

@[simp]
theorem dirac_mass (omega x : Omega) :
    (dirac omega).mass x = if x = omega then 1 else 0 :=
  rfl

@[simp]
theorem dirac_mass_self (omega : Omega) : (dirac omega).mass omega = 1 := by
  simp [dirac]

@[simp]
theorem dirac_prob (omega : Omega) (s : Finset Omega) :
    (dirac omega).prob s = if omega ∈ s then 1 else 0 := by
  classical
  exact Finset.sum_ite_eq' s omega (fun _ => (1 : Real))

@[simp]
theorem dirac_prob_event (omega : Omega) (p : Omega -> Prop) :
    (dirac omega).prob (event p) = if p omega then 1 else 0 := by
  simp

@[simp]
theorem dirac_expect (omega : Omega) (f : Omega -> Real) :
    (dirac omega).expect f = f omega := by
  classical
  unfold expect dirac
  simp

end FiniteLaw

/-- A deterministic statistic converging in the ordinary sense converges in
probability under point-mass laws. -/
theorem tendstoInProbability_dirac
    {Omega : Nat -> Type*} [forall n, Fintype (Omega n)]
    (omega : forall n, Omega n) (X : forall n, Omega n -> Real) (a : Real)
    (hX : Tendsto (fun n => X n (omega n)) atTop (nhds a)) :
    TendstoInProbability (fun n => FiniteLaw.dirac (omega n)) X a := by
  intro delta hdelta
  have hevent : ∀ᶠ n in atTop,
      |X n (omega n) - a| < delta := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.1 hX delta hdelta)
  exact (tendsto_congr' (hevent.mono fun n hn => by
    rw [FiniteLaw.dirac_prob_event]
    simp [not_le.mpr hn])).mpr tendsto_const_nhds

end

end LowDegree
