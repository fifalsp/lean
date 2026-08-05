import LowDegree.PlantedModel
import LowDegree.Probability.Convergence
import Mathlib.Data.Nat.Choose.Cast

/-!
# Counting present Bernoulli coordinates

This file proves the exact first and second moments of the number of present
coordinates under a finite Bernoulli product law, followed by the finite
Chebyshev estimate used for sparse Erdős--Rényi edge counts.
-/

namespace LowDegree

open scoped BigOperators

noncomputable section

section Count

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The number of present coordinates, regarded as a real random variable. -/
def bernoulliCountReal (x : BooleanConfiguration E) : ℝ :=
  ∑ e : E, BernoulliParameter.bitValue (x e)

/-- Centered number of present coordinates. -/
def centeredBernoulliCount (θ : BernoulliParameter)
    (x : BooleanConfiguration E) : ℝ :=
  bernoulliCountReal x - Fintype.card E * θ.p

theorem bitValue_eq_p_add_sigma_mul_oneCharacter
    (θ : BernoulliParameter) (b : Bool) :
    BernoulliParameter.bitValue b =
      θ.p + θ.sigma * θ.oneCharacter b := by
  unfold BernoulliParameter.oneCharacter
  field_simp [θ.sigma_ne_zero]
  ring_nf

theorem bernoulliExpectation_edgeCharacter
    (θ : BernoulliParameter) (e : E) :
    bernoulliExpectation θ (edgeCharacter θ e) = 0 := by
  have h := fourierCharacters_orthonormal θ (∅ : Finset E) ({e} : Finset E)
  simpa [bernoulliInner, fourierCharacter_empty,
    fourierCharacter_eq_prod, edgeCharacter] using h

theorem centeredBernoulliCount_eq_characterSum
    (θ : BernoulliParameter) (x : BooleanConfiguration E) :
    centeredBernoulliCount θ x =
      θ.sigma * ∑ e : E, edgeCharacter θ e x := by
  unfold centeredBernoulliCount bernoulliCountReal
  simp_rw [bitValue_eq_p_add_sigma_mul_oneCharacter θ]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [edgeCharacter]
  simp

/-- Exact mean of a finite Bernoulli count. -/
theorem bernoulliExpectation_count (θ : BernoulliParameter) :
    bernoulliExpectation θ (bernoulliCountReal (E := E)) =
      Fintype.card E * θ.p := by
  have hzero : bernoulliExpectation θ
      (centeredBernoulliCount (E := E) θ) = 0 := by
    unfold bernoulliExpectation
    simp_rw [centeredBernoulliCount_eq_characterSum θ]
    calc
      (∑ x, bernoulliProductMass θ x *
          (θ.sigma * ∑ e : E, edgeCharacter θ e x)) =
          ∑ x, ∑ e : E,
            θ.sigma * (bernoulliProductMass θ x * edgeCharacter θ e x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = ∑ e : E, ∑ x,
            θ.sigma * (bernoulliProductMass θ x * edgeCharacter θ e x) := by
        rw [Finset.sum_comm]
      _ =
          θ.sigma * ∑ e : E,
            bernoulliExpectation θ (edgeCharacter θ e) := by
        simp only [bernoulliExpectation]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
      _ = 0 := by simp [bernoulliExpectation_edgeCharacter]
  unfold centeredBernoulliCount at hzero
  unfold bernoulliExpectation at hzero ⊢
  simp only at hzero
  have hconst :
      ∑ x : BooleanConfiguration E,
        bernoulliProductMass θ x * (Fintype.card E * θ.p) =
          Fintype.card E * θ.p := by
    rw [← Finset.sum_mul]
    simp
  simp_rw [mul_sub] at hzero
  rw [Finset.sum_sub_distrib, hconst] at hzero
  linarith

private theorem characterSum_secondMoment (θ : BernoulliParameter) :
    bernoulliExpectation θ
        (fun x : BooleanConfiguration E ↦
          (∑ e : E, edgeCharacter θ e x) ^ 2) =
      Fintype.card E := by
  unfold bernoulliExpectation
  calc
    (∑ x : BooleanConfiguration E, bernoulliProductMass θ x *
        (∑ e : E, edgeCharacter θ e x) ^ 2) =
        ∑ x : BooleanConfiguration E, ∑ e : E, ∑ f : E,
          bernoulliProductMass θ x *
            (edgeCharacter θ e x * edgeCharacter θ f x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ e : E, ∑ f : E, ∑ x : BooleanConfiguration E,
          bernoulliProductMass θ x *
            (edgeCharacter θ e x * edgeCharacter θ f x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
    _ =
        ∑ e : E, ∑ f : E,
          bernoulliInner θ (edgeCharacter θ e) (edgeCharacter θ f) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      unfold bernoulliInner bernoulliExpectation
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ e : E, ∑ f : E, if e = f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      have h := fourierCharacters_orthonormal θ ({e} : Finset E) ({f} : Finset E)
      have he : fourierCharacter θ ({e} : Finset E) = edgeCharacter θ e := by
        funext x
        simp [fourierCharacter_eq_prod]
      have hf : fourierCharacter θ ({f} : Finset E) = edgeCharacter θ f := by
        funext x
        simp [fourierCharacter_eq_prod]
      rw [he, hf] at h
      simpa using h
    _ = Fintype.card E := by simp

/-- Exact variance of a finite Bernoulli count. -/
theorem bernoulliExpectation_centeredCount_sq (θ : BernoulliParameter) :
    bernoulliExpectation θ
        (fun x : BooleanConfiguration E ↦ (centeredBernoulliCount θ x) ^ 2) =
      Fintype.card E * θ.variance := by
  simp_rw [centeredBernoulliCount_eq_characterSum θ, mul_pow]
  unfold bernoulliExpectation
  calc
    (∑ x : BooleanConfiguration E, bernoulliProductMass θ x *
        (θ.sigma ^ 2 * (∑ e : E, edgeCharacter θ e x) ^ 2)) =
        θ.sigma ^ 2 *
          bernoulliExpectation θ
            (fun x : BooleanConfiguration E ↦
              (∑ e : E, edgeCharacter θ e x) ^ 2) := by
      unfold bernoulliExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = θ.sigma ^ 2 * Fintype.card E := by
      rw [characterSum_secondMoment]
    _ = Fintype.card E * θ.variance := by
      rw [θ.sigma_sq]
      ring

/-- Chebyshev's inequality for a finite Bernoulli count. -/
theorem bernoulliCount_chebyshev (θ : BernoulliParameter) {a : ℝ} (ha : 0 < a) :
    (bernoulliProductLaw (E := E) θ).prob
        (FiniteLaw.event fun x ↦ a ≤ |centeredBernoulliCount θ x|) ≤
      (Fintype.card E * θ.variance) / a ^ 2 := by
  let q := bernoulliProductLaw (E := E) θ
  let Z : BooleanConfiguration E → ℝ := fun x ↦ (centeredBernoulliCount θ x) ^ 2
  have hmarkov := q.markov Z (fun x ↦ sq_nonneg _) (sq_pos_of_pos ha)
  have hevent :
      FiniteLaw.event (fun x ↦ a ^ 2 ≤ Z x) =
        FiniteLaw.event (fun x ↦ a ≤ |centeredBernoulliCount θ x|) := by
    ext x
    simp only [FiniteLaw.mem_event, Z]
    let z := centeredBernoulliCount θ x
    have hiff : a ^ 2 ≤ |z| ^ 2 ↔ a ≤ |z| :=
      sq_le_sq₀ (le_of_lt ha) (abs_nonneg z)
    simpa [z, sq_abs] using hiff
  rw [hevent] at hmarkov
  have hexpect : q.expect Z = Fintype.card E * θ.variance := by
    simpa [q, FiniteLaw.expect, bernoulliExpectation, Z] using
      (bernoulliExpectation_centeredCount_sq (E := E) θ)
  rw [hexpect] at hmarkov
  exact hmarkov

end Count

section TriangularArray

open Filter Topology

variable {E : ℕ → Type*}
variable [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]

/-- Bernoulli counts on varying finite coordinate sets concentrate around
their deterministic normalized means whenever the normalized variances
vanish.  This is the triangular-array form of binomial concentration used
for sparse Erdős--Rényi edge counts in Lemma A.3. -/
theorem bernoulliCount_div_tendstoInProbability
    (θ : ∀ n, BernoulliParameter) (scale : ℕ → ℝ) (limit : ℝ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hmean : Tendsto
      (fun n ↦ (Fintype.card (E n) : ℝ) * (θ n).p / scale n)
      atTop (𝓝 limit))
    (hvariance : Vanishes
      (fun n ↦ (Fintype.card (E n) : ℝ) * (θ n).variance /
        (scale n) ^ 2)) :
    TendstoInProbability
      (fun n ↦ bernoulliProductLaw (E := E n) (θ n))
      (fun n x ↦ bernoulliCountReal x / scale n) limit := by
  intro δ hδ
  let mean : ℕ → ℝ := fun n ↦
    (Fintype.card (E n) : ℝ) * (θ n).p / scale n
  let bad : (n : ℕ) → Finset (BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun x ↦ δ ≤ |bernoulliCountReal x / scale n - limit|
  let centeredBad : (n : ℕ) → Finset (BooleanConfiguration (E n)) := fun n ↦
    FiniteLaw.event fun x ↦
      (δ / 2) * scale n ≤ |centeredBernoulliCount (θ n) x|
  have hmeanClose : ∀ᶠ n in atTop, |mean n - limit| < δ / 2 := by
    have hball := hmean.eventually (Metric.ball_mem_nhds limit (half_pos hδ))
    filter_upwards [hball] with n hn
    simpa only [mean, Real.dist_eq] using hn
  have hsubset : ∀ᶠ n in atTop, bad n ⊆ centeredBad n := by
    filter_upwards [hmeanClose, hscale] with n hn hs
    intro x hx
    simp only [bad, centeredBad, FiniteLaw.mem_event] at hx ⊢
    let A := bernoulliCountReal x / scale n
    have htriangle : |A - limit| ≤ |A - mean n| + |mean n - limit| := by
      convert abs_add_le (A - mean n) (mean n - limit) using 1 <;> ring_nf
    have hcenter : δ / 2 ≤ |A - mean n| := by
      dsimp only [A]
      dsimp only [A] at htriangle
      linarith
    have hrewrite :
        |A - mean n| = |centeredBernoulliCount (θ n) x| / scale n := by
      have halgebra :
          A - mean n = centeredBernoulliCount (θ n) x / scale n := by
        dsimp only [A, mean]
        unfold centeredBernoulliCount
        field_simp [(ne_of_gt hs)]
      rw [halgebra, abs_div, abs_of_pos hs]
    rw [hrewrite] at hcenter
    exact (le_div_iff₀ hs).mp (by simpa [mul_comm] using hcenter)
  have hprobBound : ∀ᶠ n in atTop,
      (bernoulliProductLaw (E := E n) (θ n)).prob (bad n) ≤
        ((Fintype.card (E n) : ℝ) * (θ n).variance) /
          (((δ / 2) * scale n) ^ 2) := by
    filter_upwards [hsubset, hscale] with n hn hs
    exact le_trans
      ((bernoulliProductLaw (E := E n) (θ n)).prob_mono hn)
      (bernoulliCount_chebyshev (E := E n) (θ n)
        (mul_pos (half_pos hδ) hs))
  have hright : Vanishes (fun n ↦
      ((Fintype.card (E n) : ℝ) * (θ n).variance) /
        (((δ / 2) * scale n) ^ 2)) := by
    have hscaled := Vanishes.const_mul (4 / δ ^ 2) hvariance
    apply hscaled.congr'
    filter_upwards [hscale] with n hs
    field_simp [(ne_of_gt hδ), (ne_of_gt hs)]
    ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦
      (bernoulliProductLaw (E := E n) (θ n)).prob_nonneg (bad n)
  · exact hprobBound
  · exact hright

end TriangularArray

section ErdosRenyi

open Filter Topology

/-- The number of edge coordinates of the complete graph on `Fin m`. -/
theorem card_ambientEdge (m : ℕ) :
    Fintype.card (AmbientEdge m) = m.choose 2 := by
  calc
    Fintype.card (AmbientEdge m) =
        (⊤ : SimpleGraph (Fin m)).edgeFinset.card := by
      simpa only [AmbientEdge] using
        (SimpleGraph.edgeFinset_card (G := (⊤ : SimpleGraph (Fin m)))).symm
    _ = m.choose 2 := by
      simpa using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin m))

/-- Sparse Erdős--Rényi graphs have their usual linear edge density.  The
coordinate set is the actual edge set of the complete graph, the Bernoulli
parameter is the canonical eventually-`λ/m` family, and the convergence is
in probability under the concrete finite graph law. -/
theorem sparseErdosRenyi_edgeDensity_tendstoInProbability
    (lam : ℝ) (hlam : 0 < lam) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    TendstoInProbability
      (fun n ↦ erdosRenyiLaw (n := m n)
        (sparseBernoulliParameter lam (m n)))
      (fun n x ↦ bernoulliCountReal x / (m n : ℝ)) (lam / 2) := by
  have hmreal : Tendsto (fun n ↦ (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hinv : Tendsto (fun n ↦ ((m n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hmreal
  have hmpos : ∀ᶠ n in atTop, 0 < (m n : ℝ) := by
    have hnat : ∀ᶠ n in atTop, 0 < m n := hm.eventually (eventually_gt_atTop 0)
    filter_upwards [hnat] with n hn
    exact_mod_cast hn
  have hp : ∀ᶠ n in atTop,
      (sparseBernoulliParameter lam (m n)).p = lam / (m n : ℝ) :=
    hm.eventually (eventually_sparseBernoulliParameter_p_eq hlam)
  have honeMinusInv :
      Tendsto (fun n ↦ 1 - ((m n : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  have hmean : Tendsto
      (fun n ↦
        (Fintype.card (AmbientEdge (m n)) : ℝ) *
          (sparseBernoulliParameter lam (m n)).p / (m n : ℝ))
      atTop (𝓝 (lam / 2)) := by
    have hsimple : Tendsto
        (fun n ↦ (lam / 2) * (1 - ((m n : ℝ))⁻¹))
        atTop (𝓝 (lam / 2)) := by
      simpa using tendsto_const_nhds.mul honeMinusInv
    apply hsimple.congr'
    filter_upwards [hp, hmpos] with n hpn hmn
    rw [card_ambientEdge, hpn, Nat.cast_choose_two]
    field_simp [(ne_of_gt hmn)]
  have honeMinusLambdaInv :
      Tendsto (fun n ↦ 1 - lam * ((m n : ℝ))⁻¹) atTop (𝓝 1) := by
    have hlambdaInv :
        Tendsto (fun n ↦ lam * ((m n : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinv
    simpa only [sub_zero] using tendsto_const_nhds.sub hlambdaInv
  have hvariance : Vanishes
      (fun n ↦
        (Fintype.card (AmbientEdge (m n)) : ℝ) *
          (sparseBernoulliParameter lam (m n)).variance /
            (m n : ℝ) ^ 2) := by
    have hsimple : Tendsto
        (fun n ↦
          (lam / 2) * (1 - ((m n : ℝ))⁻¹) *
            (1 - lam * ((m n : ℝ))⁻¹) * ((m n : ℝ))⁻¹)
        atTop (𝓝 0) := by
      simpa using
        (((tendsto_const_nhds.mul honeMinusInv).mul honeMinusLambdaInv).mul hinv)
    apply hsimple.congr'
    filter_upwards [hp, hmpos] with n hpn hmn
    rw [card_ambientEdge]
    unfold BernoulliParameter.variance
    rw [hpn, Nat.cast_choose_two]
    field_simp [(ne_of_gt hmn)]
  simpa only [erdosRenyiLaw] using
    (bernoulliCount_div_tendstoInProbability
      (E := fun n ↦ AmbientEdge (m n))
      (θ := fun n ↦ sparseBernoulliParameter lam (m n))
      (scale := fun n ↦ (m n : ℝ)) (limit := lam / 2)
      hmpos hmean hvariance)

end ErdosRenyi

end

end LowDegree
