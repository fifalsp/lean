import LowDegree.Asymptotics.Basic
import LowDegree.Fourier
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Perm

/-!
# The finite planted-subgraph model

This file connects the finite Bernoulli Fourier kernel to the graph model in
the paper.  At size `n`, coordinates are the edges of the complete graph on
`Fin n`.  A deterministic plant is moved by a uniformly random permutation,
and its likelihood is the corresponding finite mixture of fixed-edge
likelihoods.

For a fixed real `c > 0`, the expression `c / n` is not a Bernoulli parameter
at `n = 0` and can also fail to be less than one for finitely many small `n`.
The canonical sparse family below therefore uses the harmless value `1/2` on
that finite prefix and proves explicitly that its parameter is exactly `c / n`
eventually.  No asymptotic statement relies on a silently clamped parameter.
-/

namespace LowDegree

open Filter

open scoped BigOperators

noncomputable section

/-- Extensionality of finite laws by their mass functions. -/
theorem FiniteLaw.ext_mass
    {Ω : Type*} [Fintype Ω] {p q : FiniteLaw Ω}
    (h : p.mass = q.mass) : p = q := by
  cases p with
  | mk pMass pNonneg pSum =>
      cases q with
      | mk qMass qNonneg qSum =>
          cases h
          rfl

/-- A sequence of honest Bernoulli parameters which agrees eventually with
the sparse density `c / n`. -/
structure SparseBernoulliFamily (c : ℝ) where
  parameter : ℕ → BernoulliParameter
  eventually_p_eq : ∀ᶠ n in atTop, (parameter n).p = c / (n : ℝ)

/-- The parameter used in the canonical sparse family.  The `1/2` branch is
confined to the finite set of indices where `c / n` is not in `(0,1)`. -/
noncomputable def sparseBernoulliParameter (c : ℝ) (n : ℕ) : BernoulliParameter :=
  if h : 0 < c / (n : ℝ) ∧ c / (n : ℝ) < 1 then
    ⟨c / (n : ℝ), h.1, h.2⟩
  else
    ⟨1 / 2, by norm_num, by norm_num⟩

theorem sparseBernoulliParameter_p_eq_of
    {c : ℝ} {n : ℕ}
    (hp : 0 < c / (n : ℝ)) (hp_one : c / (n : ℝ) < 1) :
    (sparseBernoulliParameter c n).p = c / (n : ℝ) := by
  simp [sparseBernoulliParameter, hp, hp_one]

/-- Positivity of `c` makes the canonical parameter equal to `c/n` at all
sufficiently large indices. -/
theorem eventually_sparseBernoulliParameter_p_eq
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, (sparseBernoulliParameter c n).p = c / (n : ℝ) := by
  filter_upwards [eventually_ge_atTop (⌈c⌉₊ + 1)] with n hn
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hc_lt_n : c < (n : ℝ) := by
    have hceil_lt : (⌈c⌉₊ : ℝ) < n := by
      exact_mod_cast (Nat.lt_of_succ_le hn)
    exact (Nat.le_ceil c).trans_lt hceil_lt
  exact sparseBernoulliParameter_p_eq_of
    (div_pos hc hn_real_pos) ((div_lt_one hn_real_pos).2 hc_lt_n)

/-- The canonical eventual `G(n,c/n)` parameter family. -/
noncomputable def SparseBernoulliFamily.canonical
    (c : ℝ) (hc : 0 < c) : SparseBernoulliFamily c where
  parameter := sparseBernoulliParameter c
  eventually_p_eq := eventually_sparseBernoulliParameter_p_eq hc

/-- The coordinate type for simple graphs on `Fin n`: unordered,
non-diagonal pairs of vertices. -/
abbrev AmbientEdge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- Move a spanning plant by a permutation of its ambient vertices. -/
def permutedPlant {n : ℕ} (plant : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  plant.map σ.toEmbedding

/-- The edge coordinates forced by a permuted plant. -/
noncomputable def permutedPlantEdges {n : ℕ}
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Finset (AmbientEdge n) := by
  classical
  exact Finset.univ.filter fun e ↦
    (e : Sym2 (Fin n)) ∈ (permutedPlant plant σ).edgeSet

@[simp]
theorem mem_permutedPlantEdges_iff {n : ℕ}
    (plant : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (e : AmbientEdge n) :
    e ∈ permutedPlantEdges plant σ ↔
      (e : Sym2 (Fin n)) ∈ (permutedPlant plant σ).edgeSet := by
  classical
  simp [permutedPlantEdges]

/-- The positive mass of one permutation under the uniform distribution. -/
noncomputable def uniformPermutationWeight (n : ℕ) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹

theorem uniformPermutationWeight_pos (n : ℕ) :
    0 < uniformPermutationWeight n := by
  apply inv_pos.mpr
  exact_mod_cast (Fintype.card_pos_iff.mpr
    ⟨Equiv.refl (Fin n)⟩ : 0 < Fintype.card (Equiv.Perm (Fin n)))

/-- Number of ambient permutations whose image of `plant` contains `S`. -/
noncomputable def permutationContainmentCount {n : ℕ}
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦
    S ⊆ permutedPlantEdges plant σ).card

/-- The likelihood ratio obtained by moving the plant by a uniformly random
ambient permutation and then forcing every edge in the image to be present. -/
noncomputable def plantedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    uniformPermutationWeight n * forcedLikelihood θ (permutedPlantEdges plant σ) x

theorem forcedLikelihood_nonneg
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E)
    (x : BooleanConfiguration E) :
    0 ≤ forcedLikelihood θ A x := by
  unfold forcedLikelihood
  apply Finset.prod_nonneg
  intro e _he
  apply div_nonneg _ θ.p_pos.le
  cases x e <;> simp [BernoulliParameter.bitValue]

theorem plantedLikelihood_nonneg {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    0 ≤ plantedLikelihood θ plant x := by
  classical
  unfold plantedLikelihood
  exact Finset.sum_nonneg fun σ _ ↦
    mul_nonneg (uniformPermutationWeight_pos n).le
      (forcedLikelihood_nonneg θ (permutedPlantEdges plant σ) x)

/-- Exact Fourier coefficient of the random-permutation mixture.  The first
factor is the finite probability that the permuted plant contains `S`; the
second is the fixed-forcing coefficient already proved in `Fourier.lean`. -/
theorem fourierCoeff_plantedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (S : Finset (AmbientEdge n)) :
    fourierCoeff θ (plantedLikelihood θ plant) S =
      ((permutationContainmentCount plant S : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
        θ.forcedWeight ^ S.card := by
  classical
  have hlinear := bernoulliInner_finset_sum_left
    (E := AmbientEdge n) θ
    (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun _ ↦ uniformPermutationWeight n)
    (fun σ ↦ forcedLikelihood θ (permutedPlantEdges plant σ))
    (fourierCharacter θ S)
  change fourierCoeff θ (plantedLikelihood θ plant) S = _
  rw [show fourierCoeff θ (plantedLikelihood θ plant) S =
      ∑ σ : Equiv.Perm (Fin n), uniformPermutationWeight n *
        fourierCoeff θ (forcedLikelihood θ (permutedPlantEdges plant σ)) S by
      simpa only [plantedLikelihood, fourierCoeff] using hlinear]
  simp_rw [fourierCoeff_forcedLikelihood]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [show (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦
      S ⊆ permutedPlantEdges plant σ).card =
      permutationContainmentCount plant S by
      rfl]
  simp only [uniformPermutationWeight, div_eq_mul_inv]
  ring

/-- A fixed forcing likelihood has null expectation one. -/
theorem bernoulliExpectation_forcedLikelihood
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (A : Finset E) :
    bernoulliExpectation θ (forcedLikelihood θ A) = 1 := by
  have h := fourierCoeff_forcedLikelihood θ A (∅ : Finset E)
  rw [fourierCoeff_empty] at h
  simpa using h

/-- The random-permutation mixture is normalized under the null law. -/
theorem bernoulliExpectation_plantedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) :
    bernoulliExpectation θ (plantedLikelihood θ plant) = 1 := by
  rw [← fourierCoeff_empty, fourierCoeff_plantedLikelihood]
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨Equiv.refl (Fin n)⟩ : 0 < Fintype.card (Equiv.Perm (Fin n))).ne'
  simp [permutationContainmentCount, hcard]

/-- The Erdős--Rényi null law on graph-edge coordinates. -/
def erdosRenyiLaw {n : ℕ} (θ : BernoulliParameter) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) :=
  bernoulliProductLaw θ

/-- Push a finite law through independent coordinate resampling. -/
noncomputable def resampleLaw
    {E : Type*} [Fintype E] [DecidableEq E]
    (θ : BernoulliParameter) (ε : NoiseRate)
    (p : FiniteLaw (BooleanConfiguration E)) :
    FiniteLaw (BooleanConfiguration E) where
  mass y := ∑ x, p.mass x * bernoulliNoiseTransition θ (ε : ℝ) x y
  mass_nonneg y := Finset.sum_nonneg fun x _ ↦
    mul_nonneg (p.mass_nonneg x)
      (bernoulliNoiseTransition_nonneg θ ε.2.1.le ε.2.2.le x y)
  sum_mass := by
    calc
      (∑ y, ∑ x, p.mass x * bernoulliNoiseTransition θ (ε : ℝ) x y) =
          ∑ x, ∑ y, p.mass x * bernoulliNoiseTransition θ (ε : ℝ) x y := by
            rw [Finset.sum_comm]
      _ = ∑ x, p.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum, sum_bernoulliNoiseTransition, mul_one]
      _ = 1 := p.sum_mass

/-- Independent resampling preserves the Erdős--Rényi null law. -/
theorem resampleLaw_erdosRenyiLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate) :
    resampleLaw θ ε (erdosRenyiLaw (n := n) θ) = erdosRenyiLaw θ := by
  apply FiniteLaw.ext_mass
  funext y
  change
    (∑ x, bernoulliProductMass θ x *
      bernoulliNoiseTransition θ (ε : ℝ) x y) =
      bernoulliProductMass θ y
  calc
    (∑ x, bernoulliProductMass θ x *
        bernoulliNoiseTransition θ (ε : ℝ) x y) =
        ∑ x, bernoulliProductMass θ y *
          bernoulliNoiseTransition θ (ε : ℝ) y x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [bernoulliNoise_detailedBalance]
    _ = bernoulliProductMass θ y := by
      rw [← Finset.mul_sum, sum_bernoulliNoiseTransition, mul_one]

/-- The planted law, constructed from its nonnegative normalized density
relative to the Erdős--Rényi law. -/
noncomputable def plantedLaw {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) where
  mass x := bernoulliProductMass θ x * plantedLikelihood θ plant x
  mass_nonneg x := mul_nonneg (bernoulliProductMass_nonneg θ x)
    (plantedLikelihood_nonneg θ plant x)
  sum_mass := by
    simpa only [bernoulliExpectation] using
      bernoulliExpectation_plantedLikelihood θ plant

@[simp]
theorem plantedLaw_mass {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    (plantedLaw θ plant).mass x =
      (erdosRenyiLaw θ).mass x * plantedLikelihood θ plant x :=
  rfl

/-- The mixture function is the pointwise likelihood ratio of the planted
law with respect to the Erdős--Rényi null. -/
theorem plantedLikelihood_isLikelihoodRatio {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) :
    FiniteLaw.IsLikelihoodRatio (plantedLaw θ plant)
      (erdosRenyiLaw θ) (plantedLikelihood θ plant) := by
  intro x
  rfl

/-- The density after independently resampling every ambient edge at rate
`ε`.  Reversibility of the null kernel makes this the edge-noise operator
applied to the original planted density. -/
def noisedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    BooleanConfiguration (AmbientEdge n) → ℝ :=
  edgeNoise θ (ε : ℝ) (plantedLikelihood θ plant)

theorem noisedLikelihood_nonneg {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    0 ≤ noisedLikelihood θ ε plant x := by
  classical
  unfold noisedLikelihood edgeNoise
  exact Finset.sum_nonneg fun y _ ↦
    mul_nonneg
      (bernoulliNoiseTransition_nonneg θ ε.2.1.le ε.2.2.le x y)
      (plantedLikelihood_nonneg θ plant y)

/-- Edge noise preserves normalization of the planted density. -/
theorem bernoulliExpectation_noisedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    bernoulliExpectation θ (noisedLikelihood θ ε plant) = 1 := by
  rw [noisedLikelihood, bernoulliExpectation_edgeNoise,
    bernoulliExpectation_plantedLikelihood]

/-- The noised planted law, built from the noised density relative to the
unchanged Erdős--Rényi null law. -/
noncomputable def noisedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    FiniteLaw (BooleanConfiguration (AmbientEdge n)) where
  mass x := bernoulliProductMass θ x * noisedLikelihood θ ε plant x
  mass_nonneg x := mul_nonneg (bernoulliProductMass_nonneg θ x)
    (noisedLikelihood_nonneg θ ε plant x)
  sum_mass := by
    simpa only [bernoulliExpectation] using
      bernoulliExpectation_noisedLikelihood θ ε plant

@[simp]
theorem noisedPlantedLaw_mass {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n))
    (x : BooleanConfiguration (AmbientEdge n)) :
    (noisedPlantedLaw θ ε plant).mass x =
      (erdosRenyiLaw θ).mass x * noisedLikelihood θ ε plant x :=
  rfl

/-- The noised density is a genuine likelihood ratio. -/
theorem noisedLikelihood_isLikelihoodRatio {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    FiniteLaw.IsLikelihoodRatio (noisedPlantedLaw θ ε plant)
      (erdosRenyiLaw θ) (noisedLikelihood θ ε plant) := by
  intro x
  rfl

/-- The density-defined noised law is exactly the Markov pushforward of the
planted law.  This is the finite detailed-balance identity connecting the
likelihood construction to the generative resampling operation. -/
theorem resampleLaw_plantedLaw_eq_noisedPlantedLaw {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    resampleLaw θ ε (plantedLaw θ plant) =
      noisedPlantedLaw θ ε plant := by
  apply FiniteLaw.ext_mass
  funext y
  change
    (∑ x, (bernoulliProductMass θ x * plantedLikelihood θ plant x) *
      bernoulliNoiseTransition θ (ε : ℝ) x y) =
    bernoulliProductMass θ y *
      (∑ x, bernoulliNoiseTransition θ (ε : ℝ) y x *
        plantedLikelihood θ plant x)
  calc
    (∑ x, (bernoulliProductMass θ x * plantedLikelihood θ plant x) *
        bernoulliNoiseTransition θ (ε : ℝ) x y) =
        ∑ x, (bernoulliProductMass θ x *
          bernoulliNoiseTransition θ (ε : ℝ) x y) *
          plantedLikelihood θ plant x := by
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = ∑ x, (bernoulliProductMass θ y *
          bernoulliNoiseTransition θ (ε : ℝ) y x) *
          plantedLikelihood θ plant x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [bernoulliNoise_detailedBalance]
    _ = bernoulliProductMass θ y *
        (∑ x, bernoulliNoiseTransition θ (ε : ℝ) y x *
          plantedLikelihood θ plant x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring

/-- Exact coefficient formula after edge resampling. -/
theorem fourierCoeff_noisedLikelihood {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) (S : Finset (AmbientEdge n)) :
    fourierCoeff θ (noisedLikelihood θ ε plant) S =
      (1 - (ε : ℝ)) ^ S.card *
        ((permutationContainmentCount plant S : ℝ) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
        θ.forcedWeight ^ S.card := by
  rw [noisedLikelihood, fourierCoeff_edgeNoise,
    fourierCoeff_plantedLikelihood]
  ring

/-! ## Model-realized observables -/

/-- The degree-`D` likelihood-ratio projection for the concrete planted law. -/
noncomputable def plantedLowDegreeLikelihood {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (D : ℕ) :
    BooleanConfiguration (AmbientEdge n) → ℝ :=
  lowDegreeProjection θ D (plantedLikelihood θ plant)

/-- Squared low-degree norm appearing in the premise of Theorems 1.1 and
1.2, now definitionally tied to the planted law. -/
noncomputable def plantedLowDegreeNormSq {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (D : ℕ) : ℝ :=
  bernoulliInner θ
    (plantedLowDegreeLikelihood θ plant D)
    (plantedLowDegreeLikelihood θ plant D)

/-- Squared full norm of the noised likelihood ratio. -/
noncomputable def plantedNoisedNormSq {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) : ℝ :=
  bernoulliInner θ
    (noisedLikelihood θ ε plant)
    (noisedLikelihood θ ε plant)

/-- Total variation between the concrete noised planted and null laws. -/
noncomputable def plantedNoisedTotalVariation {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) : ℝ :=
  (noisedPlantedLaw θ ε plant).tv (erdosRenyiLaw θ)

/-- Exact labeled-support Parseval formula for the low-degree norm.  Regrouping
this finite sum by graph isomorphism class yields paper Equation (3.5). -/
theorem plantedLowDegreeNormSq_eq_sum {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (D : ℕ) :
    plantedLowDegreeNormSq θ plant D =
      ∑ S : Finset (AmbientEdge n) with S.card ≤ D,
        ((((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2) := by
  rw [plantedLowDegreeNormSq, plantedLowDegreeLikelihood,
    lowDegreeProjection_norm_sq]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourierCoeff_plantedLikelihood]

/-- Exact labeled-support Parseval formula for the full noised norm.  This is
the finite, pre-regrouping form of paper Equation (3.6). -/
theorem plantedNoisedNormSq_eq_sum {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    plantedNoisedNormSq θ ε plant =
      ∑ S : Finset (AmbientEdge n),
        (((1 - (ε : ℝ)) ^ S.card *
          ((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2) := by
  rw [plantedNoisedNormSq, fourierParseval_sq]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourierCoeff_noisedLikelihood]

/-- The empty Fourier support contributes exactly one to both moment sums. -/
theorem emptySupport_contribution (n : ℕ) (plant : SimpleGraph (Fin n))
    (θ : BernoulliParameter) :
    ((((permutationContainmentCount plant (∅ : Finset (AmbientEdge n)) : ℝ) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
        θ.forcedWeight ^ (∅ : Finset (AmbientEdge n)).card) ^ 2) = 1 := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨Equiv.refl (Fin n)⟩ : 0 < Fintype.card (Equiv.Perm (Fin n))).ne'
  simp [permutationContainmentCount, hcard]

/-- Equation (3.5) before regrouping by graph isomorphism class: subtracting
the empty support leaves a finite sum of nonnegative nonempty-support weights. -/
theorem plantedLowDegreeNormSq_sub_one_eq_sum_nonempty {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (D : ℕ) :
    plantedLowDegreeNormSq θ plant D - 1 =
      ∑ S : Finset (AmbientEdge n) with S.card ≤ D ∧ S.Nonempty,
        ((((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2) := by
  classical
  let weight : Finset (AmbientEdge n) → ℝ := fun S ↦
    ((((permutationContainmentCount plant S : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
      θ.forcedWeight ^ S.card) ^ 2)
  let supports : Finset (Finset (AmbientEdge n)) :=
    Finset.univ.filter fun S ↦ S.card ≤ D
  have hempty_mem : (∅ : Finset (AmbientEdge n)) ∈ supports := by
    simp [supports]
  have hempty_weight : weight ∅ = 1 := by
    exact emptySupport_contribution n plant θ
  have herase : supports.erase ∅ =
      Finset.univ.filter (fun S : Finset (AmbientEdge n) ↦
        S.card ≤ D ∧ S.Nonempty) := by
    ext S
    simp [supports, Finset.nonempty_iff_ne_empty, and_comm]
  rw [plantedLowDegreeNormSq_eq_sum]
  change (∑ S ∈ supports, weight S) - 1 = _
  have hsplit : (∑ S ∈ supports, weight S) =
      (∑ S ∈ supports.erase ∅, weight S) + weight ∅ :=
    (Finset.sum_erase_add supports weight hempty_mem).symm
  rw [hsplit, hempty_weight, herase]
  simp only [add_sub_cancel_right]
  rfl

/-- Equation (3.6) before isomorphism-class regrouping, again with the empty
support removed explicitly. -/
theorem plantedNoisedNormSq_sub_one_eq_sum_nonempty {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    plantedNoisedNormSq θ ε plant - 1 =
      ∑ S : Finset (AmbientEdge n) with S.Nonempty,
        (((1 - (ε : ℝ)) ^ S.card *
          ((permutationContainmentCount plant S : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
          θ.forcedWeight ^ S.card) ^ 2) := by
  classical
  let weight : Finset (AmbientEdge n) → ℝ := fun S ↦
    (((1 - (ε : ℝ)) ^ S.card *
      ((permutationContainmentCount plant S : ℝ) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
      θ.forcedWeight ^ S.card) ^ 2)
  have hempty_weight : weight ∅ = 1 := by
    dsimp [weight]
    simpa using emptySupport_contribution n plant θ
  have hempty_mem : (∅ : Finset (AmbientEdge n)) ∈
      (Finset.univ : Finset (Finset (AmbientEdge n))) := Finset.mem_univ _
  rw [plantedNoisedNormSq_eq_sum]
  change (∑ S : Finset (AmbientEdge n), weight S) - 1 = _
  have hsplit : (∑ S : Finset (AmbientEdge n), weight S) =
      (∑ S ∈ (Finset.univ : Finset (Finset (AmbientEdge n))).erase ∅,
        weight S) + weight ∅ :=
    (Finset.sum_erase_add Finset.univ weight hempty_mem).symm
  rw [hsplit, hempty_weight]
  have herase :
      (Finset.univ : Finset (Finset (AmbientEdge n))).erase ∅ =
        Finset.univ.filter (fun S : Finset (AmbientEdge n) ↦ S.Nonempty) := by
    ext S
    simp [Finset.nonempty_iff_ne_empty]
  rw [herase]
  simp only [add_sub_cancel_right]
  rfl

theorem one_le_plantedLowDegreeNormSq {n : ℕ}
    (θ : BernoulliParameter) (plant : SimpleGraph (Fin n)) (D : ℕ) :
    1 ≤ plantedLowDegreeNormSq θ plant D := by
  rw [← sub_nonneg, plantedLowDegreeNormSq_sub_one_eq_sum_nonempty]
  exact Finset.sum_nonneg fun S _ ↦ sq_nonneg _

theorem one_le_plantedNoisedNormSq {n : ℕ}
    (θ : BernoulliParameter) (ε : NoiseRate)
    (plant : SimpleGraph (Fin n)) :
    1 ≤ plantedNoisedNormSq θ ε plant := by
  rw [← sub_nonneg, plantedNoisedNormSq_sub_one_eq_sum_nonempty]
  exact Finset.sum_nonneg fun S _ ↦ sq_nonneg _

end

end LowDegree
