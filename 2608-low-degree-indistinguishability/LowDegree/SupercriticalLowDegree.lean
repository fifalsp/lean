import LowDegree.RandomPlantFourier
import LowDegree.Asymptotics.ModelConsequences
import LowDegree.Combinatorics.GraphShapeClasses
import LowDegree.SupercriticalCanonicalScales
import LowDegree.SupercriticalSupportRestrictions
import LowDegree.SupercriticalShapeRestrictions
import LowDegree.SupercriticalInjectionBounds
import LowDegree.SupercriticalEnumerationBounds
import LowDegree.SupercriticalLargeC
import LowDegree.SupercriticalCountingBound
import LowDegree.SupercriticalExcessBound
import LowDegree.Combinatorics.FiniteDoubleRegrouping

/-!
# Low-degree indistinguishability for the supercritical appendix

This file formalizes the low-degree half of Appendix Theorem A.1 for the
actual twice-truncated, uniformly injected plant law.  We first expose the
canonical likelihood ratio and its exact support-level Parseval expansion
(Equation (A.5)); the subsequent bounds specialize Equations (A.6)--(A.12).
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The squared norm of the degree-`D_n` projection of the actual appendix
alternative likelihood ratio. -/
noncomputable def appendixLowDegreeNormSq
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) : ℝ :=
  randomForcedLowDegreeNormSq
    (sparseBernoulliParameter c n)
    (appendixInjectedTruncatedPlantLaw lam r gamma hr n)
    (appendixDegreeCutoff n)

/-- The function projected in `appendixLowDegreeNormSq` is the likelihood
ratio of the actual appendix alternative with respect to `G(n,c/n)`. -/
theorem appendixAlternativeLikelihood_isLikelihoodRatio
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    FiniteLaw.IsLikelihoodRatio
      (appendixAlternativeLaw c lam r gamma hr n)
      (erdosRenyiLaw (n := n) (sparseBernoulliParameter c n))
      (randomForcedLikelihood
        (sparseBernoulliParameter c n)
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n)) := by
  exact randomForcedLikelihood_isLikelihoodRatio _ _

/-- **Equation (A.5), for the actual appendix law.**  This is the exact
finite Parseval identity before graph-isomorphism regrouping. -/
theorem appendixLowDegreeNormSq_sub_one_eq_sum_nonempty
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixLowDegreeNormSq c lam r gamma hr n - 1 =
      ∑ S : Finset (AmbientEdge n) with
          S.card ≤ appendixDegreeCutoff n ∧ S.Nonempty,
        (randomPlantContainmentProbability
            (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S *
          (sparseBernoulliParameter c n).forcedWeight ^ S.card) ^ 2 := by
  exact randomForcedLowDegreeNormSq_sub_one_eq_sum_nonempty _ _ _

/-- Equation (A.5) regrouped without duplication by nonempty graph shape.
The inner sum ranges over the `(n)_v/|Aut(F)|` ambient copies of the shape;
unlike the deterministic-plant formula, the containment probability here is
the one for the actual random twice-truncated plant. -/
theorem appendixLowDegreeNormSq_sub_one_eq_sum_supportClasses
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixLowDegreeNormSq c lam r gamma hr n - 1 =
      ∑ C : AmbientSupportClass n with
          C.shape.edgeCount ≤ appendixDegreeCutoff n,
        ∑ copy : C.shape.ConcreteCopy (⊤ : SimpleGraph (Fin n)),
          (randomPlantContainmentProbability
              (appendixInjectedTruncatedPlantLaw lam r gamma hr n)
              (C.shape.concreteCopyEdges copy) *
            (sparseBernoulliParameter c n).forcedWeight ^
              C.shape.edgeCount) ^ 2 := by
  rw [appendixLowDegreeNormSq_sub_one_eq_sum_nonempty]
  simpa only [FiniteGraphShape.card_concreteCopyEdges] using
    sum_nonempty_ambientSupports_degree_eq_sum_concreteCopyClasses
      (n := n) (D := appendixDegreeCutoff n)
      (fun S ↦
        (randomPlantContainmentProbability
            (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S *
          (sparseBernoulliParameter c n).forcedWeight ^ S.card) ^ 2)

/-- Finite set of nonempty Fourier supports below the canonical degree
cutoff. -/
noncomputable def appendixLowDegreeSupports (n : ℕ) :
    Finset (Finset (AmbientEdge n)) :=
  (Finset.univ : Finset (Finset (AmbientEdge n))).filter fun S ↦
    S.card ≤ appendixDegreeCutoff n ∧ S.Nonempty

/-- One actual Fourier weight in Equation (A.5). -/
noncomputable def appendixFourierSupportWeight
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ)
    (S : Finset (AmbientEdge n)) : ℝ :=
  (randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S *
    (sparseBernoulliParameter c n).forcedWeight ^ S.card) ^ 2

/-! ## The graph enumeration in (A.9) -/

/-- Number of incident vertices of an ambient edge support. -/
noncomputable def ambientSupportVertexCount {n : ℕ}
    (S : Finset (AmbientEdge n)) : ℕ :=
  (FiniteGraphShape.supportShape (ambientSupportGraph S)).vertexCount

/-- Edge count of the support shape is literally the cardinality of the
ambient edge support. -/
@[simp]
theorem supportShape_ambientSupportGraph_edgeCount {n : ℕ}
    (S : Finset (AmbientEdge n)) :
    (FiniteGraphShape.supportShape
      (ambientSupportGraph S)).edgeCount = S.card := by
  let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
  let copy := supportConcreteCopy S
  rw [← F.card_concreteCopyEdges copy,
    concreteCopyEdges_supportConcreteCopy]

/-- A nonempty simple-graph support has at least two incident vertices. -/
theorem two_le_ambientSupportVertexCount_of_nonempty {n : ℕ}
    {S : Finset (AmbientEdge n)} (hS : S.Nonempty) :
    2 ≤ ambientSupportVertexCount S := by
  let U := ambientSupportVertexFinset S
  obtain ⟨e, he⟩ := hS
  have heU : e ∈ ambientEdgesOn U :=
    support_subset_ambientEdgesOn_supportVertexFinset S he
  have hcardPos : 0 < (ambientEdgesOn U).card :=
    (show (ambientEdgesOn U).Nonempty from ⟨e, heU⟩).card_pos
  have hchooseNe : U.card.choose 2 ≠ 0 := by
    rw [card_ambientEdgesOn] at hcardPos
    exact hcardPos.ne'
  have htwo : 2 ≤ U.card := Nat.choose_ne_zero_iff.mp hchooseNe
  simpa only [U, ambientSupportVertexCount,
    card_ambientSupportVertexFinset] using htwo

/-- Supports with prescribed numbers of incident vertices and edges. -/
noncomputable def ambientSupportsAtCounts (n v e : ℕ) :
    Finset (Finset (AmbientEdge n)) :=
  (Finset.univ : Finset (Finset (AmbientEdge n))).filter fun S ↦
    ambientSupportVertexCount S = v ∧ S.card = e

/-- The actual low-degree supports in one occupied-vertex/edge-count
fiber. -/
noncomputable def appendixLowDegreeCountFiber (n v e : ℕ) :
    Finset (Finset (AmbientEdge n)) :=
  (appendixLowDegreeSupports n).filter fun S ↦
    ambientSupportVertexCount S = v ∧ S.card = e

/-- The contribution of one count fiber to the exact Parseval sum. -/
noncomputable def appendixLowDegreeCountFiberMass
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (n v e : ℕ) : ℝ :=
  ∑ S ∈ appendixLowDegreeCountFiber n v e,
    appendixFourierSupportWeight c lam r gamma hr n S

/-- A count fiber is active when one of its actual containment
coefficients is positive. -/
def AppendixLowDegreeCountFiberActive
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (n v e : ℕ) : Prop :=
  ∃ S ∈ appendixLowDegreeCountFiber n v e,
    0 < randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S

/-- Elementary graph enumeration used in (A.9): the number of labelled
ambient supports with `v` occupied vertices and `e` edges is at most
`choose(n,v) choose(choose(v,2),e)`.  The proof encodes a support by its
canonical occupied vertex set and then by an `e`-subset of the possible
edges on that set. -/
theorem card_ambientSupportsAtCounts_le (n v e : ℕ) :
    (ambientSupportsAtCounts n v e).card ≤
      n.choose v * (v.choose 2).choose e := by
  let cover : Finset (Finset (AmbientEdge n)) :=
    (vertexSubsets n v).biUnion fun U ↦
      (ambientEdgesOn U).powersetCard e
  have hsubset : ambientSupportsAtCounts n v e ⊆ cover := by
    intro S hS
    rw [ambientSupportsAtCounts, Finset.mem_filter] at hS
    obtain ⟨U, hUcard, hSU⟩ :=
      exists_vertexFinset_card_eq_supportShape_vertexCount S
    have hUcard' : U.card = v := by
      simpa only [ambientSupportVertexCount] using hUcard.trans hS.2.1
    change S ∈ (vertexSubsets n v).biUnion (fun U ↦
      (ambientEdgesOn U).powersetCard e)
    rw [Finset.mem_biUnion]
    refine ⟨U, ?_, ?_⟩
    · rw [vertexSubsets, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ U, hUcard'⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hSU, hS.2.2⟩
  calc
    (ambientSupportsAtCounts n v e).card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ U ∈ vertexSubsets n v,
        ((ambientEdgesOn U).powersetCard e).card :=
      Finset.card_biUnion_le
    _ = n.choose v * (v.choose 2).choose e := by
      calc
        (∑ U ∈ vertexSubsets n v,
            ((ambientEdgesOn U).powersetCard e).card) =
            ∑ _U ∈ vertexSubsets n v, (v.choose 2).choose e := by
          apply Finset.sum_congr rfl
          intro U hU
          have hUcard : U.card = v := by
            simpa [vertexSubsets] using
              (Finset.mem_powersetCard.mp hU).2
          rw [Finset.card_powersetCard, card_ambientEdgesOn, hUcard]
        _ = n.choose v * (v.choose 2).choose e := by
          simp [card_vertexSubsets]

/-- Exact, duplicate-free regrouping of A.5 by occupied vertex and edge
counts. -/
theorem appendixLowDegreeExcess_eq_sum_countFibers
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixLowDegreeNormSq c lam r gamma hr n - 1 =
      ∑ v ∈ Finset.range (2 * appendixDegreeCutoff n + 1),
        ∑ e ∈ Finset.range (appendixDegreeCutoff n + 1),
          ∑ S ∈ appendixLowDegreeSupports n with
              ambientSupportVertexCount S = v ∧ S.card = e,
            appendixFourierSupportWeight c lam r gamma hr n S := by
  rw [appendixLowDegreeNormSq_sub_one_eq_sum_nonempty]
  change (∑ S ∈ appendixLowDegreeSupports n,
      appendixFourierSupportWeight c lam r gamma hr n S) = _
  apply sum_eq_sum_two_count_fibers
  · intro S hS
    rw [appendixLowDegreeSupports, Finset.mem_filter] at hS
    let F := FiniteGraphShape.supportShape (ambientSupportGraph S)
    have hvle : F.vertexCount ≤ 2 * F.edgeCount :=
      F.vertexCount_le_twice_edgeCount
    have hedge : F.edgeCount = S.card :=
      supportShape_ambientSupportGraph_edgeCount S
    have hvle' : F.vertexCount ≤ 2 * S.card := by
      simpa only [hedge] using hvle
    change F.vertexCount < 2 * appendixDegreeCutoff n + 1
    omega
  · intro S hS
    rw [appendixLowDegreeSupports, Finset.mem_filter] at hS
    omega

/-- The exact count-fiber regrouping, packaged using
`appendixLowDegreeCountFiberMass`. -/
theorem appendixLowDegreeExcess_eq_sum_countFiberMass
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    appendixLowDegreeNormSq c lam r gamma hr n - 1 =
      ∑ v ∈ Finset.range (2 * appendixDegreeCutoff n + 1),
        ∑ e ∈ Finset.range (appendixDegreeCutoff n + 1),
          appendixLowDegreeCountFiberMass c lam r gamma hr n v e := by
  simpa only [appendixLowDegreeCountFiberMass,
    appendixLowDegreeCountFiber, Finset.sum_filter] using
    appendixLowDegreeExcess_eq_sum_countFibers c lam r gamma hr n

/-- An inactive count fiber contributes zero to (A.5). -/
theorem appendixLowDegreeCountFiberMass_eq_zero_of_not_active
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    {n v e : ℕ}
    (hinactive : ¬ AppendixLowDegreeCountFiberActive
      lam r gamma hr n v e) :
    appendixLowDegreeCountFiberMass c lam r gamma hr n v e = 0 := by
  unfold appendixLowDegreeCountFiberMass
  apply Finset.sum_eq_zero
  intro S hS
  have hqnonneg : 0 ≤ randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S :=
    randomPlantContainmentProbability_nonneg _ _
  have hqnotpos : ¬ 0 < randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S := by
    intro hqpos
    exact hinactive ⟨S, hS, hqpos⟩
  have hqzero : randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S = 0 :=
    le_antisymm (le_of_not_gt hqnotpos) hqnonneg
  unfold appendixFourierSupportWeight
  rw [hqzero]
  norm_num

/-- The small parameter `a_n=m_n^2/n` used after Equation (A.8). -/
noncomputable def appendixLowDegreeSmallParameter (r : ℝ) (n : ℕ) : ℝ :=
  (appendixPlantSize r n : ℝ) ^ 2 / (n : ℝ)

/-- The signed natural power `a^(v-e)` used in (A.9), written without an
integer exponent. -/
noncomputable def appendixSignedScalePower (a : ℝ) (v e : ℕ) : ℝ :=
  if e ≤ v then a ^ (v - e) else a⁻¹ ^ (e - v)

/-- The individual `(v,e)` summand in the right side of (A.9). -/
noncomputable def appendixA9Term
    (a b : ℝ) (v e : ℕ) : ℝ :=
  2 ^ v * appendixGraphCountingFactor v e *
    appendixSignedScalePower a v e * b ^ e

/-- At the canonical scales every support in the low-degree sum eventually
uses at most `n` incident vertices. -/
theorem eventually_two_appendixDegreeCutoff_le_index
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 2 * appendixDegreeCutoff n ≤ n := by
  filter_upwards
      [eventually_two_appendixDegreeCutoff_le_appendixPlantSize_rpow
        hr.1 (by norm_num : (0 : ℝ) < 1)] with n hn
  have hn' : 2 * appendixDegreeCutoff n ≤ appendixPlantSize r n := by
    rw [Real.rpow_one] at hn
    exact_mod_cast hn
  exact hn'.trans
    (appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n)

/-- The stronger margin used to bound `(n)_v` below by `(n/2)^v`. -/
theorem eventually_four_appendixDegreeCutoff_le_index
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 4 * appendixDegreeCutoff n ≤ n := by
  have htwoD :=
    eventually_two_appendixDegreeCutoff_le_appendixPlantSize_rpow
      hr.1 (by norm_num : (0 : ℝ) < 1)
  have hmratio := appendixPlantSize_div_index_vanishes (by linarith [hr.2])
  have hhalf : ∀ᶠ n : ℕ in atTop,
      (appendixPlantSize r n : ℝ) / (n : ℝ) < 1 / 2 :=
    (tendsto_order.1 hmratio).2 (1 / 2) (by norm_num)
  filter_upwards [htwoD, hhalf,
      Filter.eventually_gt_atTop (0 : ℕ)] with n hD hm hn
  rw [Real.rpow_one] at hD
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmle : 2 * (appendixPlantSize r n : ℝ) ≤ (n : ℝ) := by
    have := (div_lt_iff₀ hnreal).mp hm
    linarith
  have hresult : ((4 * appendixDegreeCutoff n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast at hD ⊢
    linarith
  exact_mod_cast hresult

/-- Elementary upper bound `(m)_v≤m^v`. -/
theorem fallingFactorial_le_pow_cast (m v : ℕ) :
    fallingFactorial m v ≤ (m : ℝ) ^ v := by
  unfold fallingFactorial
  exact_mod_cast Nat.descFactorial_le_pow m v

/-- If `2v≤n`, every factor in `(n)_v` is at least `n/2`. -/
theorem half_pow_le_fallingFactorial
    {n v : ℕ} (h2v : 2 * v ≤ n) :
    ((n : ℝ) / 2) ^ v ≤ fallingFactorial n v := by
  have hvn : v ≤ n := by omega
  rw [fallingFactorial_eq_prod n v hvn]
  calc
    ((n : ℝ) / 2) ^ v =
        ∏ _j ∈ Finset.range v, ((n : ℝ) / 2) := by
      simp only [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range v, ((n : ℝ) - (j : ℝ)) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        have hjv : j < v := Finset.mem_range.mp hj
        have hreal : 2 * (j : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (show 2 * j ≤ n by omega)
        linarith

theorem choose_mul_fallingRatio_sq_le
    {n m v : ℕ} (hn : 0 < n) (h2v : 2 * v ≤ n) :
    (n.choose v : ℝ) *
        (fallingFactorial m v / fallingFactorial n v) ^ 2 ≤
      (2 : ℝ) ^ v / (v.factorial : ℝ) *
        ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) := by
  have hvn : v ≤ n := by omega
  have hfn0 : 0 < fallingFactorial n v := by
    have hne := fallingFactorial_ne_zero hvn
    have hnonneg : 0 ≤ fallingFactorial n v := by
      unfold fallingFactorial
      positivity
    exact hnonneg.lt_of_ne' hne
  have hfm0 : 0 ≤ fallingFactorial m v := by
    unfold fallingFactorial
    positivity
  have hfac0 : (0 : ℝ) < v.factorial := by positivity
  have hchoose : (n.choose v : ℝ) =
      fallingFactorial n v / (v.factorial : ℝ) := by
    rw [eq_div_iff hfac0.ne']
    rw [← Nat.cast_mul, fallingFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    exact Nat.mul_comm _ _
  have hfmle := fallingFactorial_le_pow_cast m v
  have hfmSq : fallingFactorial m v ^ 2 ≤ (m : ℝ) ^ (2 * v) := by
    calc
      fallingFactorial m v ^ 2 ≤ ((m : ℝ) ^ v) ^ 2 := by gcongr
      _ = (m : ℝ) ^ (2 * v) := by rw [← pow_mul]; congr 1; omega
  have hfnlower := half_pow_le_fallingFactorial h2v
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hchoose]
  calc
    fallingFactorial n v / (v.factorial : ℝ) *
          (fallingFactorial m v / fallingFactorial n v) ^ 2 =
        fallingFactorial m v ^ 2 /
          ((v.factorial : ℝ) * fallingFactorial n v) := by
      field_simp [hfn0.ne', hfac0.ne']
    _ ≤ (m : ℝ) ^ (2 * v) /
          ((v.factorial : ℝ) * (((n : ℝ) / 2) ^ v)) := by
      apply div_le_div₀
      · positivity
      · exact hfmSq
      · positivity
      · exact mul_le_mul_of_nonneg_left hfnlower hfac0.le
    _ = (2 : ℝ) ^ v / (v.factorial : ℝ) *
          ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) := by
      rw [div_pow]
      field_simp [hfac0.ne', hnreal.ne']

/-- Variant of `choose_mul_fallingRatio_sq_le` for the sufficient A.6
bound with numerator `m^v`.  This avoids evaluating the injection-fit
probability exactly while producing the same A.9 scale. -/
theorem choose_mul_pow_fallingRatio_sq_le
    {n m v : ℕ} (hn : 0 < n) (h2v : 2 * v ≤ n) :
    (n.choose v : ℝ) *
        (((m : ℝ) ^ v / fallingFactorial n v) ^ 2) ≤
      (2 : ℝ) ^ v / (v.factorial : ℝ) *
        ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) := by
  have hvn : v ≤ n := by omega
  have hfn0 : 0 < fallingFactorial n v := by
    have hne := fallingFactorial_ne_zero hvn
    have hnonneg : 0 ≤ fallingFactorial n v := by
      unfold fallingFactorial
      positivity
    exact hnonneg.lt_of_ne' hne
  have hfac0 : (0 : ℝ) < v.factorial := by positivity
  have hchoose : (n.choose v : ℝ) =
      fallingFactorial n v / (v.factorial : ℝ) := by
    rw [eq_div_iff hfac0.ne']
    rw [← Nat.cast_mul, fallingFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    exact Nat.mul_comm _ _
  have hfnlower := half_pow_le_fallingFactorial h2v
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hchoose]
  calc
    fallingFactorial n v / (v.factorial : ℝ) *
          (((m : ℝ) ^ v / fallingFactorial n v) ^ 2) =
        (m : ℝ) ^ (2 * v) /
          ((v.factorial : ℝ) * fallingFactorial n v) := by
      rw [div_pow, ← pow_mul]
      field_simp [hfn0.ne', hfac0.ne']
      congr 1
      omega
    _ ≤ (m : ℝ) ^ (2 * v) /
          ((v.factorial : ℝ) * (((n : ℝ) / 2) ^ v)) := by
      apply div_le_div₀
      · positivity
      · rfl
      · positivity
      · exact mul_le_mul_of_nonneg_left hfnlower hfac0.le
    _ = (2 : ℝ) ^ v / (v.factorial : ℝ) *
          ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) := by
      rw [div_pow]
      field_simp [hfac0.ne', hnreal.ne']

/-- Algebraic normalization producing `a^(v-e)b^e` in (A.9). -/
theorem appendix_sparseScale_identity
    {n m e v : ℕ} {c lam : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hc : c ≠ 0) :
    ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) *
        (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e =
      appendixSignedScalePower
          ((m : ℝ) ^ 2 / (n : ℝ)) v e *
        (lam ^ 2 / c) ^ e := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let a : ℝ := (m : ℝ) ^ 2 / (n : ℝ)
  have ha0 : a ≠ 0 := div_ne_zero (pow_ne_zero _ hm0) hn0
  by_cases hev : e ≤ v
  · rw [appendixSignedScalePower, if_pos hev]
    rw [pow_sub₀ a ha0 hev]
    dsimp [a]
    simp only [div_pow, mul_pow]
    field_simp [hn0, hm0, hc]
    ring

  · have hve : v ≤ e := Nat.le_of_not_ge hev
    rw [appendixSignedScalePower, if_neg hev]
    rw [pow_sub₀ a⁻¹ (inv_ne_zero ha0) hve]
    dsimp [a]
    simp only [div_pow, mul_pow, inv_div]
    field_simp [hn0, hm0, hc]
    ring

/-- The quantitative A.6 bound, after summing over at most all labelled
supports with fixed `(v,e)`, has exactly the A.9 summand as a majorant. -/
theorem appendix_countedContainmentWeight_le_A9Term
    {n m v e : ℕ} {c lam : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hc : 0 < c)
    (h2v : 2 * v ≤ n) :
    (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) *
        ((fallingFactorial m v / fallingFactorial n v) *
          (lam / (m : ℝ)) ^ e) ^ 2 * ((n : ℝ) / c) ^ e ≤
      appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
        (lam ^ 2 / c) v e := by
  have hratio := choose_mul_fallingRatio_sq_le hn h2v (m := m)
  have hchoose0 : 0 ≤ ((v.choose 2).choose e : ℝ) := by positivity
  have hplant0 : 0 ≤ (lam / (m : ℝ)) ^ (2 * e) := by
    rw [pow_mul]
    positivity
  have hnull0 : 0 ≤ ((n : ℝ) / c) ^ e := by positivity
  calc
    (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) *
          ((fallingFactorial m v / fallingFactorial n v) *
            (lam / (m : ℝ)) ^ e) ^ 2 * ((n : ℝ) / c) ^ e =
        ((v.choose 2).choose e : ℝ) *
          ((n.choose v : ℝ) *
            (fallingFactorial m v / fallingFactorial n v) ^ 2) *
          (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e := by
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ ((v.choose 2).choose e : ℝ) *
          ((2 : ℝ) ^ v / (v.factorial : ℝ) *
            ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v)) *
          (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hchoose0) hplant0)
        hnull0
    _ = (2 : ℝ) ^ v * appendixGraphCountingFactor v e *
          (((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) *
            (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e) := by
      unfold appendixGraphCountingFactor
      ring
    _ = appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
          (lam ^ 2 / c) v e := by
      rw [appendix_sparseScale_identity hn hm hc.ne']
      unfold appendixA9Term
      ring

/-- A.9 summand bound corresponding to the sufficient A.6 estimate with
`m^v/(n)_v` in place of the smaller exact injection factor. -/
theorem appendix_countedPowContainmentWeight_le_A9Term
    {n m v e : ℕ} {c lam : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hc : 0 < c)
    (h2v : 2 * v ≤ n) :
    (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) *
        (((m : ℝ) ^ v / fallingFactorial n v) *
          (lam / (m : ℝ)) ^ e) ^ 2 * ((n : ℝ) / c) ^ e ≤
      appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
        (lam ^ 2 / c) v e := by
  have hratio := choose_mul_pow_fallingRatio_sq_le hn h2v (m := m)
  have hchoose0 : 0 ≤ ((v.choose 2).choose e : ℝ) := by positivity
  have hplant0 : 0 ≤ (lam / (m : ℝ)) ^ (2 * e) := by
    rw [pow_mul]
    positivity
  have hnull0 : 0 ≤ ((n : ℝ) / c) ^ e := by positivity
  calc
    (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) *
          (((m : ℝ) ^ v / fallingFactorial n v) *
            (lam / (m : ℝ)) ^ e) ^ 2 * ((n : ℝ) / c) ^ e =
        ((v.choose 2).choose e : ℝ) *
          ((n.choose v : ℝ) *
            (((m : ℝ) ^ v / fallingFactorial n v) ^ 2)) *
          (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e := by
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ ((v.choose 2).choose e : ℝ) *
          ((2 : ℝ) ^ v / (v.factorial : ℝ) *
            ((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v)) *
          (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hchoose0) hplant0)
        hnull0
    _ = (2 : ℝ) ^ v * appendixGraphCountingFactor v e *
          (((m : ℝ) ^ (2 * v) / (n : ℝ) ^ v) *
            (lam / (m : ℝ)) ^ (2 * e) * ((n : ℝ) / c) ^ e) := by
      unfold appendixGraphCountingFactor
      ring
    _ = appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
          (lam ^ 2 / c) v e := by
      rw [appendix_sparseScale_identity hn hm hc.ne']
      unfold appendixA9Term
      ring

/-- Converts any A.6-type containment bound into a bound for the squared
Fourier weight, including the Bernoulli odds factor. -/
theorem appendixFourierSupportWeight_le_of_containment
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    {n : ℕ} (S : Finset (AmbientEdge n))
    (hn : 0 < n) (hc : 0 < c)
    (hp : (sparseBernoulliParameter c n).p = c / (n : ℝ))
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hcontainment : randomPlantContainmentProbability
      (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S ≤ Q) :
    appendixFourierSupportWeight c lam r gamma hr n S ≤
      Q ^ 2 * ((n : ℝ) / c) ^ S.card := by
  let theta := sparseBernoulliParameter c n
  let q := randomPlantContainmentProbability
    (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hforcedSq : theta.forcedWeight ^ 2 ≤ (n : ℝ) / c := by
    calc
      theta.forcedWeight ^ 2 = (1 - theta.p) / theta.p :=
        theta.forcedWeight_sq
      _ ≤ 1 / theta.p := by
        apply (div_le_div_iff_of_pos_right theta.p_pos).2
        linarith [theta.p_pos]
      _ = (n : ℝ) / c := by
        rw [show theta.p = c / (n : ℝ) by exact hp]
        field_simp [hc.ne', hnreal.ne']
  have hforcedPow : (theta.forcedWeight ^ S.card) ^ 2 ≤
      ((n : ℝ) / c) ^ S.card := by
    calc
      (theta.forcedWeight ^ S.card) ^ 2 =
          (theta.forcedWeight ^ 2) ^ S.card := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ ≤ ((n : ℝ) / c) ^ S.card :=
        pow_le_pow_left₀ (sq_nonneg theta.forcedWeight) hforcedSq _
  have hqnonneg : 0 ≤ q :=
    randomPlantContainmentProbability_nonneg _ _
  have hqSq : q ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ hqnonneg hQ).2 hcontainment
  unfold appendixFourierSupportWeight
  change (q * theta.forcedWeight ^ S.card) ^ 2 ≤ _
  rw [mul_pow]
  exact mul_le_mul hqSq hforcedPow
    (sq_nonneg _) (sq_nonneg Q)

/-- Summing the sufficient A.6 bound over one `(v,e)` fiber and applying
the elementary labelled-support count yields the corresponding A.9 term. -/
theorem appendixLowDegreeCountFiberMass_le_A9Term_of_containment
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    {n m v e : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hp : (sparseBernoulliParameter c n).p = c / (n : ℝ))
    (h2v : 2 * v ≤ n)
    (hcontainment : ∀ S ∈ appendixLowDegreeCountFiber n v e,
      randomPlantContainmentProbability
          (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S ≤
        ((m : ℝ) ^ v / fallingFactorial n v) *
          (lam / (m : ℝ)) ^ e) :
    appendixLowDegreeCountFiberMass c lam r gamma hr n v e ≤
      appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
        (lam ^ 2 / c) v e := by
  let Q : ℝ := ((m : ℝ) ^ v / fallingFactorial n v) *
    (lam / (m : ℝ)) ^ e
  let C : ℝ := Q ^ 2 * ((n : ℝ) / c) ^ e
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have hmreal : (0 : ℝ) ≤ m := by exact_mod_cast hm.le
    have hfall : 0 ≤ fallingFactorial n v := by
      unfold fallingFactorial
      positivity
    exact mul_nonneg
      (div_nonneg (pow_nonneg hmreal v) hfall)
      (pow_nonneg (div_nonneg hlam hmreal) e)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfiberSubset : appendixLowDegreeCountFiber n v e ⊆
      ambientSupportsAtCounts n v e := by
    intro S hS
    rw [appendixLowDegreeCountFiber, Finset.mem_filter] at hS
    rw [ambientSupportsAtCounts, Finset.mem_filter]
    exact ⟨Finset.mem_univ S, hS.2⟩
  have hcardNat : (appendixLowDegreeCountFiber n v e).card ≤
      n.choose v * (v.choose 2).choose e :=
    (Finset.card_le_card hfiberSubset).trans
      (card_ambientSupportsAtCounts_le n v e)
  have hcard : ((appendixLowDegreeCountFiber n v e).card : ℝ) ≤
      (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) := by
    exact_mod_cast hcardNat
  have hterm (S : Finset (AmbientEdge n))
      (hS : S ∈ appendixLowDegreeCountFiber n v e) :
      appendixFourierSupportWeight c lam r gamma hr n S ≤ C := by
    have heS : S.card = e := by
      rw [appendixLowDegreeCountFiber, Finset.mem_filter] at hS
      exact hS.2.2
    have hbound := appendixFourierSupportWeight_le_of_containment
      c lam r gamma hr S hn hc hp hQ (by
        simpa only [Q] using hcontainment S hS)
    simpa only [C, Q, heS] using hbound
  calc
    appendixLowDegreeCountFiberMass c lam r gamma hr n v e ≤
        ∑ _S ∈ appendixLowDegreeCountFiber n v e, C := by
      unfold appendixLowDegreeCountFiberMass
      exact Finset.sum_le_sum hterm
    _ = ((appendixLowDegreeCountFiber n v e).card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n.choose v : ℝ) * ((v.choose 2).choose e : ℝ)) * C :=
      mul_le_mul_of_nonneg_right hcard hC
    _ = (n.choose v : ℝ) * ((v.choose 2).choose e : ℝ) *
        (((m : ℝ) ^ v / fallingFactorial n v) *
          (lam / (m : ℝ)) ^ e) ^ 2 * ((n : ℝ) / c) ^ e := by
      dsimp [C, Q]
      ring
    _ ≤ appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ))
          (lam ^ 2 / c) v e :=
      appendix_countedPowContainmentWeight_le_A9Term hn hm hc h2v

/-- The local-density condition in (A.7) absorbs the only nonconstant
factor left by `appendixGraphCountingFactor_le`.  Uniformly for
`v≤2D_n`, one has `v^(e-v)≤exp(A)^v`. -/
theorem eventually_appendixGraphCounting_excess_le
    {A r : ℝ} (hA : 0 ≤ A)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ v e : ℕ,
      1 ≤ v → v ≤ 2 * appendixDegreeCutoff n →
      (e : ℝ) ≤ (1 + A / Real.log (n : ℝ)) * (v : ℝ) →
      (v : ℝ) ^ (e - v) ≤ (Real.exp A) ^ v := by
  filter_upwards [eventually_two_appendixDegreeCutoff_le_index hr,
      Filter.eventually_gt_atTop (1 : ℕ)] with n hDn hn v e hv hvD hdensity
  have hvn : v ≤ n := hvD.trans hDn
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hvone : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hlogv0 : 0 ≤ Real.log (v : ℝ) := Real.log_nonneg hvone
  have hlogle : Real.log (v : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log hvpos (by exact_mod_cast hvn)
  by_cases hev : e ≤ v
  · rw [Nat.sub_eq_zero_of_le hev, pow_zero]
    have hexpOne : 1 ≤ Real.exp A := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
    exact one_le_pow₀ hexpOne
  · have hve : v ≤ e := Nat.le_of_not_ge hev
    have hd : ((e - v : ℕ) : ℝ) ≤
        A / Real.log (n : ℝ) * (v : ℝ) := by
      rw [Nat.cast_sub hve]
      nlinarith
    have hcoef0 : 0 ≤ A / Real.log (n : ℝ) * (v : ℝ) := by
      positivity
    have hprod : ((e - v : ℕ) : ℝ) * Real.log (v : ℝ) ≤
        A * (v : ℝ) := by
      calc
        ((e - v : ℕ) : ℝ) * Real.log (v : ℝ) ≤
            (A / Real.log (n : ℝ) * (v : ℝ)) *
              Real.log (v : ℝ) :=
          mul_le_mul_of_nonneg_right hd hlogv0
        _ ≤ (A / Real.log (n : ℝ) * (v : ℝ)) *
              Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlogle hcoef0
        _ = A * (v : ℝ) := by field_simp
    calc
      (v : ℝ) ^ (e - v) =
          (Real.exp (Real.log (v : ℝ))) ^ (e - v) := by
        rw [Real.exp_log hvpos]
      _ =
          Real.exp (((e - v : ℕ) : ℝ) * Real.log (v : ℝ)) := by
        exact (Real.exp_nat_mul (Real.log (v : ℝ)) (e - v)).symm
      _ ≤ Real.exp (A * (v : ℝ)) := Real.exp_le_exp.mpr hprod
      _ = (Real.exp A) ^ v := by
        simpa only [Nat.cast_ofNat, mul_comm] using Real.exp_nat_mul A v

/-- Admissible forest edge counts for a fixed vertex count in (A.9). -/
noncomputable def appendixA9ForestEdges
    (A : ℝ) (n v : ℕ) : Finset ℕ :=
  (Finset.Icc ((v + 1) / 2)
      (min (appendixDegreeCutoff n) (v - 1))).filter
    fun e ↦ (e : ℝ) ≤
      (1 + A / Real.log (n : ℝ)) * (v : ℝ)

/-- Admissible cyclic/excess edge counts for a fixed vertex count. -/
noncomputable def appendixA9CyclicEdges
    (A : ℝ) (n v : ℕ) : Finset ℕ :=
  (Finset.Icc v (appendixDegreeCutoff n)).filter fun e ↦
    (e : ℝ) ≤ (1 + A / Real.log (n : ℝ)) * (v : ℝ)

/-- **Equation (A.9), graph-counted finite sum.**

The two summands are the disjoint alternatives `e<v` and
`e≥v, v>g_n`.  The outer cap is `2D_n`, and
`appendixGraphCountingFactor v e` is
`choose(choose(v,2),e)/v!`. -/
noncomputable def appendixA9Enumeration
    (A c lam r : ℝ) (n : ℕ) : ℝ :=
  let a := appendixLowDegreeSmallParameter r n
  let b := lam ^ 2 / c
  ∑ v ∈ Finset.Ico 2 (2 * appendixDegreeCutoff n + 1),
      ∑ e ∈ appendixA9ForestEdges A n v, appendixA9Term a b v e
    +
    ∑ v ∈ Finset.Ico (appendixCycleCutoff n + 1)
        (2 * appendixDegreeCutoff n + 1),
      ∑ e ∈ appendixA9CyclicEdges A n v, appendixA9Term a b v e

/-- The rectangular-index version of the two disjoint pieces in (A.9).
It is convenient when comparing the exact `(v,e)` regrouping of (A.5)
with the filtered forest and cyclic sums. -/
noncomputable def appendixA9IndexedTerm
    (A c lam r : ℝ) (n v e : ℕ) : ℝ :=
  let t := appendixA9Term (appendixLowDegreeSmallParameter r n)
    (lam ^ 2 / c) v e
  (if 2 ≤ v ∧ e ∈ appendixA9ForestEdges A n v then t else 0) +
    (if appendixCycleCutoff n < v ∧
        e ∈ appendixA9CyclicEdges A n v then t else 0)

/-- Summing the rectangular-index form gives exactly the displayed A.9
enumeration. -/
theorem sum_appendixA9IndexedTerm_eq_enumeration
    (A c lam r : ℝ) (n : ℕ) :
    (∑ v ∈ Finset.range (2 * appendixDegreeCutoff n + 1),
      ∑ e ∈ Finset.range (appendixDegreeCutoff n + 1),
        appendixA9IndexedTerm A c lam r n v e) =
      appendixA9Enumeration A c lam r n := by
  let cap := 2 * appendixDegreeCutoff n + 1
  let D := appendixDegreeCutoff n
  let t : ℕ → ℕ → ℝ := fun v e ↦
    appendixA9Term (appendixLowDegreeSmallParameter r n)
      (lam ^ 2 / c) v e
  have hforestSubset (v : ℕ) :
      appendixA9ForestEdges A n v ⊆ Finset.range (D + 1) := by
    intro e he
    rw [appendixA9ForestEdges, Finset.mem_filter,
      Finset.mem_Icc] at he
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_min.mp he.1.2).1)
  have hcyclicSubset (v : ℕ) :
      appendixA9CyclicEdges A n v ⊆ Finset.range (D + 1) := by
    intro e he
    rw [appendixA9CyclicEdges, Finset.mem_filter,
      Finset.mem_Icc] at he
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le he.1.2
  have hinnerForest (v : ℕ) :
      (∑ e ∈ Finset.range (D + 1),
          if e ∈ appendixA9ForestEdges A n v then t v e else 0) =
        ∑ e ∈ appendixA9ForestEdges A n v, t v e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext e
      simp only [Finset.mem_filter]
      constructor
      · exact fun he ↦ he.2
      · exact fun he ↦ ⟨hforestSubset v he, he⟩
    · intro e _he
      rfl
  have hinnerCyclic (v : ℕ) :
      (∑ e ∈ Finset.range (D + 1),
          if e ∈ appendixA9CyclicEdges A n v then t v e else 0) =
        ∑ e ∈ appendixA9CyclicEdges A n v, t v e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext e
      simp only [Finset.mem_filter]
      constructor
      · exact fun he ↦ he.2
      · exact fun he ↦ ⟨hcyclicSubset v he, he⟩
    · intro e _he
      rfl
  have houterForest :
      (∑ v ∈ Finset.range cap,
          if 2 ≤ v then
            ∑ e ∈ appendixA9ForestEdges A n v, t v e else 0) =
        ∑ v ∈ Finset.Ico 2 cap,
          ∑ e ∈ appendixA9ForestEdges A n v, t v e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext v
      simp [Finset.mem_Ico]
      tauto
    · intro v _hv
      rfl
  have houterCyclic :
      (∑ v ∈ Finset.range cap,
          if appendixCycleCutoff n < v then
            ∑ e ∈ appendixA9CyclicEdges A n v, t v e else 0) =
        ∑ v ∈ Finset.Ico (appendixCycleCutoff n + 1) cap,
          ∑ e ∈ appendixA9CyclicEdges A n v, t v e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext v
      simp [Finset.mem_Ico]
      omega
    · intro v _hv
      rfl
  unfold appendixA9IndexedTerm appendixA9Enumeration
  change (∑ v ∈ Finset.range cap,
      ∑ e ∈ Finset.range (D + 1),
        ((if 2 ≤ v ∧ e ∈ appendixA9ForestEdges A n v then
            t v e else 0) +
          (if appendixCycleCutoff n < v ∧
              e ∈ appendixA9CyclicEdges A n v then t v e else 0))) =
    (∑ v ∈ Finset.Ico 2 cap,
        ∑ e ∈ appendixA9ForestEdges A n v, t v e) +
      ∑ v ∈ Finset.Ico (appendixCycleCutoff n + 1) cap,
        ∑ e ∈ appendixA9CyclicEdges A n v, t v e
  simp_rw [ite_and]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  simp_rw [hinnerForest, hinnerCyclic]
  rw [houterForest, houterCyclic]

/-- Every active count fiber in the exact A.5 regrouping eventually obeys
the complete combinatorial restrictions used in A.9. -/
theorem eventually_active_appendixLowDegreeCountFiber_restrictions
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, ∀ v e : ℕ,
      AppendixLowDegreeCountFiberActive lam r gamma hr n v e →
      2 ≤ v ∧ v ≤ 2 * e ∧ e ≤ appendixDegreeCutoff n ∧
        ((e : ℝ) ≤
          (1 + localSparsitySlackConstant lam r gamma /
            Real.log (n : ℝ)) * (v : ℝ)) ∧
        (v ≤ e → appendixCycleCutoff n < v) := by
  filter_upwards
      [eventually_positive_appendixContainment_shapeRestrictions
        lam r gamma hr hgamma] with n hshape
  intro v e hactive
  rcases hactive with ⟨S, hSfiber, hpos⟩
  rw [appendixLowDegreeCountFiber, Finset.mem_filter] at hSfiber
  rcases hSfiber with ⟨hSlow, hv, he⟩
  have hSlow' : S.card ≤ appendixDegreeCutoff n ∧ S.Nonempty := by
    simpa [appendixLowDegreeSupports] using hSlow
  rcases hSlow' with ⟨heD, hSnonempty⟩
  change (FiniteGraphShape.supportShape
    (ambientSupportGraph S)).vertexCount = v at hv
  have hrestr := hshape S hSnonempty heD hpos
  have hv2 : 2 ≤ v := by
    simpa only [ambientSupportVertexCount, hv] using
      two_le_ambientSupportVertexCount_of_nonempty hSnonempty
  have hvle : v ≤ 2 * e := by
    simpa only [hv, he] using
      supportShape_vertexCount_le_twice_card S
  have hdensity : (e : ℝ) ≤
      (1 + localSparsitySlackConstant lam r gamma /
        Real.log (n : ℝ)) * (v : ℝ) := by
    simpa only [he, hv] using hrestr.1
  refine ⟨hv2, hvle, he ▸ heD, hdensity, ?_⟩
  intro hve
  have hg := hrestr.2 (by
    rw [supportShape_ambientSupportGraph_edgeCount]
    simpa only [hv, he] using hve)
  simpa only [hv] using hg

/-- The restrictions above say exactly that an active rectangular index
selects one (and only one) of the two A.9 pieces. -/
theorem appendixA9IndexedTerm_eq_term_of_restrictions
    (A c lam r : ℝ) {n v e : ℕ}
    (hv2 : 2 ≤ v) (hve2 : v ≤ 2 * e)
    (heD : e ≤ appendixDegreeCutoff n)
    (hdensity : (e : ℝ) ≤
      (1 + A / Real.log (n : ℝ)) * (v : ℝ))
    (hcycle : v ≤ e → appendixCycleCutoff n < v) :
    appendixA9IndexedTerm A c lam r n v e =
      appendixA9Term (appendixLowDegreeSmallParameter r n)
        (lam ^ 2 / c) v e := by
  by_cases hev : e < v
  · have hforest : e ∈ appendixA9ForestEdges A n v := by
      rw [appendixA9ForestEdges, Finset.mem_filter,
        Finset.mem_Icc]
      refine ⟨⟨?_, (Nat.le_min).2 ⟨heD, by omega⟩⟩, hdensity⟩
      omega
    have hncyclic : e ∉ appendixA9CyclicEdges A n v := by
      intro hecyclic
      rw [appendixA9CyclicEdges, Finset.mem_filter,
        Finset.mem_Icc] at hecyclic
      omega
    simp [appendixA9IndexedTerm, hv2, hforest, hncyclic]
  · have hve : v ≤ e := Nat.le_of_not_gt hev
    have hcyclicMem : e ∈ appendixA9CyclicEdges A n v := by
      rw [appendixA9CyclicEdges, Finset.mem_filter,
        Finset.mem_Icc]
      exact ⟨⟨hve, heD⟩, hdensity⟩
    have hnforest : e ∉ appendixA9ForestEdges A n v := by
      intro heforest
      rw [appendixA9ForestEdges, Finset.mem_filter,
        Finset.mem_Icc] at heforest
      have := (Nat.le_min.mp heforest.1.2).2
      omega
    simp [appendixA9IndexedTerm, hv2, hnforest,
      hcycle hve, hcyclicMem]

/-- The fixed exponential counting constant produced by (A.10). -/
noncomputable def appendixCountingConstant : ℝ := 4 * Real.exp 3

/-- The fixed excess constant `C_A` used in (A.12). -/
noncomputable def appendixExcessConstant (A : ℝ) : ℝ :=
  Real.exp (2 * A)

/-- The forest ratio `2K√b` in (A.11), where `b=λ²/c`. -/
noncomputable def appendixForestGeometricRatio
    (lam K c : ℝ) : ℝ :=
  2 * K * Real.sqrt (lam ^ 2 / c)

/-- The cyclic/excess ratio `2 K C_A b` in (A.12). -/
noncomputable def appendixCyclicGeometricRatio
    (lam K C_A c : ℝ) : ℝ :=
  2 * K * C_A * (lam ^ 2 / c)

theorem appendixCountingConstant_pos : 0 < appendixCountingConstant := by
  unfold appendixCountingConstant
  positivity

theorem appendixExcessConstant_pos (A : ℝ) :
    0 < appendixExcessConstant A := by
  unfold appendixExcessConstant
  positivity

theorem appendixA9Term_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (v e : ℕ) :
    0 ≤ appendixA9Term a b v e := by
  unfold appendixA9Term appendixGraphCountingFactor
  have hscale : 0 ≤ appendixSignedScalePower a v e := by
    unfold appendixSignedScalePower
    split <;> positivity
  positivity

theorem appendixA9IndexedTerm_nonneg
    (A c lam r : ℝ) (n v e : ℕ) (hc : 0 < c) :
    0 ≤ appendixA9IndexedTerm A c lam r n v e := by
  have ha : 0 ≤ appendixLowDegreeSmallParameter r n := by
    unfold appendixLowDegreeSmallParameter
    positivity
  have hb : 0 ≤ lam ^ 2 / c := by positivity
  have ht : 0 ≤ appendixA9Term
      (appendixLowDegreeSmallParameter r n) (lam ^ 2 / c) v e :=
    appendixA9Term_nonneg ha hb v e
  unfold appendixA9IndexedTerm
  dsimp only
  exact add_nonneg (by split <;> simp_all) (by split <;> simp_all)

/-- One forest-range summand is bounded by the geometric weight used in
(A.11). -/
theorem appendixA9Term_forest_le
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    {v e : ℕ} (hv : 1 ≤ v) (hlower : v ≤ 2 * e) (he : e < v) :
    appendixA9Term a b v e ≤
      a * (2 * appendixCountingConstant * Real.sqrt b) ^ v := by
  have heUpper : e ≤ 2 * v := by omega
  have hcount := appendixGraphCountingFactor_le hv hlower heUpper
  have hcount' : appendixGraphCountingFactor v e ≤
      appendixCountingConstant ^ v := by
    simpa [appendixCountingConstant, Nat.sub_eq_zero_of_le he.le]
      using hcount
  have hscale : appendixSignedScalePower a v e = a ^ (v - e) := by
    simp [appendixSignedScalePower, he.le]
  have hdiff : v - e ≠ 0 := by omega
  have hscaleLe : a ^ (v - e) ≤ a :=
    pow_le_of_le_one ha0 ha1 hdiff
  have hsqrt0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsqrt1 : Real.sqrt b ≤ 1 := by
    nlinarith [Real.sq_sqrt hb0]
  have hbpow : b ^ e ≤ (Real.sqrt b) ^ v := by
    calc
      b ^ e = ((Real.sqrt b) ^ 2) ^ e := by
        rw [Real.sq_sqrt hb0]
      _ = (Real.sqrt b) ^ (2 * e) := by rw [pow_mul]
      _ ≤ (Real.sqrt b) ^ v :=
        pow_le_pow_of_le_one hsqrt0 hsqrt1 hlower
  have hK0 : 0 ≤ appendixCountingConstant :=
    appendixCountingConstant_pos.le
  have hfront0 : 0 ≤ 2 ^ v * appendixCountingConstant ^ v :=
    mul_nonneg (pow_nonneg (by norm_num) v) (pow_nonneg hK0 v)
  unfold appendixA9Term
  rw [hscale]
  calc
    2 ^ v * appendixGraphCountingFactor v e * a ^ (v - e) * b ^ e ≤
        2 ^ v * appendixCountingConstant ^ v * a ^ (v - e) * b ^ e := by
      gcongr
    _ ≤ 2 ^ v * appendixCountingConstant ^ v * a * b ^ e := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscaleLe hfront0)
        (pow_nonneg hb0 e)
    _ ≤ 2 ^ v * appendixCountingConstant ^ v * a *
        (Real.sqrt b) ^ v := by
      exact mul_le_mul_of_nonneg_left hbpow (mul_nonneg hfront0 ha0)
    _ = a * (2 * appendixCountingConstant * Real.sqrt b) ^ v := by
      rw [mul_pow, mul_pow]
      ring

/-- One cyclic/excess summand is bounded by the geometric weight used in
(A.12).  The factor `v^(e-v)` from (A.10) and the negative power of
`a=m²/n` are controlled together by the local-density restriction. -/
theorem appendixA9Term_cyclic_le
    (A b : ℝ) {n m v e : ℕ}
    (hn : 1 < n) (hm : 1 ≤ m) (hv : 1 ≤ v) (hvn : v ≤ n)
    (hve : v ≤ e) (heUpper : e ≤ 2 * v)
    (hdensity : (e : ℝ) ≤
      (1 + A / Real.log (n : ℝ)) * (v : ℝ))
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ)) b v e ≤
      (2 * appendixCountingConstant * appendixExcessConstant A * b) ^ v := by
  let a : ℝ := (m : ℝ) ^ 2 / (n : ℝ)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (zero_lt_one.trans_le hm)
  have ha : 0 < a := by dsimp [a]; positivity
  have hcount := appendixGraphCountingFactor_le hv (by omega) heUpper
  have hscale : appendixSignedScalePower a v e = a⁻¹ ^ (e - v) := by
    unfold appendixSignedScalePower
    split
    · have hev : e = v := by omega
      subst e
      simp
    · rfl
  have hcombine : (v : ℝ) ^ (e - v) * a⁻¹ ^ (e - v) =
      ((v : ℝ) / a) ^ (e - v) := by
    rw [← mul_pow, div_eq_mul_inv]
  have hexcess : ((v : ℝ) / a) ^ (e - v) ≤
      appendixExcessConstant A ^ v := by
    dsimp [a, appendixExcessConstant]
    exact appendix_excess_power_le A hn hm hvn hve hdensity
  have hbpow : b ^ e ≤ b ^ v :=
    pow_le_pow_of_le_one hb0 hb1.le hve
  have hK0 : 0 ≤ appendixCountingConstant :=
    appendixCountingConstant_pos.le
  have htwoK0 : 0 ≤ 2 * appendixCountingConstant :=
    mul_nonneg (by norm_num) hK0
  have hCA0 : 0 ≤ appendixExcessConstant A :=
    (appendixExcessConstant_pos A).le
  have htwo0 : (0 : ℝ) ≤ 2 ^ v := pow_nonneg (by norm_num) v
  have hcount' : appendixGraphCountingFactor v e ≤
      appendixCountingConstant ^ v * (v : ℝ) ^ (e - v) := by
    simpa only [appendixCountingConstant] using hcount
  unfold appendixA9Term
  change 2 ^ v * appendixGraphCountingFactor v e *
      appendixSignedScalePower a v e * b ^ e ≤ _
  rw [hscale]
  calc
    2 ^ v * appendixGraphCountingFactor v e * a⁻¹ ^ (e - v) * b ^ e ≤
        2 ^ v *
          (appendixCountingConstant ^ v * (v : ℝ) ^ (e - v)) *
          a⁻¹ ^ (e - v) * b ^ e := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcount' htwo0)
          (pow_nonneg (inv_nonneg.mpr ha.le) (e - v)))
        (pow_nonneg hb0 e)
    _ = (2 * appendixCountingConstant) ^ v *
          (((v : ℝ) / a) ^ (e - v)) * b ^ e := by
      calc
        2 ^ v *
              (appendixCountingConstant ^ v * (v : ℝ) ^ (e - v)) *
              a⁻¹ ^ (e - v) * b ^ e =
            (2 ^ v * appendixCountingConstant ^ v) *
              ((v : ℝ) ^ (e - v) * a⁻¹ ^ (e - v)) * b ^ e := by ring
        _ = (2 ^ v * appendixCountingConstant ^ v) *
              (((v : ℝ) / a) ^ (e - v)) * b ^ e := by rw [hcombine]
        _ = (2 * appendixCountingConstant) ^ v *
              (((v : ℝ) / a) ^ (e - v)) * b ^ e := by
          rw [mul_pow]
    _ ≤ (2 * appendixCountingConstant) ^ v *
          (appendixExcessConstant A ^ v * b ^ e) := by
      calc
        (2 * appendixCountingConstant) ^ v *
              ((v : ℝ) / a) ^ (e - v) * b ^ e ≤
            (2 * appendixCountingConstant) ^ v *
              appendixExcessConstant A ^ v * b ^ e :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexcess (pow_nonneg htwoK0 v))
            (pow_nonneg hb0 e)
        _ = (2 * appendixCountingConstant) ^ v *
              (appendixExcessConstant A ^ v * b ^ e) := by ring
    _ ≤ (2 * appendixCountingConstant) ^ v *
          (appendixExcessConstant A ^ v * b ^ v) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbpow (pow_nonneg hCA0 v))
        (pow_nonneg htwoK0 v)
    _ = (2 * appendixCountingConstant * appendixExcessConstant A * b) ^ v := by
      rw [mul_pow, mul_pow, mul_pow]
      ring

theorem card_appendixA9ForestEdges_le (A : ℝ) (n v : ℕ) (hv : 1 ≤ v) :
    (appendixA9ForestEdges A n v).card ≤ v := by
  have hsubset : appendixA9ForestEdges A n v ⊆ Finset.range v := by
    intro e he
    rw [appendixA9ForestEdges, Finset.mem_filter,
      Finset.mem_Icc] at he
    rw [Finset.mem_range]
    have hev : e ≤ v - 1 := (Nat.le_min.mp he.1.2).2
    omega
  simpa using Finset.card_le_card hsubset

theorem card_appendixA9CyclicEdges_le
    {A : ℝ} {n v : ℕ} (hv : 1 ≤ v)
    (hdelta : A / Real.log (n : ℝ) ≤ 1) :
    (appendixA9CyclicEdges A n v).card ≤ 2 * v := by
  have hsubset : appendixA9CyclicEdges A n v ⊆ Finset.Icc v (2 * v) := by
    intro e he
    rw [appendixA9CyclicEdges, Finset.mem_filter,
      Finset.mem_Icc] at he
    rw [Finset.mem_Icc]
    refine ⟨he.1.1, ?_⟩
    have hcoef : 1 + A / Real.log (n : ℝ) ≤ 2 := by linarith
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    have heReal : (e : ℝ) ≤ 2 * (v : ℝ) :=
      he.2.trans (mul_le_mul_of_nonneg_right hcoef hv0)
    exact_mod_cast heReal
  calc
    (appendixA9CyclicEdges A n v).card ≤
        (Finset.Icc v (2 * v)).card := Finset.card_le_card hsubset
    _ ≤ 2 * v := by simp; omega

/-- Sum over the forest edge counts at a fixed `v`; this is the individual
outer summand in (A.11). -/
theorem sum_appendixA9ForestEdges_le
    (A : ℝ) {n v : ℕ} {a b : ℝ}
    (hv : 1 ≤ v) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (∑ e ∈ appendixA9ForestEdges A n v,
      appendixA9Term a b v e) ≤
      a * appendixWeightedGeometricTerm
        (2 * appendixCountingConstant * Real.sqrt b) v := by
  let q := 2 * appendixCountingConstant * Real.sqrt b
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (mul_nonneg (by norm_num) appendixCountingConstant_pos.le)
      (Real.sqrt_nonneg b)
  have hterm (e : ℕ) (heMem : e ∈ appendixA9ForestEdges A n v) :
      appendixA9Term a b v e ≤ a * q ^ v := by
    rw [appendixA9ForestEdges, Finset.mem_filter,
      Finset.mem_Icc] at heMem
    have heUpper : e ≤ v - 1 := (Nat.le_min.mp heMem.1.2).2
    have he : e < v := by omega
    have hlower : v ≤ 2 * e := by
      have := heMem.1.1
      omega
    exact appendixA9Term_forest_le ha0 ha1 hb0 hb1 hv hlower he
  have hcard : ((appendixA9ForestEdges A n v).card : ℝ) ≤ 2 * (v : ℝ) := by
    have hnat := card_appendixA9ForestEdges_le A n v hv
    exact_mod_cast (hnat.trans (by omega : v ≤ 2 * v))
  calc
    (∑ e ∈ appendixA9ForestEdges A n v,
        appendixA9Term a b v e) ≤
        ∑ _e ∈ appendixA9ForestEdges A n v, a * q ^ v :=
      Finset.sum_le_sum hterm
    _ = ((appendixA9ForestEdges A n v).card : ℝ) * (a * q ^ v) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (v : ℝ)) * (a * q ^ v) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg ha0 (pow_nonneg hq0 v))
    _ = a * appendixWeightedGeometricTerm q v := by
      unfold appendixWeightedGeometricTerm
      ring

/-- Sum over the cyclic/excess edge counts at a fixed `v`; this is the
individual outer summand in (A.12). -/
theorem sum_appendixA9CyclicEdges_le
    (A b : ℝ) {n m v : ℕ}
    (hn : 1 < n) (hm : 1 ≤ m) (hv : 1 ≤ v) (hvn : v ≤ n)
    (hdelta : A / Real.log (n : ℝ) ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (∑ e ∈ appendixA9CyclicEdges A n v,
      appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ)) b v e) ≤
      appendixWeightedGeometricTerm
        (2 * appendixCountingConstant * appendixExcessConstant A * b) v := by
  let q := 2 * appendixCountingConstant * appendixExcessConstant A * b
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) appendixCountingConstant_pos.le)
        (appendixExcessConstant_pos A).le)
      hb0
  have hterm (e : ℕ) (heMem : e ∈ appendixA9CyclicEdges A n v) :
      appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ)) b v e ≤ q ^ v := by
    rw [appendixA9CyclicEdges, Finset.mem_filter,
      Finset.mem_Icc] at heMem
    have hcoef : 1 + A / Real.log (n : ℝ) ≤ 2 := by linarith
    have heReal : (e : ℝ) ≤ 2 * (v : ℝ) :=
      heMem.2.trans
        (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg v))
    have heUpper : e ≤ 2 * v := by exact_mod_cast heReal
    exact appendixA9Term_cyclic_le A b hn hm hv hvn
      heMem.1.1 heUpper heMem.2 hb0 hb1
  have hcard : ((appendixA9CyclicEdges A n v).card : ℝ) ≤ 2 * (v : ℝ) := by
    exact_mod_cast card_appendixA9CyclicEdges_le hv hdelta
  calc
    (∑ e ∈ appendixA9CyclicEdges A n v,
        appendixA9Term ((m : ℝ) ^ 2 / (n : ℝ)) b v e) ≤
        ∑ _e ∈ appendixA9CyclicEdges A n v, q ^ v :=
      Finset.sum_le_sum hterm
    _ = ((appendixA9CyclicEdges A n v).card : ℝ) * q ^ v := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (v : ℝ)) * q ^ v :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hq0 v)
    _ = appendixWeightedGeometricTerm q v := by
      rfl

/-- Equations (A.10)--(A.12), finite form: once `c` is above the explicit
threshold, the full graph-counted A.9 sum is dominated eventually by the
paper's two weighted geometric sums. -/
theorem eventually_appendixA9Enumeration_le_tailEnvelope
    (A c lam r : ℝ) (hA : 0 ≤ A)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hc : appendixLargeCThreshold lam appendixCountingConstant
      (appendixExcessConstant A) ≤ c) :
    ∀ᶠ n : ℕ in atTop,
      appendixA9Enumeration A c lam r n ≤
        appendixEnumerationTailEnvelope
          (appendixLowDegreeSmallParameter r)
          appendixCycleCutoff
          (fun n ↦ 2 * appendixDegreeCutoff n + 1)
          (appendixForestGeometricRatio lam appendixCountingConstant c)
          (appendixCyclicGeometricRatio lam appendixCountingConstant
            (appendixExcessConstant A) c) n := by
  obtain ⟨hb0, hb1, _hqF0, _hqF1, _hqC0, _hqC1⟩ :=
    appendix_largeC_geometric_ratios lam appendixCountingConstant
      (appendixExcessConstant A) appendixCountingConstant_pos
      (appendixExcessConstant_pos A) hc
  have hD := eventually_two_appendixDegreeCutoff_le_index hr
  have hm := (appendixPlantSize_tendsto_atTop hr.1).eventually_ge_atTop 1
  have ha := appendixPlantSize_sq_div_index_vanishes hr.2
  have ha1 : ∀ᶠ n : ℕ in atTop,
      appendixLowDegreeSmallParameter r n ≤ 1 := by
    filter_upwards [(tendsto_order.1 ha).2 1 zero_lt_one] with n hn
    simpa only [appendixLowDegreeSmallParameter] using hn.le
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogA := hlog.eventually_ge_atTop A
  filter_upwards [hD, hm, ha1, hlogA,
      Filter.eventually_gt_atTop (1 : ℕ)] with n hDn hmn han hlogAn hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hdelta : A / Real.log (n : ℝ) ≤ 1 :=
    (div_le_one hlogpos).2 hlogAn
  have ha0 : 0 ≤ appendixLowDegreeSmallParameter r n := by
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  let cap := 2 * appendixDegreeCutoff n + 1
  let qF := appendixForestGeometricRatio lam appendixCountingConstant c
  let qC := appendixCyclicGeometricRatio lam appendixCountingConstant
    (appendixExcessConstant A) c
  have hforest :
      (∑ v ∈ Finset.Ico 2 cap,
          ∑ e ∈ appendixA9ForestEdges A n v,
            appendixA9Term (appendixLowDegreeSmallParameter r n)
              (lam ^ 2 / c) v e) ≤
        appendixLowDegreeSmallParameter r n *
          finiteAppendixWeightedGeometricSum qF 2 cap := by
    unfold finiteAppendixWeightedGeometricSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hvMem
    have hv : 1 ≤ v := by
      have := (Finset.mem_Ico.mp hvMem).1
      omega
    simpa only [qF, appendixForestGeometricRatio] using
      sum_appendixA9ForestEdges_le A hv ha0 han hb0 hb1
  have hcyclic :
      (∑ v ∈ Finset.Ico (appendixCycleCutoff n + 1) cap,
          ∑ e ∈ appendixA9CyclicEdges A n v,
            appendixA9Term (appendixLowDegreeSmallParameter r n)
              (lam ^ 2 / c) v e) ≤
        finiteAppendixWeightedGeometricSum qC
          (appendixCycleCutoff n + 1) cap := by
    unfold finiteAppendixWeightedGeometricSum
    apply Finset.sum_le_sum
    intro v hvMem
    have hvLower := (Finset.mem_Ico.mp hvMem).1
    have hvUpper := (Finset.mem_Ico.mp hvMem).2
    have hv : 1 ≤ v := by
      have hg : 3 ≤ appendixCycleCutoff n := by
        unfold appendixCycleCutoff
        exact le_max_left _ _
      omega
    have hvD : v ≤ 2 * appendixDegreeCutoff n := by
      dsimp [cap] at hvUpper
      omega
    have hvn : v ≤ n := hvD.trans hDn
    simpa only [qC, appendixCyclicGeometricRatio,
      appendixLowDegreeSmallParameter] using
      sum_appendixA9CyclicEdges_le A (lam ^ 2 / c)
        hn hmn hv hvn hdelta hb0 hb1
  unfold appendixA9Enumeration appendixEnumerationTailEnvelope
  dsimp only [cap, qF, qC]
  exact add_le_add hforest hcyclic

/-- The canonical projected norm is always at least its constant-character
contribution. -/
theorem one_le_appendixLowDegreeNormSq
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) :
    1 ≤ appendixLowDegreeNormSq c lam r gamma hr n := by
  exact one_le_randomForcedLowDegreeNormSq _ _ _

/-! ## The A.9--A.12 analytic endgame -/

/-- The nonconstant Fourier mass whose vanishing is the low-degree
indistinguishability conclusion. -/
noncomputable def appendixLowDegreeExcess
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) (n : ℕ) : ℝ :=
  appendixLowDegreeNormSq c lam r gamma hr n - 1

/-- The canonical girth cutoff tends to infinity.  This is the limit used in
the last step of (A.12). -/
theorem appendixCycleCutoff_tendsto_atTop :
    Tendsto appendixCycleCutoff atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hfloor : Tendsto
      (fun n : ℕ ↦ ⌊Real.log (Real.log (n : ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hloglog
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun n ↦ le_max_right 3
      ⌊Real.log (Real.log (n : ℝ))⌋₊)
    hfloor

/-- A precise interface for the enumeration in (A.9)--(A.12).

The first weighted geometric sum is exactly the right side of (A.11), with
prefactor `a_n` and ratio `2K√b`; the second starts strictly above `g_n` and
is exactly (A.12), with ratio `2 K C_A b`. -/
def AppendixEnumerationEnvelope
    (K C_A c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    appendixLowDegreeExcess c lam r gamma hr n ≤
      appendixEnumerationTailEnvelope
        (appendixLowDegreeSmallParameter r)
        appendixCycleCutoff
        (fun n ↦ 2 * appendixDegreeCutoff n + 1)
        (appendixForestGeometricRatio lam K c)
        (appendixCyclicGeometricRatio lam K C_A c) n

/-- The remaining finite graph/probability statement (A.9): the actual
nonconstant Fourier mass is eventually bounded by the explicit graph-counted
sum.  Equations (A.10)--(A.12) below discharge everything after this
interface. -/
def AppendixA9Bound
    (A c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    appendixLowDegreeExcess c lam r gamma hr n ≤
      appendixA9Enumeration A c lam r n

/-- Sufficient quantitative form of Appendix (A.6).  The numerator
`m_n^v` is slightly weaker than the exact falling-factorial numerator but
already gives the displayed A.9 summand. -/
def AppendixA6PowBound
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ S : Finset (AmbientEdge n),
    randomPlantContainmentProbability
        (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S ≤
      ((appendixPlantSize r n : ℝ) ^ ambientSupportVertexCount S /
        fallingFactorial n (ambientSupportVertexCount S)) *
        (lam / (appendixPlantSize r n : ℝ)) ^ S.card

/-- Equation (A.6) for the actual twice-truncated, uniformly injected
appendix plant. -/
theorem appendixA6PowBound_actual
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hlam : 0 < lam) :
    AppendixA6PowBound lam r gamma hr := by
  have hpSource : ∀ᶠ n : ℕ in atTop,
      (sparseBernoulliParameter lam (appendixPlantSize r n)).p =
        lam / (appendixPlantSize r n : ℝ) :=
    (appendixPlantSize_tendsto_atTop hr.1).eventually
      (eventually_sparseBernoulliParameter_p_eq hlam)
  filter_upwards [hpSource] with n hp
  intro S
  let hfit : appendixPlantSize r n ≤ n :=
    appendixPlantSize_le_index hr.1 (by linarith [hr.2]) n
  let theta := sparseBernoulliParameter lam (appendixPlantSize r n)
  calc
    randomPlantContainmentProbability
          (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S ≤
        randomPlantContainmentProbability
          (uniformlyInjectedPlantLaw hfit
            ((erdosRenyiLaw (n := appendixPlantSize r n) theta).map
              presentAmbientEdges)) S := by
      simpa only [appendixInjectedTruncatedPlantLaw, hfit, theta] using
        uniformlyInjected_twiceTruncated_containment_le_original
          lam r gamma (appendixPlantSize r) appendixCycleCutoff n n hfit S
    _ = theta.p ^ S.card *
          (uniformPermutationLaw n).prob
            (ambientSupportFitEvent hfit S) :=
      uniformlyInjected_erdosRenyi_containment_eq_pow_mul_fitProbability
        hfit theta S
    _ ≤ theta.p ^ S.card *
          ((appendixPlantSize r n : ℝ) ^ ambientSupportVertexCount S /
            fallingFactorial n (ambientSupportVertexCount S)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [ambientSupportVertexCount] using
          uniformPermutationLaw_prob_ambientSupportFitEvent_le_pow_div
            hfit S
      · exact pow_nonneg theta.p_pos.le _
    _ = ((appendixPlantSize r n : ℝ) ^ ambientSupportVertexCount S /
          fallingFactorial n (ambientSupportVertexCount S)) *
          (lam / (appendixPlantSize r n : ℝ)) ^ S.card := by
      rw [show theta.p = lam / (appendixPlantSize r n : ℝ) by
        exact hp]
      ring

/-- A.6 together with the actual support restrictions A.7--A.8 proves the
finite graph/probability bound A.9. -/
theorem appendixA9Bound_of_A6PowBound
    (c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hc : 0 < c) (hlam : 0 < lam)
    (hA6 : AppendixA6PowBound lam r gamma hr) :
    AppendixA9Bound (localSparsitySlackConstant lam r gamma)
      c lam r gamma hr := by
  have hm := (appendixPlantSize_tendsto_atTop hr.1).eventually_ge_atTop 1
  filter_upwards [hA6,
      eventually_active_appendixLowDegreeCountFiber_restrictions
        lam r gamma hr hgamma,
      eventually_four_appendixDegreeCutoff_le_index hr,
      eventually_sparseBernoulliParameter_p_eq hc,
      hm,
      Filter.eventually_gt_atTop (0 : ℕ)] with
      n hcontainment hrestr hfourD hp hm1 hn
  unfold appendixLowDegreeExcess
  rw [appendixLowDegreeExcess_eq_sum_countFiberMass]
  calc
    (∑ v ∈ Finset.range (2 * appendixDegreeCutoff n + 1),
        ∑ e ∈ Finset.range (appendixDegreeCutoff n + 1),
          appendixLowDegreeCountFiberMass c lam r gamma hr n v e) ≤
      ∑ v ∈ Finset.range (2 * appendixDegreeCutoff n + 1),
        ∑ e ∈ Finset.range (appendixDegreeCutoff n + 1),
          appendixA9IndexedTerm
            (localSparsitySlackConstant lam r gamma)
            c lam r n v e := by
      apply Finset.sum_le_sum
      intro v hvRange
      apply Finset.sum_le_sum
      intro e _heRange
      by_cases hactive : AppendixLowDegreeCountFiberActive
          lam r gamma hr n v e
      · rcases hrestr v e hactive with
          ⟨hv2, hve2, heD, hdensity, hcycle⟩
        have hvD : v ≤ 2 * appendixDegreeCutoff n := by
          have := Finset.mem_range.mp hvRange
          omega
        have h2vn : 2 * v ≤ n := by omega
        have hmpos : 0 < appendixPlantSize r n := by omega
        have hfiberContainment : ∀ S ∈
            appendixLowDegreeCountFiber n v e,
            randomPlantContainmentProbability
                (appendixInjectedTruncatedPlantLaw lam r gamma hr n) S ≤
              ((appendixPlantSize r n : ℝ) ^ v /
                fallingFactorial n v) *
                (lam / (appendixPlantSize r n : ℝ)) ^ e := by
          intro S hS
          have hstats := hS
          rw [appendixLowDegreeCountFiber, Finset.mem_filter] at hstats
          simpa only [hstats.2.1, hstats.2.2] using hcontainment S
        calc
          appendixLowDegreeCountFiberMass c lam r gamma hr n v e ≤
              appendixA9Term
                ((appendixPlantSize r n : ℝ) ^ 2 / (n : ℝ))
                (lam ^ 2 / c) v e :=
            appendixLowDegreeCountFiberMass_le_A9Term_of_containment
              c lam r gamma hr hn hmpos hc hlam.le hp h2vn
              hfiberContainment
          _ = appendixA9IndexedTerm
                (localSparsitySlackConstant lam r gamma)
                c lam r n v e :=
            (appendixA9IndexedTerm_eq_term_of_restrictions
              (localSparsitySlackConstant lam r gamma) c lam r
              hv2 hve2 heD hdensity hcycle).symm
      · rw [appendixLowDegreeCountFiberMass_eq_zero_of_not_active
            c lam r gamma hr hactive]
        exact appendixA9IndexedTerm_nonneg
          (localSparsitySlackConstant lam r gamma) c lam r n v e hc
    _ = appendixA9Enumeration
          (localSparsitySlackConstant lam r gamma) c lam r n :=
      sum_appendixA9IndexedTerm_eq_enumeration
        (localSparsitySlackConstant lam r gamma) c lam r n

/-- A.9 implies the A.11--A.12 envelope with the explicit constants furnished
by the counting and excess lemmas. -/
theorem appendixEnumerationEnvelope_of_A9
    (A c lam r gamma : ℝ) (hA : 0 ≤ A)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hc : appendixLargeCThreshold lam appendixCountingConstant
      (appendixExcessConstant A) ≤ c)
    (hA9 : AppendixA9Bound A c lam r gamma hr) :
    AppendixEnumerationEnvelope appendixCountingConstant
      (appendixExcessConstant A) c lam r gamma hr := by
  filter_upwards [hA9,
      eventually_appendixA9Enumeration_le_tailEnvelope A c lam r hA hr hc]
    with n hactual henum
  exact hactual.trans henum

/-- Equations (A.11)--(A.12): the enumeration envelope vanishes at the
canonical scales. -/
theorem appendixEnumerationEnvelope_vanishes
    (lam K C_A c r : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hK : 0 < K) (hC_A : 0 < C_A)
    (hc : appendixLargeCThreshold lam K C_A ≤ c) :
    Vanishes (appendixEnumerationTailEnvelope
      (appendixLowDegreeSmallParameter r)
      appendixCycleCutoff
      (fun n ↦ 2 * appendixDegreeCutoff n + 1)
      (appendixForestGeometricRatio lam K c)
      (appendixCyclicGeometricRatio lam K C_A c)) := by
  obtain ⟨_hb0, _hb1, hForest0, hForest1,
      hCyclic0, hCyclic1⟩ :=
    appendix_largeC_geometric_ratios lam K C_A hK hC_A hc
  apply appendixEnumerationTailEnvelope_vanishes
  · exact hForest0
  · exact hForest1
  · exact hCyclic0
  · exact hCyclic1
  · intro n
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · exact appendixPlantSize_sq_div_index_vanishes hr.2
  · exact appendixCycleCutoff_tendsto_atTop

/-- The exact analytic implication from (A.9) to the low-degree conclusion
for the actual appendix alternative. -/
theorem appendixLowDegreeNormSq_tendsToOne_of_envelope
    (K C_A c lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hK : 0 < K) (hC_A : 0 < C_A)
    (hc : appendixLargeCThreshold lam K C_A ≤ c)
    (henvelope : AppendixEnumerationEnvelope
      K C_A c lam r gamma hr) :
    TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) := by
  rw [tendsToOne_iff_vanishes_sub]
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      exact sub_nonneg.mpr
        (one_le_appendixLowDegreeNormSq c lam r gamma hr n))
    henvelope
    (appendixEnumerationEnvelope_vanishes
      lam K C_A c r hr hK hC_A hc)

/-- Quantifier-exact form of the low-degree half of Theorem A.1 once the
finite A.9 envelope has been established uniformly above a constant `c₀`.
In particular, `c` is fixed outside the limit in `n`. -/
theorem appendix_lowDegreeIndistinguishability_of_envelopes
    (lam r gamma K C_A : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hK : 0 < K) (hC_A : 0 < C_A)
    (henvelopes : ∀ c : ℝ,
      appendixLargeCThreshold lam K C_A ≤ c →
      AppendixEnumerationEnvelope K C_A c lam r gamma hr) :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) := by
  refine ⟨appendixLargeCThreshold lam K C_A,
    one_lt_appendixLargeCThreshold lam K C_A, ?_⟩
  intro c hc
  exact appendixLowDegreeNormSq_tendsToOne_of_envelope
    K C_A c lam r gamma hr hK hC_A hc (henvelopes c hc)

/-- Low-degree half of Theorem A.1 reduced exactly to the finite A.9
graph/probability bound, with the paper's explicit `c₀` quantifier order. -/
theorem appendix_lowDegreeIndistinguishability_of_A9
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hA9 : ∀ c : ℝ,
      appendixLargeCThreshold lam appendixCountingConstant
          (appendixExcessConstant
            (localSparsitySlackConstant lam r gamma)) ≤ c →
      AppendixA9Bound (localSparsitySlackConstant lam r gamma)
        c lam r gamma hr) :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) := by
  let A := localSparsitySlackConstant lam r gamma
  have hApos : 0 < A :=
    localSparsitySlackConstant_pos lam hr.1 hgamma.2
  apply appendix_lowDegreeIndistinguishability_of_envelopes
    lam r gamma appendixCountingConstant (appendixExcessConstant A)
    hr appendixCountingConstant_pos (appendixExcessConstant_pos A)
  intro c hc
  exact appendixEnumerationEnvelope_of_A9 A c lam r gamma hApos.le hr hc
    (hA9 c hc)

/-- Low-degree half of Appendix Theorem A.1 from the quantitative A.6
bound; A.7--A.12 are discharged internally. -/
theorem appendix_lowDegreeIndistinguishability_of_A6PowBound
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam)
    (hA6 : AppendixA6PowBound lam r gamma hr) :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) := by
  apply appendix_lowDegreeIndistinguishability_of_A9
    lam r gamma hr hgamma
  intro c hc
  have hcpos : 0 < c := by
    have hthreshold : 1 < appendixLargeCThreshold lam
        appendixCountingConstant
        (appendixExcessConstant
          (localSparsitySlackConstant lam r gamma)) :=
      one_lt_appendixLargeCThreshold _ _ _
    linarith
  exact appendixA9Bound_of_A6PowBound
    c lam r gamma hr hgamma hcpos hlam hA6

/-- **Low-degree consequence in Appendix Theorem A.1, for the actual
twice-truncated uniformly injected alternative.**  For every fixed
`lam > 0`, `0 < r < 1/2`, and `0 < gamma < 1`, there is a constant
`c₀ > 1` such that every fixed `c ≥ c₀` has projected likelihood-ratio
norm tending to one at the canonical degree cutoff. -/
theorem appendix_lowDegreeIndistinguishability
    (lam r gamma : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      TendsToOne (appendixLowDegreeNormSq c lam r gamma hr) := by
  exact appendix_lowDegreeIndistinguishability_of_A6PowBound
    lam r gamma hr hgamma hlam
      (appendixA6PowBound_actual lam r gamma hr hlam)

end

end LowDegree
