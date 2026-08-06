import LowDegree.Asymptotics.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Enumeration tails for the supercritical appendix

This module isolates the pure finite-sum and limit estimates behind the
enumeration in Appendix equations A.10--A.12.  The concrete graph layer may
use any finite dependent inner index family.  Once its summands are bounded
by two geometric weights, the whole enumeration is controlled uniformly in
the finite cutoffs.
-/

namespace LowDegree

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite dependent double geometric sum.  The outer index lies in
`[start, stop)`, while the finite inner index set may depend arbitrarily on
the outer index. -/
noncomputable def finiteDependentDoubleGeometricSum
    (outerBase innerBase : ℝ) (start stop : ℕ)
    (inner : ℕ → Finset ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico start stop,
    ∑ j ∈ inner i, outerBase ^ i * innerBase ^ j

/-- Splitting the outer interval splits the dependent double sum exactly. -/
theorem finiteDependentDoubleGeometricSum_split
    (outerBase innerBase : ℝ) {start cut stop : ℕ}
    (inner : ℕ → Finset ℕ)
    (hstart : start ≤ cut) (hstop : cut ≤ stop) :
    finiteDependentDoubleGeometricSum outerBase innerBase start stop inner =
      finiteDependentDoubleGeometricSum outerBase innerBase start cut inner +
        finiteDependentDoubleGeometricSum outerBase innerBase cut stop inner := by
  unfold finiteDependentDoubleGeometricSum
  exact (Finset.sum_Ico_consecutive
    (fun i ↦ ∑ j ∈ inner i, outerBase ^ i * innerBase ^ j)
    hstart hstop).symm

/-- Any finite sub-sum of a nonnegative geometric series is bounded by its
complete sum. -/
theorem finiteGeometricSum_le_inv_one_sub
    {base : ℝ} (hbase0 : 0 ≤ base) (hbase1 : base < 1)
    (indices : Finset ℕ) :
    (∑ i ∈ indices, base ^ i) ≤ (1 - base)⁻¹ := by
  calc
    (∑ i ∈ indices, base ^ i) ≤ ∑' i : ℕ, base ^ i :=
      (summable_geometric_of_lt_one hbase0 hbase1).sum_le_tsum indices
        (fun i _hi ↦ pow_nonneg hbase0 i)
    _ = (1 - base)⁻¹ := tsum_geometric_of_lt_one hbase0 hbase1

/-- A finite geometric interval beginning at `start` is bounded by the
corresponding infinite tail. -/
theorem finiteGeometricIco_le_tail
    {base : ℝ} (hbase0 : 0 ≤ base) (hbase1 : base < 1)
    (start stop : ℕ) :
    (∑ i ∈ Finset.Ico start stop, base ^ i) ≤
      base ^ start / (1 - base) := by
  by_cases hle : start ≤ stop
  · rw [geom_sum_Ico' (ne_of_lt hbase1) hle]
    have hden : 0 < 1 - base := sub_pos.mpr hbase1
    rw [div_le_div_iff_of_pos_right hden]
    exact sub_le_self _ (pow_nonneg hbase0 stop)
  · have hempty : Finset.Ico start stop = ∅ :=
      Finset.Ico_eq_empty (Nat.not_lt.mpr (Nat.le_of_not_ge hle))
    rw [hempty]
    simp only [Finset.sum_empty]
    exact div_nonneg (pow_nonneg hbase0 start) (sub_nonneg.mpr hbase1.le)

/-- Uniform product-tail bound for a finite dependent double sum.  No
cardinality bound on the inner family is needed: it is a finite subset of
the complete inner geometric series. -/
theorem finiteDependentDoubleGeometricSum_le
    {outerBase innerBase : ℝ}
    (hOuter0 : 0 ≤ outerBase) (hOuter1 : outerBase < 1)
    (hInner0 : 0 ≤ innerBase) (hInner1 : innerBase < 1)
    (start stop : ℕ) (inner : ℕ → Finset ℕ) :
    finiteDependentDoubleGeometricSum outerBase innerBase start stop inner ≤
      outerBase ^ start / ((1 - outerBase) * (1 - innerBase)) := by
  have hInnerInv : 0 ≤ (1 - innerBase)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hInner1.le)
  unfold finiteDependentDoubleGeometricSum
  calc
    (∑ i ∈ Finset.Ico start stop,
        ∑ j ∈ inner i, outerBase ^ i * innerBase ^ j) =
      ∑ i ∈ Finset.Ico start stop,
        outerBase ^ i * ∑ j ∈ inner i, innerBase ^ j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.Ico start stop,
        outerBase ^ i * (1 - innerBase)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (finiteGeometricSum_le_inv_one_sub hInner0 hInner1 (inner i))
        (pow_nonneg hOuter0 i)
    _ = (∑ i ∈ Finset.Ico start stop, outerBase ^ i) *
        (1 - innerBase)⁻¹ := by
      rw [Finset.sum_mul]
    _ ≤ (outerBase ^ start / (1 - outerBase)) *
        (1 - innerBase)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (finiteGeometricIco_le_tail hOuter0 hOuter1 start stop) hInnerInv
    _ = outerBase ^ start /
        ((1 - outerBase) * (1 - innerBase)) := by
      field_simp [ne_of_gt (sub_pos.mpr hOuter1),
        ne_of_gt (sub_pos.mpr hInner1)]

/-! ## The weighted geometric series in A.11--A.12 -/

/-- The common majorant in A.11--A.12.  In the forest part one takes
`q = 2 K √b`; in the cyclic/excess part one takes `q = 2 K C_A b`. -/
def appendixWeightedGeometricTerm (q : ℝ) (v : ℕ) : ℝ :=
  2 * (v : ℝ) * q ^ v

/-- The finite half-open interval sum of the A.11--A.12 weights. -/
noncomputable def finiteAppendixWeightedGeometricSum
    (q : ℝ) (start stop : ℕ) : ℝ :=
  ∑ v ∈ Finset.Ico start stop, appendixWeightedGeometricTerm q v

/-- The infinite weighted tail beginning strictly after `g`. -/
noncomputable def appendixWeightedGeometricTail (q : ℝ) (g : ℕ) : ℝ :=
  ∑' k : ℕ, appendixWeightedGeometricTerm q (k + g + 1)

theorem appendixWeightedGeometricTerm_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (v : ℕ) :
    0 ≤ appendixWeightedGeometricTerm q v := by
  unfold appendixWeightedGeometricTerm
  positivity

/-- The series `∑_v 2 v q^v` is summable for `0 ≤ q < 1`. -/
theorem summable_appendixWeightedGeometricTerm
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (appendixWeightedGeometricTerm q) := by
  have hn := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := q) (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  have hbase : Summable (fun v : ℕ ↦ (v : ℝ) * q ^ v) := by
    apply hn.congr
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simp only [pow_one]
    · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg v) 1)
        (pow_nonneg hq0 v)
  change Summable (fun v : ℕ ↦ 2 * (v : ℝ) * q ^ v)
  simpa only [mul_assoc] using hbase.mul_left 2

/-- Every finite interval of weighted terms is bounded by the complete
weighted geometric series, uniformly in its endpoints. -/
theorem finiteAppendixWeightedGeometricSum_le_tsum
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (start stop : ℕ) :
    finiteAppendixWeightedGeometricSum q start stop ≤
      ∑' v : ℕ, appendixWeightedGeometricTerm q v := by
  unfold finiteAppendixWeightedGeometricSum
  exact (summable_appendixWeightedGeometricTerm hq0 hq1).sum_le_tsum
    (Finset.Ico start stop)
    (fun v _hv ↦ appendixWeightedGeometricTerm_nonneg hq0 v)

/-- The finite sum over `g < v < stop` is bounded by the corresponding
infinite weighted tail. -/
theorem finiteAppendixWeightedGeometricSum_succ_le_tail
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (g stop : ℕ) :
    finiteAppendixWeightedGeometricSum q (g + 1) stop ≤
      appendixWeightedGeometricTail q g := by
  have hsum := summable_appendixWeightedGeometricTerm hq0 hq1
  have hshift : Summable
      (fun k : ℕ ↦ appendixWeightedGeometricTerm q (k + (g + 1))) :=
    (summable_nat_add_iff (g + 1)).2 hsum
  unfold finiteAppendixWeightedGeometricSum appendixWeightedGeometricTail
  rw [Finset.sum_Ico_eq_sum_range]
  have hfinite := hshift.sum_le_tsum (Finset.range (stop - (g + 1)))
    (fun k _hk ↦ appendixWeightedGeometricTerm_nonneg hq0 (k + (g + 1)))
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinite

/-- The infinite weighted tail tends to zero as its strict lower cutoff
tends to infinity. -/
theorem appendixWeightedGeometricTail_vanishes
    {q : ℝ} (_hq0 : 0 ≤ q) (_hq1 : q < 1) :
    Vanishes (appendixWeightedGeometricTail q) := by
  unfold appendixWeightedGeometricTail
  simpa only [Nat.add_assoc] using
    (tendsto_sum_nat_add (fun v : ℕ ↦
      appendixWeightedGeometricTerm q (v + 1)))

/-! ## A paper-facing A.11--A.12 envelope -/

/-- The exact analytic envelope used after the graph enumeration.

The first finite sum is the A.11 forest contribution, with its vanishing
prefactor `aₙ`.  The second is the A.12 cyclic/excess contribution over
`v > gₙ`.  The upper cutoff `cap n` is exclusive and may be arbitrary. -/
noncomputable def appendixEnumerationTailEnvelope
    (a : ℕ → ℝ) (g cap : ℕ → ℕ)
    (qForest qCyclic : ℝ) (n : ℕ) : ℝ :=
  a n * finiteAppendixWeightedGeometricSum qForest 2 (cap n) +
    finiteAppendixWeightedGeometricSum qCyclic (g n + 1) (cap n)

/-- Uniform finite A.11--A.12 bound.  It is independent of the finite
upper cutoff. -/
theorem appendixEnumerationTailEnvelope_le
    {a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {qForest qCyclic : ℝ}
    (hForest0 : 0 ≤ qForest) (hForest1 : qForest < 1)
    (hCyclic0 : 0 ≤ qCyclic) (hCyclic1 : qCyclic < 1)
    {n : ℕ} (ha0 : 0 ≤ a n) :
    appendixEnumerationTailEnvelope a g cap qForest qCyclic n ≤
      a n * (∑' v : ℕ, appendixWeightedGeometricTerm qForest v) +
        appendixWeightedGeometricTail qCyclic (g n) := by
  unfold appendixEnumerationTailEnvelope
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (finiteAppendixWeightedGeometricSum_le_tsum
        hForest0 hForest1 2 (cap n)) ha0)
    (finiteAppendixWeightedGeometricSum_succ_le_tail
      hCyclic0 hCyclic1 (g n) (cap n))

/-- Once `aₙ → 0`, `gₙ → ∞`, and both geometric bases are below
one, the complete finite enumeration envelope vanishes. -/
theorem appendixEnumerationTailEnvelope_vanishes
    {a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {qForest qCyclic : ℝ}
    (hForest0 : 0 ≤ qForest) (hForest1 : qForest < 1)
    (hCyclic0 : 0 ≤ qCyclic) (hCyclic1 : qCyclic < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Vanishes a)
    (hg : Tendsto g atTop atTop) :
    Vanishes (appendixEnumerationTailEnvelope
      a g cap qForest qCyclic) := by
  have hhead : Vanishes (fun n ↦
      a n * (∑' v : ℕ, appendixWeightedGeometricTerm qForest v)) := by
    simpa only [mul_comm] using
      ha.const_mul (∑' v : ℕ, appendixWeightedGeometricTerm qForest v)
  have htail : Vanishes (fun n ↦
      appendixWeightedGeometricTail qCyclic (g n)) :=
    (appendixWeightedGeometricTail_vanishes hCyclic0 hCyclic1).comp hg
  have hmajor : Vanishes (fun n ↦
      a n * (∑' v : ℕ, appendixWeightedGeometricTerm qForest v) +
        appendixWeightedGeometricTail qCyclic (g n)) := hhead.add htail
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      unfold appendixEnumerationTailEnvelope
      exact add_nonneg
        (mul_nonneg (ha0 n) (Finset.sum_nonneg fun v _hv ↦
          appendixWeightedGeometricTerm_nonneg hForest0 v))
        (Finset.sum_nonneg fun v _hv ↦
          appendixWeightedGeometricTerm_nonneg hCyclic0 v)
  · exact Eventually.of_forall fun n ↦
      appendixEnumerationTailEnvelope_le hForest0 hForest1
        hCyclic0 hCyclic1 (ha0 n)
  · exact hmajor

/-- Reusable conclusion for the appendix: any nonnegative enumerated excess
dominated by the A.11--A.12 weighted envelope vanishes. -/
theorem appendixEnumeratedExcess_vanishes_of_le
    {excess a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {qForest qCyclic : ℝ}
    (hForest0 : 0 ≤ qForest) (hForest1 : qForest < 1)
    (hCyclic0 : 0 ≤ qCyclic) (hCyclic1 : qCyclic < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Vanishes a)
    (hg : Tendsto g atTop atTop)
    (hexcess0 : ∀ᶠ n in atTop, 0 ≤ excess n)
    (hbound : ∀ᶠ n in atTop,
      excess n ≤ appendixEnumerationTailEnvelope
        a g cap qForest qCyclic n) :
    Vanishes excess := by
  exact squeeze_zero' hexcess0 hbound
    (appendixEnumerationTailEnvelope_vanishes
      hForest0 hForest1 hCyclic0 hCyclic1 ha0 ha hg)

/-- Abstract envelope for the two pieces in A.11--A.12.

The first term carries a small prefactor `aₙ` and allows every outer
index below the finite cutoff.  The second term is the cyclic/excess tail,
whose outer index starts at `gₙ`. -/
noncomputable def enumeratedExcessEnvelope
    (a : ℕ → ℝ) (g cap : ℕ → ℕ)
    (inner : ℕ → ℕ → Finset ℕ)
    (outerBase innerBase : ℝ) (n : ℕ) : ℝ :=
  a n * finiteDependentDoubleGeometricSum
      outerBase innerBase 0 (cap n) (inner n) +
    finiteDependentDoubleGeometricSum
      outerBase innerBase (g n) (cap n) (inner n)

/-- Finite A.11--A.12 envelope bound, uniform in both finite enumeration
cutoffs and in the dependent inner index sets. -/
theorem enumeratedExcessEnvelope_le
    {a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {inner : ℕ → ℕ → Finset ℕ}
    {outerBase innerBase : ℝ}
    (hOuter0 : 0 ≤ outerBase) (hOuter1 : outerBase < 1)
    (hInner0 : 0 ≤ innerBase) (hInner1 : innerBase < 1)
    {n : ℕ} (ha0 : 0 ≤ a n) :
    enumeratedExcessEnvelope a g cap inner outerBase innerBase n ≤
      (a n + outerBase ^ (g n)) /
        ((1 - outerBase) * (1 - innerBase)) := by
  let denom := (1 - outerBase) * (1 - innerBase)
  have hdenom : 0 < denom :=
    mul_pos (sub_pos.mpr hOuter1) (sub_pos.mpr hInner1)
  have hhead := finiteDependentDoubleGeometricSum_le
    hOuter0 hOuter1 hInner0 hInner1 0 (cap n) (inner n)
  have htail := finiteDependentDoubleGeometricSum_le
    hOuter0 hOuter1 hInner0 hInner1 (g n) (cap n) (inner n)
  unfold enumeratedExcessEnvelope
  calc
    a n * finiteDependentDoubleGeometricSum
          outerBase innerBase 0 (cap n) (inner n) +
        finiteDependentDoubleGeometricSum
          outerBase innerBase (g n) (cap n) (inner n) ≤
      a n * (outerBase ^ 0 / denom) + outerBase ^ (g n) / denom :=
        add_le_add (mul_le_mul_of_nonneg_left hhead ha0) htail
    _ = (a n + outerBase ^ (g n)) / denom := by
      simp only [pow_zero, one_div]
      field_simp [hdenom.ne']

/-- The abstract A.11--A.12 enumeration envelope vanishes when its small
prefactor vanishes and its girth cutoff diverges. -/
theorem enumeratedExcessEnvelope_vanishes
    {a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {inner : ℕ → ℕ → Finset ℕ}
    {outerBase innerBase : ℝ}
    (hOuter0 : 0 ≤ outerBase) (hOuter1 : outerBase < 1)
    (hInner0 : 0 ≤ innerBase) (hInner1 : innerBase < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Vanishes a)
    (hg : Tendsto g atTop atTop) :
    Vanishes (enumeratedExcessEnvelope
      a g cap inner outerBase innerBase) := by
  have hpow : Vanishes fun n ↦ outerBase ^ (g n) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hOuter0 hOuter1).comp hg
  have hnum : Vanishes fun n ↦ a n + outerBase ^ (g n) := ha.add hpow
  have hdenom : 0 < (1 - outerBase) * (1 - innerBase) :=
    mul_pos (sub_pos.mpr hOuter1) (sub_pos.mpr hInner1)
  have hmajor : Vanishes fun n ↦
      (a n + outerBase ^ (g n)) /
        ((1 - outerBase) * (1 - innerBase)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      hnum.const_mul (((1 - outerBase) * (1 - innerBase))⁻¹)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      unfold enumeratedExcessEnvelope
      exact add_nonneg
        (mul_nonneg (ha0 n) (Finset.sum_nonneg fun i _hi ↦
          Finset.sum_nonneg fun j _hj ↦
            mul_nonneg (pow_nonneg hOuter0 i) (pow_nonneg hInner0 j)))
        (Finset.sum_nonneg fun i _hi ↦
          Finset.sum_nonneg fun j _hj ↦
            mul_nonneg (pow_nonneg hOuter0 i) (pow_nonneg hInner0 j))
  · exact Eventually.of_forall fun n ↦
      enumeratedExcessEnvelope_le hOuter0 hOuter1 hInner0 hInner1 (ha0 n)
  · exact hmajor

/-- Reusable domination form: any nonnegative enumerated excess bounded by
the A.11--A.12 envelope also vanishes. -/
theorem enumeratedExcess_vanishes_of_le_envelope
    {excess a : ℕ → ℝ} {g cap : ℕ → ℕ}
    {inner : ℕ → ℕ → Finset ℕ}
    {outerBase innerBase : ℝ}
    (hOuter0 : 0 ≤ outerBase) (hOuter1 : outerBase < 1)
    (hInner0 : 0 ≤ innerBase) (hInner1 : innerBase < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Vanishes a)
    (hg : Tendsto g atTop atTop)
    (hexcess0 : ∀ᶠ n in atTop, 0 ≤ excess n)
    (hbound : ∀ᶠ n in atTop,
      excess n ≤ enumeratedExcessEnvelope
        a g cap inner outerBase innerBase n) :
    Vanishes excess := by
  exact squeeze_zero' hexcess0 hbound
    (enumeratedExcessEnvelope_vanishes
      hOuter0 hOuter1 hInner0 hInner1 ha0 ha hg)

end

end LowDegree
