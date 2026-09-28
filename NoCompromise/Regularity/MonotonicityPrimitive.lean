import NoCompromise.Measure.CumulativeDerivative
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Compact radial primitives

A test supported in a positive annulus has a primitive which is constant near
the origin and vanishes beyond the annulus. A harmless cutoff on negative
radii makes this primitive compactly supported on the real line as well.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Interval
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def radialTailPrimitive (p : ℝ → ℝ) (b r : ℝ) : ℝ := ∫ t in r..b, p t

lemma hasDerivAt_radialTailPrimitive {p : ℝ → ℝ} (hp : Continuous p) (b r : ℝ) :
    HasDerivAt (radialTailPrimitive p b) (-p r) r :=
  intervalIntegral.integral_hasDerivAt_left (hp.intervalIntegrable r b)
    hp.stronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt

lemma contDiff_radialTailPrimitive {p : ℝ → ℝ} (hp : Continuous p) (b : ℝ) :
    ContDiff ℝ 1 (radialTailPrimitive p b) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (hasDerivAt_radialTailPrimitive hp b r).differentiableAt, ?_⟩
  have hd : deriv (radialTailPrimitive p b) = fun r => -p r :=
    funext fun r => (hasDerivAt_radialTailPrimitive hp b r).deriv
  rw [hd]
  exact hp.neg

lemma radialTailPrimitive_eq_zero_above {p : ℝ → ℝ} {b r : ℝ}
    (hp : ∀ t, b ≤ t → p t = 0) (hr : b ≤ r) : radialTailPrimitive p b r = 0 := by
  rw [radialTailPrimitive, intervalIntegral.integral_symm]
  have he : (∫ t in b..r, p t) = ∫ t in b..r, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    exact hp t ht.1
  rw [he, intervalIntegral.integral_zero, neg_zero]

lemma radialTailPrimitive_eq_below {p : ℝ → ℝ} (hp : Continuous p) {a b r : ℝ}
    (hz : ∀ t, t ≤ a → p t = 0) (hr : r ≤ a) :
    radialTailPrimitive p b r = radialTailPrimitive p b a := by
  have he : (∫ t in r..a, p t) = ∫ t in r..a, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    exact hz t ht.2
  have hadd : (∫ t in r..a, p t) + (∫ t in a..b, p t) = ∫ t in r..b, p t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hp.intervalIntegrable r a) (hp.intervalIntegrable a b)
  rw [he, intervalIntegral.integral_zero, zero_add] at hadd
  exact hadd.symm

/-- A real-line compact realization of the radial tail primitive. -/
def compactRadialPrimitive (p : ℝ → ℝ) (b r : ℝ) : ℝ :=
  Real.smoothTransition (r + 2) * radialTailPrimitive p b r

lemma contDiff_compactRadialPrimitive {p : ℝ → ℝ} (hp : Continuous p) (b : ℝ) :
    ContDiff ℝ 1 (compactRadialPrimitive p b) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_radialTailPrimitive hp b)

lemma compactRadialPrimitive_eq_tail {p : ℝ → ℝ} {b r : ℝ} (hr : -1 ≤ r) :
    compactRadialPrimitive p b r = radialTailPrimitive p b r := by
  rw [compactRadialPrimitive, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

lemma hasDerivAt_compactRadialPrimitive {p : ℝ → ℝ} (hp : Continuous p)
    (b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (compactRadialPrimitive p b) (-p r) r := by
  have he : compactRadialPrimitive p b =ᶠ[𝓝 r] radialTailPrimitive p b := by
    filter_upwards [eventually_gt_nhds (by linarith : -1 < r)] with t ht
    exact compactRadialPrimitive_eq_tail ht.le
  exact (hasDerivAt_radialTailPrimitive hp b r).congr_of_eventuallyEq he

lemma compactRadialPrimitive_eq_zero_above {p : ℝ → ℝ} {b r : ℝ}
    (hp : ∀ t, b ≤ t → p t = 0) (hr : b ≤ r) : compactRadialPrimitive p b r = 0 := by
  rw [compactRadialPrimitive, radialTailPrimitive_eq_zero_above hp hr, mul_zero]

lemma hasCompactSupport_compactRadialPrimitive {p : ℝ → ℝ} {b : ℝ}
    (hp : ∀ t, b ≤ t → p t = 0) : HasCompactSupport (compactRadialPrimitive p b) := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (s := Icc (-2 : ℝ) b)
  apply closure_minimal _ isClosed_Icc
  intro r hr
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn | hn
  · exact hr (by
      rw [compactRadialPrimitive, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul])
  · exact hr (compactRadialPrimitive_eq_zero_above hp hn.le)

lemma compactRadialPrimitive_constant_near_zero {p : ℝ → ℝ} (hp : Continuous p)
    {a b : ℝ} (ha : 0 < a) (hz : ∀ t, t ≤ a → p t = 0) :
    ∀ᶠ r in 𝓝 (0 : ℝ), compactRadialPrimitive p b r = compactRadialPrimitive p b 0 := by
  filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_lt_nhds ha] with r hr hrea
  rw [compactRadialPrimitive_eq_tail hr.le,
    compactRadialPrimitive_eq_tail (by norm_num : (-1 : ℝ) ≤ 0),
    radialTailPrimitive_eq_below hp hz hrea.le,
    radialTailPrimitive_eq_below hp hz ha.le]

lemma compactRadialPrimitive_nonneg {p : ℝ → ℝ} {b : ℝ}
    (hp : ∀ t, 0 ≤ p t) (hz : ∀ t, b ≤ t → p t = 0) (r : ℝ) :
    0 ≤ compactRadialPrimitive p b r := by
  by_cases hr : r ≤ b
  · apply mul_nonneg (Real.smoothTransition.nonneg _)
    exact intervalIntegral.integral_nonneg hr (fun t _ => hp t)
  · rw [compactRadialPrimitive_eq_zero_above hz (le_of_not_ge hr)]

/-- The actual compact C¹ primitive needed by the first-variation test. -/
theorem exists_compact_radial_primitive {p : ℝ → ℝ} (hp : Continuous p)
    {a b : ℝ} (ha : 0 < a) (hs : tsupport p ⊆ Ioo a b) (hn : ∀ t, 0 ≤ p t) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
      (∀ᶠ r in 𝓝 (0 : ℝ), η r = η 0) ∧
      (∀ r, b ≤ r → η r = 0) ∧ (∀ r, 0 ≤ η r) ∧
      ∀ r, 0 ≤ r → HasDerivAt η (-p r) r := by
  have hlo : ∀ t, t ≤ a → p t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => (not_lt_of_ge ht) (hs h).1)
  have hup : ∀ t, b ≤ t → p t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => (not_lt_of_ge ht) (hs h).2)
  exact ⟨compactRadialPrimitive p b, contDiff_compactRadialPrimitive hp b,
    hasCompactSupport_compactRadialPrimitive hup,
    compactRadialPrimitive_constant_near_zero hp ha hlo,
    fun r hr => compactRadialPrimitive_eq_zero_above hup hr,
    compactRadialPrimitive_nonneg hn hup,
    fun r hr => hasDerivAt_compactRadialPrimitive hp b hr⟩

end LiquidDrop
