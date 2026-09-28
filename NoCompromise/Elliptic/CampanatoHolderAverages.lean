import NoCompromise.Elliptic.CampanatoGrowth
import NoCompromise.Measure.BallDifferentiation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Quantitative comparison of actual ball averages from squared mean oscillation. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_norm_average_sq_le {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    {f : X → F} (hf : MemLp f 2 μ) :
    ‖⨍ x, f x ∂μ‖ ^ 2 ≤ (μ.real univ)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hm : 0 < μ.real univ := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  have hi := hf.integrable (by norm_num)
  have hi₂ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hk : (∫ _x : X, (μ.real univ)⁻¹ ∂μ) = 1 := by
    rw [integral_const]
    simp only [smul_eq_mul]
    exact mul_inv_cancel₀ hm.ne'
  have h := norm_integral_smul_sq_le_of_probability_kernel
    (measurable_const (a := (μ.real univ)⁻¹)) (integrable_const _)
    (fun _ => inv_nonneg.mpr hm.le) hk (hi.smul _) (hi₂.const_mul _)
  simpa only [integral_smul, integral_const_mul, ← average_eq] using h

lemma campanato_average_sub_average_sq_le {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ univ ≠ 0) (hμν : μ ≤ ν) {f : X → F} (hf : MemLp f 2 ν) :
    ‖(⨍ x, f x ∂μ) - ⨍ x, f x ∂ν‖ ^ 2 ≤
      (μ.real univ)⁻¹ * ∫ x, ‖f x - ⨍ y, f y ∂ν‖ ^ 2 ∂ν := by
  let : NeZero μ := ⟨fun h => hμ (by rw [h]; simp)⟩
  have hg := hf.sub (memLp_const (⨍ y, f y ∂ν))
  have hgm := hg.mono_measure hμν
  have hj := campanato_norm_average_sq_le hμ hgm
  have hfm := hf.mono_measure hμν
  rw [average_sub (hfm.integrable (by norm_num)) (integrable_const _), average_const] at hj
  exact hj.trans (mul_le_mul_of_nonneg_left
    (integral_mono_measure hμν (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg))
    (inv_nonneg.mpr ENNReal.toReal_nonneg))

lemma campanato_volume_ball_double {n : ℕ} (hn : 0 < n)
    (x z : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    volume.real (ball z r) = (2 : ℝ) ^ n * volume.real (ball x (r / 2)) := by
  rw [frozen_real_volume_ball hn z hr.le,
    frozen_real_volume_ball hn x (by positivity), div_pow]
  field_simp

/-- A contained ball whose radius is at least half the larger radius has a
quantitatively close average, with no common-center requirement. -/
theorem campanato_average_comparable_radius_bound {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} {x z : EuclideanSpace ℝ (Fin n)}
    {r s B γ : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hhalf : r / 2 ≤ s)
    (hsub : ball x s ⊆ ball z r)
    (hf : MemLp f 2 (volume.restrict (ball z r)))
    (hosc : (∫ y in ball z r, ‖f y - ⨍ w in ball z r, f w‖ ^ 2) ≤
      (B * r ^ γ) ^ 2 * volume.real (ball z r)) :
    ‖(⨍ y in ball x s, f y) - ⨍ y in ball z r, f y‖ ≤
      Real.sqrt ((2 : ℝ) ^ n) * B * r ^ γ := by
  have hs : 0 < s := (div_pos hr (by norm_num : (0 : ℝ) < 2)).trans_le hhalf
  let : IsFiniteMeasure (volume.restrict (ball z r)) :=
    ⟨by simpa using (isBounded_ball (x := z) (r := r)).measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (ball x s)) :=
    ⟨by simpa using (isBounded_ball (x := x) (r := s)).measure_lt_top⟩
  have hm : volume (ball x s) ≠ 0 := (measure_ball_pos volume x hs).ne'
  have hmreal : 0 < volume.real (ball x s) :=
    ENNReal.toReal_pos hm (isBounded_ball.measure_lt_top.ne)
  have hvol : volume.real (ball z r) ≤ (2 : ℝ) ^ n * volume.real (ball x s) := by
    rw [campanato_volume_ball_double hn x z hr]
    exact mul_le_mul_of_nonneg_left (measureReal_mono (ball_subset_ball hhalf))
      (pow_nonneg (by norm_num) n)
  have hj := campanato_average_sub_average_sq_le
    (by simpa using hm) (Measure.restrict_mono hsub (le_rfl (a := volume))) hf
  simp only [Measure.real, Measure.restrict_apply_univ] at hj
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (volume.real (ball x s))⁻¹ *
        (∫ y in ball z r, ‖f y - ⨍ w in ball z r, f w‖ ^ 2) := hj
    _ ≤ (volume.real (ball x s))⁻¹ *
        ((B * r ^ γ) ^ 2 * volume.real (ball z r)) :=
      mul_le_mul_of_nonneg_left hosc (inv_nonneg.mpr hmreal.le)
    _ ≤ (volume.real (ball x s))⁻¹ *
        ((B * r ^ γ) ^ 2 * ((2 : ℝ) ^ n * volume.real (ball x s))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol (sq_nonneg _))
        (inv_nonneg.mpr hmreal.le)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
      field_simp [hmreal.ne']

/-- The adjacent dyadic averages are covered by the comparable-radius estimate. -/
theorem campanato_average_half_radius_bound {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} {x z : EuclideanSpace ℝ (Fin n)}
    {r B γ : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hsub : ball x (r / 2) ⊆ ball z r)
    (hf : MemLp f 2 (volume.restrict (ball z r)))
    (hosc : (∫ y in ball z r, ‖f y - ⨍ w in ball z r, f w‖ ^ 2) ≤
      (B * r ^ γ) ^ 2 * volume.real (ball z r)) :
    ‖(⨍ y in ball x (r / 2), f y) - ⨍ y in ball z r, f y‖ ≤
      Real.sqrt ((2 : ℝ) ^ n) * B * r ^ γ :=
  campanato_average_comparable_radius_bound hn hr hB le_rfl hsub hf hosc

end LiquidDrop
