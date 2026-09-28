import NoCompromise.Regularity.GraphAffineHeightArea
import NoCompromise.Regularity.HarmonicBlowupNormalization
import NoCompromise.Regularity.HarmonicAffine

/-! # Normalization and harmonic-affine error control for the height moment -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual average retains a global height clamp. -/
lemma graphAffineHeight_average_le
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hf : ∀ x, |f x| ≤ τ) :
    |⨍ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f x| ≤ τ := by
  let μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin 2)))
        (r := (1 / 2 : ℝ)))⟩
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (ae_of_all μ fun x => show ‖f x‖ ≤ τ by simpa only [Real.norm_eq_abs] using hf x)
  change |average μ f| ≤ τ
  rw [average_eq, smul_eq_mul, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg]
  by_cases hz : μ.real univ = 0
  · simp only [hz, inv_zero, zero_mul]
    exact hτ
  · calc
      _ ≤ (μ.real univ)⁻¹ * (τ * μ.real univ) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr measureReal_nonneg)
      _ = τ := by field_simp

/-- Exact normalization yields the elementary two-error square estimate. -/
lemma graphAffineHeight_two_errors
    (f h : EuclideanSpace ℝ (Fin 2) → ℝ) {a : ℝ} (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f x - ((⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y) + a * h 0) -
      inner ℝ (a • gradient h 0) x) ^ 2 ≤
      2 * a ^ 2 * (harmonicBlowupFunction f a x - h x) ^ 2 +
        2 * a ^ 2 * (h x - h 0 - inner ℝ (gradient h 0) x) ^ 2 := by
  have hid : f x - ((⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y) + a * h 0) -
      inner ℝ (a • gradient h 0) x =
      a * ((harmonicBlowupFunction f a x - h x) +
        (h x - h 0 - inner ℝ (gradient h 0) x)) := by
    rw [harmonicBlowupFunction, real_inner_smul_left]
    field_simp
    ring
  rw [hid, mul_pow]
  have hs := sq_nonneg ((harmonicBlowupFunction f a x - h x) -
    (h x - h 0 - inner ℝ (gradient h 0) x))
  nlinarith [mul_nonneg (sq_nonneg a) hs]

/-- Actual H¹ data make the normalized error integrable on the quarter disk. -/
lemma integrableOn_graphAffineHeight_normalized_error
    {f h : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hh : HasH1GradientOn h (gradient h) (ball 0 (1 / 4))) (a : ℝ) :
    IntegrableOn (fun x => (harmonicBlowupFunction f a x - h x) ^ 2)
      (ball 0 (1 / 4)) volume := by
  have hs : ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) ⊆ ball 0 (1 / 2) :=
    ball_subset_ball (by norm_num)
  have hf1 := (harmonicBlowup_hasH1GradientOn (harmonicBlowup_hasH1_lipschitz hf) a).mono hs
  have hi := (hf1.memLp_function.sub hh.memLp_function).integrable_norm_pow
    (by norm_num : 2 ≠ 0)
  simpa only [IntegrableOn, Pi.sub_apply, Real.norm_eq_abs, sq_abs] using hi

/-- The graph's affine discrepancy is controlled by the genuine normalized
harmonic error and the harmonic affine error, with a constant before the radius. -/
theorem graphAffineHeight_base_error_le
    {f h : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hh : HasH1GradientOn h (gradient h) (ball 0 (1 / 4)))
    (hc : ContinuousOn h (ball 0 (1 / 4))) {a θ A : ℝ}
    (ha : 0 < a) (hθ : θ < 1 / 32)
    (hnorm : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
      |harmonicBlowupFunction f a x - h x| ^ 2) ≤ θ ^ 6)
    (haffine : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (4 * θ),
      ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2) ≤ A * θ ^ 6) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (4 * θ),
      (f x - ((⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y) + a * h 0) -
        inner ℝ (a • gradient h 0) x) ^ 2) ≤ 2 * a ^ 2 * (1 + A) * θ ^ 6 := by
  have hs : ball (0 : EuclideanSpace ℝ (Fin 2)) (4 * θ) ⊆ ball 0 (1 / 4) :=
    ball_subset_ball (by linarith)
  have hi := integrableOn_graphAffineHeight_normalized_error hf hh a
  have hi' := hi.mono_set hs
  have hj := harmonicAffine_integrable_remainder hc hθ
  simp only [Real.norm_eq_abs, sq_abs] at hj haffine
  simp only [sq_abs] at hnorm
  have ht := (setIntegral_mono_set hi (ae_of_all _ fun x => sq_nonneg _)
    (ae_of_all _ hs)).trans hnorm
  have hferr := integrableOn_graphAffineHeight_base hf (a • gradient h 0)
    ((⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y) + a * h 0)
    (A := ball 0 (4 * θ)) isBounded_ball
  have hb := integral_mono hferr ((hi'.const_mul (2 * a ^ 2)).add (hj.const_mul (2 * a ^ 2)))
    (graphAffineHeight_two_errors f h ha.ne')
  simp only [Pi.add_apply] at hb
  rw [integral_add (hi'.const_mul _) (hj.const_mul _), integral_const_mul,
    integral_const_mul] at hb
  have ht' := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * a ^ 2)
  have hj' := mul_le_mul_of_nonneg_left haffine (by positivity : 0 ≤ 2 * a ^ 2)
  exact hb.trans ((add_le_add ht' hj').trans_eq (by ring))

end LiquidDrop
