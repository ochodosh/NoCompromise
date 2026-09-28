import NoCompromise.BV.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiating integrals with uniform quadratic remainders

A uniform quadratic expansion on a finite measure space can be integrated before
taking the derivative. This keeps the finite mass and integrability hypotheses
explicit in the surface first-variation argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LiquidDrop

lemma hasDerivAt_zero_of_quadratic_remainder
    {f : ℝ → ℝ} {b C : ℝ}
    (hf : ∀ t : ℝ, |t| ≤ 1 → |f t - f 0 - t * b| ≤ C * t ^ 2) :
    HasDerivAt f b 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun t => mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
    (abs_nonneg _))
  · filter_upwards [(continuous_abs.tendsto (0 : ℝ)).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < 1 by norm_num))] with t ht
    calc
      |t|⁻¹ * |f t - f 0 - t * b| ≤ |t|⁻¹ * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left (hf t ht.le) (inv_nonneg.mpr (abs_nonneg _))
      _ = C * |t| := by
        rw [← sq_abs]
        by_cases hz : t = 0
        · simp [hz]
        · field_simp
  · simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul C

/-- Integrability near zero follows from the uniform remainder bound. -/
lemma integrable_of_quadratic_remainder
    {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    {J : ℝ → S → ℝ} {b : S → ℝ} (hb : Integrable b μ)
    {C t : ℝ} (hJ : AEStronglyMeasurable (J t) μ)
    (hr : ∀ᵐ x ∂μ, |J t x - 1 - t * b x| ≤ C * t ^ 2) : Integrable (J t) μ := by
  apply ((integrable_const (C * t ^ 2 + 1)).add (hb.norm.const_mul |t|)).mono' hJ
  filter_upwards [hr] with x hx
  change ‖J t x‖ ≤ C * t ^ 2 + 1 + |t| * ‖b x‖
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hlo := (abs_le.mp hx).1
  have hhi := (abs_le.mp hx).2
  have hm : |t * b x| = |t| * ‖b x‖ := by rw [abs_mul, Real.norm_eq_abs]
  have hn := neg_le_abs (t * b x)
  have hp := le_abs_self (t * b x)
  rw [hm] at hn hp
  constructor <;> linarith

/-- Integration preserves a quadratic expansion when the measure has finite mass. -/
theorem hasDerivAt_integral_of_quadratic_remainder
    {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    {J : ℝ → S → ℝ} {b : S → ℝ} (hb : Integrable b μ)
    (hJ : ∀ t : ℝ, |t| ≤ 1 → AEStronglyMeasurable (J t) μ)
    (hzero : ∀ᵐ x ∂μ, J 0 x = 1) {C : ℝ}
    (hr : ∀ t : ℝ, |t| ≤ 1 → ∀ᵐ x ∂μ, |J t x - 1 - t * b x| ≤ C * t ^ 2) :
    HasDerivAt (fun t => ∫ x, J t x ∂μ) (∫ x, b x ∂μ) 0 := by
  apply hasDerivAt_zero_of_quadratic_remainder (C := C * μ.real univ)
  intro t ht
  have hi := integrable_of_quadratic_remainder hb (hJ t ht) (hr t ht)
  have hi1 : Integrable (fun _ : S => (1 : ℝ)) μ := integrable_const _
  have hiz : (∫ x, J 0 x ∂μ) = ∫ _ : S, (1 : ℝ) ∂μ := integral_congr_ae hzero
  have hisub : Integrable (fun x => J t x - 1) μ := hi.sub hi1
  rw [hiz, ← integral_const_mul, ← integral_sub hi hi1,
    ← integral_sub hisub (hb.const_mul t)]
  have he := norm_integral_le_of_norm_le (f := fun x => J t x - 1 - t * b x)
    (integrable_const (C * t ^ 2))
    ((hr t ht).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  simpa only [Real.norm_eq_abs, integral_const, smul_eq_mul] using he.trans_eq
    (show (∫ _ : S, C * t ^ 2 ∂μ) = C * μ.real univ * t ^ 2 from by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring)

end LiquidDrop
