import NoCompromise.Regularity.ApproxHarmonicEstimateBounds

/-! # Exact scaling of the planar approximate-harmonic residual -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Dilation commutes with the total gradient, including at points where the
function is not differentiable. -/
lemma approxHarmonic_gradient_comp_smul {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f (r • y)) x = r • gradient f (r • x) := by
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_single, fderiv_comp_smul]
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul,
    gradient_apply_eq_fderiv_single]

lemma approxHarmonic_gradient_mul {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => r * f y) x = r • gradient f x := by
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_single]
  change fderiv ℝ (r • f) x (EuclideanSpace.single i 1) = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, PiLp.smul_apply,
    smul_eq_mul, gradient_apply_eq_fderiv_single]

/-- The physical height rescaling preserves slopes exactly. -/
lemma approxHarmonic_gradient_rescale
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) {r : ℝ} (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    gradient (fun y => r * f (r⁻¹ • y)) x = gradient f (r⁻¹ • x) := by
  rw [approxHarmonic_gradient_mul, approxHarmonic_gradient_comp_smul,
    smul_smul, mul_inv_cancel₀ hr, one_smul]

lemma approxHarmonic_image_half_ball {r : ℝ} (hr : 0 < r) :
    (fun x : EuclideanSpace ℝ (Fin 2) => r • x) '' ball 0 (1 / 2) = ball 0 (r / 2) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le] at *
    nlinarith
  · intro hx
    refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hr.ne' x⟩
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at *
    apply (mul_lt_mul_iff_right₀ hr).mp
    simp only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    linarith

/-- The physical pairing is radius times the pairing of the normalized height
and pulled-back test, with no differentiability assumption on the height. -/
theorem approxHarmonic_integral_rescale
    (f ζ : EuclideanSpace ℝ (Fin 2) → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 2),
      inner ℝ (gradient (fun y => r * f (r⁻¹ • y)) x) (gradient ζ x)) =
      r * ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ (gradient f x) (gradient (fun y => ζ (r • y)) x) := by
  rw [← approxHarmonic_image_half_ball hr, setIntegral_image_smul _ _ hr]
  simp_rw [approxHarmonic_gradient_rescale f hr.ne', inv_smul_smul₀ hr.ne',
    approxHarmonic_gradient_comp_smul, inner_smul_right]
  rw [integral_const_mul]
  ring

/-- Every unit-disk test estimate transfers to a physical disk with the precise
radius-squared factor. The normalized error can include the scaled volume error. -/
theorem approxHarmonic_residual_rescale
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {C a : ℝ}
    (hres : ∀ (ζ : EuclideanSpace ℝ (Fin 2) → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball 0 (1 / 2) → ∀ M : ℝ, 0 ≤ M →
      (∀ p, ‖gradient ζ p‖ ≤ M) →
      |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ (gradient f p) (gradient ζ p)| ≤ C * a * M)
    {r : ℝ} (hr : 0 < r) {ζ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (r / 2))
    {M : ℝ} (hM : 0 ≤ M) (hζM : ∀ p, ‖gradient ζ p‖ ≤ M) :
    |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 2),
      inner ℝ (gradient (fun y => r * f (r⁻¹ • y)) p) (gradient ζ p)| ≤
      C * r ^ 2 * a * M := by
  let ψ := fun p => ζ (r • p)
  have hψ : ContDiff ℝ 1 ψ := hζ.comp (contDiff_id.const_smul r)
  have hcψ : HasCompactSupport ψ :=
    hcζ.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')
  have hsψ : tsupport ψ ⊆ ball 0 (1 / 2) := by
    intro p hp
    have hz := hsζ (tsupport_comp_subset_preimage ζ
      (show Continuous (fun p : EuclideanSpace ℝ (Fin 2) => r • p) by fun_prop) hp)
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le] at hz ⊢
    nlinarith
  have hψM : ∀ p, ‖gradient ψ p‖ ≤ r * M := by
    intro p
    rw [approxHarmonic_gradient_comp_smul, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left (hζM _) hr.le
  have hh := hres ψ hψ hcψ hsψ (r * M) (mul_nonneg hr.le hM) hψM
  rw [approxHarmonic_integral_rescale f ζ hr, abs_mul, abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left hh hr.le).trans_eq (by ring)

end LiquidDrop
