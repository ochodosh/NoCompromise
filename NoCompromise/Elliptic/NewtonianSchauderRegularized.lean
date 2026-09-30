module

public import NoCompromise.Elliptic.NewtonianSchauderKernel

@[expose] public section

/-!
# Smooth regularizations of the signed Newtonian Hessian

All derivatives are actual classical derivatives. The uniform inverse-cubic
bound away from the origin permits dominated convergence after subtracting a
Hölder increment. Mixed integration by parts is recorded for the later
identification of the distributional Hessian.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ

/-- The smooth signed fundamental-kernel regularization. -/
def schauderRegularizedKernel (ε : ℝ) (x : E₃) : ℝ :=
  -(4 * Real.pi)⁻¹ * regularizedNewtonKernel ε x

/-- Its actual first derivative for a positive regularization parameter. -/
def schauderRegularizedDerivative (ε : ℝ) (x : E₃) : D₃ :=
  ((4 * Real.pi)⁻¹ * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹) • innerSL ℝ x

/-- Its actual Hessian for a positive regularization parameter. -/
def schauderRegularizedHessian (ε : ℝ) (x : E₃) : E₃ →L[ℝ] D₃ :=
  (4 * Real.pi)⁻¹ •
    ((Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ • (innerSL ℝ (E := E₃)).restrictScalars ℝ -
      (3 * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5)⁻¹) •
        (innerSL ℝ x).smulRight (innerSL ℝ x))

lemma contDiff_schauderRegularizedKernel {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (schauderRegularizedKernel ε) :=
  contDiff_const.mul (contDiff_regularizedNewtonKernel hε)

lemma schauderRegularized_hasFDerivAt_inv_pow {ε : ℝ} (hε : 0 < ε)
    (x : E₃) (k : ℕ) :
    HasFDerivAt (fun y : E₃ => (Real.sqrt (‖y‖ ^ 2 + ε ^ 2) ^ (k + 1))⁻¹)
      ((-((k + 1 : ℕ) : ℝ) / Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ (k + 3)) •
        innerSL ℝ x) x := by
  have hp : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  have hs := (regularizedNewton_sqrt_bounds hε x).1.ne'
  have hn := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).sqrt hp.ne'
  have h := (hasDerivAt_inv (pow_ne_zero (k + 1) hs)).comp_hasFDerivAt x
    (hn.pow (k + 1))
  apply h.congr_fderiv
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Nat.add_sub_cancel, pow_succ]
  simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
  field_simp
  ring

lemma hasFDerivAt_schauderRegularizedKernel {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    HasFDerivAt (schauderRegularizedKernel ε) (schauderRegularizedDerivative ε x) x := by
  have h := (hasFDerivAt_regularizedNewtonKernel hε x).const_mul (-(4 * Real.pi)⁻¹)
  apply h.congr_fderiv
  ext v
  simp only [schauderRegularizedDerivative, regularizedNewtonDerivative,
    smul_apply, smul_eq_mul]
  ring

lemma hasFDerivAt_schauderRegularizedDerivative {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    HasFDerivAt (schauderRegularizedDerivative ε) (schauderRegularizedHessian ε x) x := by
  have h := ((schauderRegularized_hasFDerivAt_inv_pow hε x 2).const_mul
    ((4 * Real.pi)⁻¹)).smul
      (((innerSL ℝ (E := E₃)).restrictScalars ℝ).hasFDerivAt (x := x))
  change HasFDerivAt (schauderRegularizedDerivative ε) _ x at h
  apply h.congr_fderiv
  ext v w
  change (4 * Real.pi)⁻¹ * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ * ⟪v, w⟫_ℝ +
    ((4 * Real.pi)⁻¹ * (-((2 + 1 : ℕ) : ℝ) /
      Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5 * ⟪x, v⟫_ℝ)) * ⟪x, w⟫_ℝ =
    (4 * Real.pi)⁻¹ * ((Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ * ⟪v, w⟫_ℝ -
      3 * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5)⁻¹ * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ))
  norm_num
  ring

lemma fderiv_two_schauderRegularizedKernel {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    fderiv ℝ (fderiv ℝ (schauderRegularizedKernel ε)) x =
      schauderRegularizedHessian ε x := by
  have he : fderiv ℝ (schauderRegularizedKernel ε) = schauderRegularizedDerivative ε :=
    funext fun y => (hasFDerivAt_schauderRegularizedKernel hε y).fderiv
  rw [he, (hasFDerivAt_schauderRegularizedDerivative hε x).fderiv]

lemma norm_schauderRegularizedHessian_le {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    ‖schauderRegularizedHessian ε x‖ ≤
      Real.pi⁻¹ * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ := by
  let s := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)
  have hs : 0 < s := (regularizedNewton_sqrt_bounds hε x).1
  have hxs : ‖x‖ ≤ s := (regularizedNewton_sqrt_bounds hε x).2.1
  have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hr3 : 0 ≤ (s ^ 3)⁻¹ := by positivity
  have hr5 : 0 ≤ 3 * (s ^ 5)⁻¹ := by positivity
  calc
    _ ≤ (4 * Real.pi)⁻¹ * ((s ^ 3)⁻¹ * 1 + (3 * (s ^ 5)⁻¹) * (‖x‖ * ‖x‖)) := by
      rw [schauderRegularizedHessian, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      apply mul_le_mul_of_nonneg_left _ hc
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr3]
        exact mul_le_mul_of_nonneg_left (by
          simpa using (norm_innerSL_le ℝ (E := E₃))) hr3
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr5,
          ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    _ ≤ (4 * Real.pi)⁻¹ * ((s ^ 3)⁻¹ * 1 + (3 * (s ^ 5)⁻¹) * (s * s)) := by
      gcongr
    _ = _ := by
      change (4 * Real.pi)⁻¹ * ((s ^ 3)⁻¹ * 1 + (3 * (s ^ 5)⁻¹) * (s * s)) =
        Real.pi⁻¹ * (s ^ 3)⁻¹
      field_simp
      ring

lemma norm_schauderRegularizedHessian_le_inv_norm {ε : ℝ} (hε : 0 < ε)
    {x : E₃} (hx : x ≠ 0) :
    ‖schauderRegularizedHessian ε x‖ ≤ Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ := by
  apply (norm_schauderRegularizedHessian_le hε x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply inv_anti₀ (pow_pos (norm_pos_iff.mpr hx) 3)
  exact pow_le_pow_left₀ (norm_nonneg x) (regularizedNewton_sqrt_bounds hε x).2.1 3

lemma tendsto_schauderRegularizedHessian {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {x : E₃} (hx : x ≠ 0) :
    Tendsto (fun j => schauderRegularizedHessian (ε j) x) atTop
      (𝓝 (schauderNewtonHessian x)) := by
  have hn := norm_ne_zero_iff.mpr hx
  have hs : Tendsto (fun j => Real.sqrt (‖x‖ ^ 2 + ε j ^ 2)) atTop (𝓝 ‖x‖) := by
    have ht0 : Tendsto (fun j => ‖x‖ ^ 2 + ε j ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
        ((tendsto_const_nhds (x := ‖x‖ ^ 2)).add (hε.pow 2))
    have ht := ht0.sqrt
    rwa [Real.sqrt_sq (norm_nonneg x)] at ht
  exact (((hs.pow 3).inv₀ (pow_ne_zero _ hn)).smul tendsto_const_nhds |>.sub
    ((tendsto_const_nhds.mul ((hs.pow 5).inv₀ (pow_ne_zero _ hn))).smul
      tendsto_const_nhds)).const_smul _

lemma integral_schauder_mixed_derivative_comm {u φ : E₃ → ℝ}
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ)
    (i j : Fin 3) :
    (∫ x, u x * poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x) =
      ∫ x, φ x * poissonCoordinateDerivative j (poissonCoordinateDerivative i u) x := by
  have hdu := ContDiff.poissonCoordinateDerivative (r := 1) hu i
  have hdφ := ContDiff.poissonCoordinateDerivative (r := 1) hφ j
  have hcdφ := HasCompactSupport.poissonCoordinateDerivative hcφ j
  have h1 := integral_mul_poissonCoordinateDerivative (hu.of_le (by norm_num)) hdφ hcdφ i
  have h2 := integral_mul_poissonCoordinateDerivative hdu (hφ.of_le (by norm_num)) hcφ j
  simp_rw [mul_comm (poissonCoordinateDerivative i u _)] at h2
  linarith only [h1, h2]

/-- Coordinate Hessian entries of the genuine regularized potential kernel. -/
def schauderRegularizedHessianEntry (ε : ℝ) (i j : Fin 3) (x : E₃) : ℝ :=
  schauderRegularizedHessian ε x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

lemma schauderRegularizedHessianEntry_eq (ε : ℝ) (i j : Fin 3) (x : E₃) :
    schauderRegularizedHessianEntry ε i j x = (4 * Real.pi)⁻¹ *
      ((if i = j then 1 else 0) * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ -
        3 * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5)⁻¹ * x i * x j) := by
  change (4 * Real.pi)⁻¹ *
    ((Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ *
        ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1⟫_ℝ -
      3 * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5)⁻¹ *
        (⟪x, EuclideanSpace.single i 1⟫_ℝ * ⟪x, EuclideanSpace.single j 1⟫_ℝ)) = _
  simp only [EuclideanSpace.inner_single_right]
  by_cases h : i = j <;> simp [h] <;> ring

lemma schauderRegularizedHessianEntry_symm (ε : ℝ) (i j : Fin 3) (x : E₃) :
    schauderRegularizedHessianEntry ε i j x = schauderRegularizedHessianEntry ε j i x := by
  simp only [schauderRegularizedHessianEntry_eq]
  by_cases h : i = j
  · simp [h]
  · simp only [h, Ne.symm h, ite_false]
    ring

lemma continuous_schauderRegularizedHessianEntry {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    Continuous (schauderRegularizedHessianEntry ε i j) := by
  have he : schauderRegularizedHessianEntry ε i j = fun x =>
      fderiv ℝ (fderiv ℝ (schauderRegularizedKernel ε)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    funext x
    rw [fderiv_two_schauderRegularizedKernel hε]
    rfl
  rw [he]
  have hc := (contDiff_schauderRegularizedKernel hε).fderiv_right
    (m := 1) (by simp) |>.fderiv_right (m := 0) (by norm_num)
  exact (hc.continuous.clm_apply continuous_const).clm_apply continuous_const

lemma norm_schauderRegularizedHessianEntry_le {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    ‖schauderRegularizedHessianEntry ε i j x‖ ≤ Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ := by
  have h := ((schauderRegularizedHessian ε x (EuclideanSpace.single i 1)).le_opNorm
    (EuclideanSpace.single j 1)).trans
    (mul_le_mul_of_nonneg_right ((schauderRegularizedHessian ε x).le_opNorm
      (EuclideanSpace.single i 1)) (norm_nonneg _))
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (norm_schauderRegularizedHessian_le_inv_norm hε hx)

lemma schauderRegularizedHessianEntry_trace {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    ∑ i : Fin 3, schauderRegularizedHessianEntry ε i i x =
      (4 * Real.pi)⁻¹ * newtonApproximationDensity ε x := by
  have hs := (regularizedNewton_sqrt_bounds hε x).1.ne'
  have hsq := Real.sq_sqrt (show 0 ≤ ‖x‖ ^ 2 + ε ^ 2 by positivity)
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn
  simp only [Fin.sum_univ_three, schauderRegularizedHessianEntry_eq, ite_true,
    one_mul, newtonApproximationDensity]
  field_simp
  nlinarith

lemma integral_schauderRegularizedHessianEntry_test {ε : ℝ} (hε : 0 < ε)
    {φ : E₃ → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) (i j : Fin 3) :
    (∫ x, schauderRegularizedKernel ε x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x) =
      ∫ x, schauderRegularizedHessianEntry ε i j x * φ x := by
  have hu : ContDiff ℝ 2 (schauderRegularizedKernel ε) :=
    (contDiff_schauderRegularizedKernel hε).of_le (by simp)
  rw [integral_schauder_mixed_derivative_comm hu hφ hcφ]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [poissonCoordinateDerivative_second hu,
    fderiv_two_schauderRegularizedKernel hε]
  change φ x * schauderRegularizedHessianEntry ε j i x = _
  rw [schauderRegularizedHessianEntry_symm ε j i x, mul_comm]

end LiquidDrop
