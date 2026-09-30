module

public import NoCompromise.Elliptic.Newtonian

@[expose] public section

/-!
# Classical Newtonian kernels for the Schauder estimate

The signed fundamental solution is `-1 / (4π |x|)`. Its derivatives are proved
on the punctured space. All formulas use the total inverse convention at zero;
no classical differentiability at the singular point is asserted.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ

/-- The signed three-dimensional fundamental solution of the Laplacian. -/
def schauderNewtonKernel (x : E₃) : ℝ := -(4 * Real.pi)⁻¹ * ‖x‖⁻¹

/-- The classical first derivative away from the origin. -/
def schauderNewtonDerivative (x : E₃) : D₃ :=
  ((4 * Real.pi)⁻¹ * (‖x‖ ^ 3)⁻¹) • innerSL ℝ x

/-- The Hessian kernel as a continuous bilinear form. -/
def schauderNewtonHessian (x : E₃) : E₃ →L[ℝ] D₃ :=
  (4 * Real.pi)⁻¹ • ((‖x‖ ^ 3)⁻¹ • (innerSL ℝ (E := E₃)).restrictScalars ℝ -
    (3 * (‖x‖ ^ 5)⁻¹) • (innerSL ℝ x).smulRight (innerSL ℝ x))

lemma schauderNewton_hasFDerivAt_norm {x : E₃} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E₃ => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).sqrt
    (sq_pos_of_pos hn).ne'
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert! h using 1
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  norm_num [smul_eq_mul]
  field_simp

lemma schauderNewton_hasFDerivAt_inv_norm_pow {x : E₃} (hx : x ≠ 0) (k : ℕ) :
    HasFDerivAt (fun y : E₃ => (‖y‖ ^ (k + 1))⁻¹)
      ((-((k + 1 : ℕ) : ℝ) / ‖x‖ ^ (k + 3)) • innerSL ℝ x) x := by
  have hn := norm_ne_zero_iff.mpr hx
  have h := (hasDerivAt_inv (pow_ne_zero (k + 1) hn)).comp_hasFDerivAt x
    ((schauderNewton_hasFDerivAt_norm hx).pow (k + 1))
  convert! h using 1
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
    Nat.add_sub_cancel, pow_succ]
  simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
  field_simp

lemma contDiffAt_schauderNewtonKernel {x : E₃} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) schauderNewtonKernel x := by
  exact contDiffAt_const.mul
    ((contDiffAt_id.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx))

lemma hasFDerivAt_schauderNewtonKernel {x : E₃} (hx : x ≠ 0) :
    HasFDerivAt schauderNewtonKernel (schauderNewtonDerivative x) x := by
  have h := (schauderNewton_hasFDerivAt_inv_norm_pow hx 0).const_mul (-(4 * Real.pi)⁻¹)
  convert! h using 1
  · funext y
    simp only [schauderNewtonKernel, zero_add, pow_one]
  · ext v
    simp only [schauderNewtonDerivative, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    norm_num
    ring

lemma hasFDerivAt_schauderNewtonDerivative {x : E₃} (hx : x ≠ 0) :
    HasFDerivAt schauderNewtonDerivative (schauderNewtonHessian x) x := by
  have h := ((schauderNewton_hasFDerivAt_inv_norm_pow hx 2).const_mul
    ((4 * Real.pi)⁻¹)).smul
      (((innerSL ℝ (E := E₃)).restrictScalars ℝ).hasFDerivAt (x := x))
  change HasFDerivAt schauderNewtonDerivative _ x at h
  apply h.congr_fderiv
  ext v w
  change (4 * Real.pi)⁻¹ * (‖x‖ ^ 3)⁻¹ * ⟪v, w⟫_ℝ +
    ((4 * Real.pi)⁻¹ * (-((2 + 1 : ℕ) : ℝ) / ‖x‖ ^ 5 * ⟪x, v⟫_ℝ)) *
      ⟪x, w⟫_ℝ =
    (4 * Real.pi)⁻¹ * ((‖x‖ ^ 3)⁻¹ * ⟪v, w⟫_ℝ -
      3 * (‖x‖ ^ 5)⁻¹ * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ))
  norm_num
  ring

lemma fderiv_schauderNewtonKernel {x : E₃} (hx : x ≠ 0) :
    fderiv ℝ schauderNewtonKernel x = schauderNewtonDerivative x :=
  (hasFDerivAt_schauderNewtonKernel hx).fderiv

lemma fderiv_two_schauderNewtonKernel {x : E₃} (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ schauderNewtonKernel) x = schauderNewtonHessian x := by
  have he : fderiv ℝ schauderNewtonKernel =ᶠ[𝓝 x] schauderNewtonDerivative :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy =>
      fderiv_schauderNewtonKernel hy
  rw [he.fderiv_eq, (hasFDerivAt_schauderNewtonDerivative hx).fderiv]

lemma schauderNewtonHessian_apply (x v w : E₃) :
    schauderNewtonHessian x v w = (4 * Real.pi)⁻¹ *
      ((‖x‖ ^ 3)⁻¹ * ⟪v, w⟫_ℝ - 3 * (‖x‖ ^ 5)⁻¹ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  change (4 * Real.pi)⁻¹ * ((‖x‖ ^ 3)⁻¹ * ⟪v, w⟫_ℝ -
    3 * (‖x‖ ^ 5)⁻¹ * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ)) = _
  ring

lemma norm_schauderNewtonHessian_le (x : E₃) :
    ‖schauderNewtonHessian x‖ ≤ (Real.pi)⁻¹ * (‖x‖ ^ 3)⁻¹ := by
  have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hr3 : 0 ≤ (‖x‖ ^ 3)⁻¹ := by positivity
  have hr5 : 0 ≤ 3 * (‖x‖ ^ 5)⁻¹ := by positivity
  calc
    _ ≤ (4 * Real.pi)⁻¹ * ((‖x‖ ^ 3)⁻¹ * 1 +
        (3 * (‖x‖ ^ 5)⁻¹) * (‖x‖ * ‖x‖)) := by
      rw [schauderNewtonHessian, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      apply mul_le_mul_of_nonneg_left _ hc
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr3]
        exact mul_le_mul_of_nonneg_left (by
          simpa using (norm_innerSL_le ℝ (E := E₃))) hr3
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr5,
          ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    _ = _ := by
      by_cases hx : x = 0
      · simp [hx]
      have hn := norm_ne_zero_iff.mpr hx
      field_simp
      ring

lemma contDiffAt_schauderNewtonHessian {x : E₃} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) schauderNewtonHessian x := by
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E₃ => ‖y‖) x :=
    contDiffAt_id.norm ℝ hx
  have hn0 := norm_ne_zero_iff.mpr hx
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E₃ => innerSL ℝ y) x :=
    ((innerSL ℝ (E := E₃)).restrictScalars ℝ).contDiff.contDiffAt
  exact (((hn.pow 3).inv (pow_ne_zero _ hn0)).smul contDiffAt_const |>.sub
    ((contDiffAt_const.mul ((hn.pow 5).inv (pow_ne_zero _ hn0))).smul
      (hi.smulRight hi))).const_smul _

lemma schauderNewtonHessian_smul {a : ℝ} (ha : 0 < a) (x : E₃) :
    schauderNewtonHessian (a • x) = (a ^ 3)⁻¹ • schauderNewtonHessian x := by
  ext v w
  simp only [schauderNewtonHessian_apply, smul_apply, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, abs_of_pos ha, real_inner_smul_left]
  field_simp

lemma fderiv_schauderNewtonHessian_smul {a : ℝ} (ha : 0 < a)
    {x : E₃} (hx : x ≠ 0) :
    fderiv ℝ schauderNewtonHessian (a • x) =
      (a ^ 4)⁻¹ • fderiv ℝ schauderNewtonHessian x := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have hd := (contDiffAt_schauderNewtonHessian hax).differentiableAt (by simp)
  have hdx := (contDiffAt_schauderNewtonHessian hx).differentiableAt (by simp)
  have h1 := hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  have h2 := hdx.hasFDerivAt.const_smul (a ^ 3)⁻¹
  have he : schauderNewtonHessian ∘ (fun y : E₃ => a • y) =
      (a ^ 3)⁻¹ • schauderNewtonHessian :=
    funext (schauderNewtonHessian_smul ha)
  rw [he] at h1
  have hu := h1.unique h2
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] at hu
  have hh := congrArg (fun q => a⁻¹ • q) hu
  have hs : a⁻¹ * (a ^ 3)⁻¹ = (a ^ 4)⁻¹ := by field_simp
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, hs] using hh

/-- The inverse-quartic bound on the genuine derivative of the Hessian kernel.
The constant is chosen before the point; it is obtained on the unit sphere and
transported by the proved degree-minus-four homogeneity. -/
lemma exists_norm_fderiv_schauderNewtonHessian_le :
    ∃ C > 0, ∀ x : E₃, x ≠ 0 →
      ‖fderiv ℝ schauderNewtonHessian x‖ ≤ C * (‖x‖ ^ 4)⁻¹ := by
  have hc : ContinuousOn (fderiv ℝ schauderNewtonHessian) (sphere 0 1) := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    have hx0 : x ≠ 0 := by intro h; simp [h] at hn
    exact ((contDiffAt_schauderNewtonHessian hx0).fderiv_right
      (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E₃) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E₃ := ‖x‖⁻¹ • x
  have hny : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
  have hy : y ≠ 0 := by intro h; simp [h] at hny
  have hxy : ‖x‖ • y = x := by simp [y, smul_smul, hn.ne']
  have he := fderiv_schauderNewtonHessian_smul hn hy
  rw [hxy] at he
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (‖x‖ ^ 4)⁻¹ * max C 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hC y (by simpa only [mem_sphere, dist_zero_right] using hny)).trans
        (le_max_left _ _)
    _ = _ := mul_comm _ _

/-- A coordinate entry of the actual Hessian kernel. -/
def schauderNewtonHessianEntry (i j : Fin 3) (x : E₃) : ℝ :=
  schauderNewtonHessian x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

lemma schauderNewtonHessianEntry_eq (i j : Fin 3) (x : E₃) :
    schauderNewtonHessianEntry i j x = (4 * Real.pi)⁻¹ *
      ((if i = j then 1 else 0) * (‖x‖ ^ 3)⁻¹ -
        3 * (‖x‖ ^ 5)⁻¹ * x i * x j) := by
  simp only [schauderNewtonHessianEntry, schauderNewtonHessian_apply,
    EuclideanSpace.inner_single_right]
  by_cases h : i = j <;> simp [h, mul_comm]

lemma schauderNewtonHessianEntry_trace (x : E₃) :
    ∑ i : Fin 3, schauderNewtonHessianEntry i i x = 0 := by
  by_cases hx : x = 0
  · simp [hx, schauderNewtonHessianEntry_eq]
  have hn := norm_ne_zero_iff.mpr hx
  have hsq := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hsq
  simp only [Fin.sum_univ_three, schauderNewtonHessianEntry_eq, ite_true, one_mul]
  field_simp
  nlinarith

end LiquidDrop
