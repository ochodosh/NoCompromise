module

public import NoCompromise.Elliptic.NewtonianSchauderFarKernel

@[expose] public section

/-!
# Far-field convolution estimates

The source is merely integrable. Differentiation acts on the smooth far kernel,
whose derivative is bounded and integrable. Its zero integral then replaces the
source by its Hölder increment, giving the scale `d^(α - 1)` without assuming
that the source itself is differentiable.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma norm_schauderFarKernel_le {d : ℝ} (hd : 0 < d) (i j : Fin 3) (x : E₃) :
    ‖schauderFarKernel d i j x‖ ≤ Real.pi⁻¹ * (d ^ 3)⁻¹ := by
  by_cases hx : ‖x‖ ≤ d
  · simp only [schauderFarKernel, schauderRadialCutoff_one hd hx,
      sub_self, zero_mul, norm_zero]
    positivity
  have hn : d < ‖x‖ := lt_of_not_ge hx
  have hm := schauderRadialCutoff_mem_Icc d x
  have h1 : ‖1 - schauderRadialCutoff d x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hm.2)]
    linarith [hm.1]
  calc
    _ ≤ 1 * (Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹) := by
      rw [schauderFarKernel, norm_mul]
      exact mul_le_mul h1 (norm_schauderNewtonHessianEntry_le i j x)
        (norm_nonneg _) (by norm_num)
    _ ≤ _ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (pow_le_pow_left₀ hd.le hn.le 3)) (by positivity)

lemma norm_fderiv_schauderFarKernel_le_uniform {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (i j : Fin 3)
    (hb : ∀ x : E₃, x ≠ 0 →
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ ≤ C * (‖x‖ ^ 4)⁻¹) (x : E₃) :
    ‖fderiv ℝ (schauderFarKernel d i j) x‖ ≤ C * (d ^ 4)⁻¹ := by
  by_cases hx : ‖x‖ < d
  · rw [fderiv_schauderFarKernel_zero hd i j hx, norm_zero]
    positivity
  have hn : d ≤ ‖x‖ := not_lt.mp hx
  apply (hb x (norm_pos_iff.mp (hd.trans_le hn))).trans
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (by positivity) (pow_le_pow_left₀ hd.le hn 4)) hC

/-- Convolution with the actual smooth far Hessian entry. -/
def schauderFarConvolution (d : ℝ) (i j : Fin 3) (f : E₃ → ℝ) (x : E₃) : ℝ :=
  ∫ y, f y * schauderFarKernel d i j (x - y)

lemma integrable_schauderFarConvolution {d : ℝ} (hd : 0 < d) (i j : Fin 3)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun y => f y * schauderFarKernel d i j (x - y)) := by
  apply (hf.norm.mul_const (Real.pi⁻¹ * (d ^ 3)⁻¹)).mono'
    (hf.aestronglyMeasurable.mul (((contDiff_schauderFarKernel hd i j).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable))
  exact Eventually.of_forall fun y => by
    change ‖f y * schauderFarKernel d i j (x - y)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_schauderFarKernel_le hd i j (x - y)) (norm_nonneg _)

lemma integrable_schauderFarConvolution_derivative {d : ℝ} (hd : 0 < d) (i j : Fin 3)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun y => f y • fderiv ℝ (schauderFarKernel d i j) (x - y)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_schauderFarKernel_le
  apply (hf.norm.mul_const (C * (d ^ 4)⁻¹)).mono'
    (hf.aestronglyMeasurable.smul
      ((((contDiff_schauderFarKernel hd i j).continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable))
  exact Eventually.of_forall fun y => by
    change ‖f y • fderiv ℝ (schauderFarKernel d i j) (x - y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (norm_fderiv_schauderFarKernel_le_uniform hd hC.le i j (hb d hd i j) (x - y))
      (norm_nonneg _)

lemma hasFDerivAt_schauderFarConvolution {d : ℝ} (hd : 0 < d) (i j : Fin 3)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    HasFDerivAt (schauderFarConvolution d i j f)
      (∫ y, f y • fderiv ℝ (schauderFarKernel d i j) (x - y)) x := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_schauderFarKernel_le
  unfold schauderFarConvolution
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun a y => f y • fderiv ℝ (schauderFarKernel d i j) (a - y))
    (bound := fun y => ‖f y‖ * (C * (d ^ 4)⁻¹)) univ_mem
  · exact Eventually.of_forall fun a =>
      (integrable_schauderFarConvolution hd i j hf a).aestronglyMeasurable
  · exact integrable_schauderFarConvolution hd i j hf x
  · exact (integrable_schauderFarConvolution_derivative hd i j hf x).aestronglyMeasurable
  · exact Eventually.of_forall fun y a _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (norm_fderiv_schauderFarKernel_le_uniform hd hC.le i j (hb d hd i j) (a - y))
        (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact Eventually.of_forall fun y a _ => by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (((contDiff_schauderFarKernel hd i j).differentiable (by simp) (a - y)).hasFDerivAt.comp
          a ((hasFDerivAt_id a).sub_const y)).const_mul (f y)

lemma integrable_schauderFarConvolution_derivative_sub {d : ℝ} (hd : 0 < d)
    (i j : Fin 3) {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun z => (f (x - z) - f x) • fderiv ℝ (schauderFarKernel d i j) z) := by
  have hi : Integrable (fun z => f (x - z) • fderiv ℝ (schauderFarKernel d i j) z) := by
    have h := (integrable_comp_sub_left
      (fun y => f y • fderiv ℝ (schauderFarKernel d i j) (x - y)) x).mpr
        (integrable_schauderFarConvolution_derivative hd i j hf x)
    simpa only [sub_sub_cancel] using h
  have hic : Integrable (fun z => f x • fderiv ℝ (schauderFarKernel d i j) z) :=
    (integrable_fderiv_schauderFarKernel hd i j).smul (f x)
  exact (hi.sub hic).congr (Eventually.of_forall fun z => (sub_smul _ _ _).symm)

/-- Cancellation of the genuinely integrable far-kernel derivative removes the
source value. No derivative of the source is required. -/
lemma fderiv_schauderFarConvolution_eq_sub {d : ℝ} (hd : 0 < d)
    (i j : Fin 3) {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    fderiv ℝ (schauderFarConvolution d i j f) x =
      ∫ z, (f (x - z) - f x) • fderiv ℝ (schauderFarKernel d i j) z := by
  have hi : Integrable (fun z => f (x - z) • fderiv ℝ (schauderFarKernel d i j) z) := by
    have h := (integrable_comp_sub_left
      (fun y => f y • fderiv ℝ (schauderFarKernel d i j) (x - y)) x).mpr
        (integrable_schauderFarConvolution_derivative hd i j hf x)
    simpa only [sub_sub_cancel] using h
  have he := integral_sub_left_eq_self
    (fun y => f y • fderiv ℝ (schauderFarKernel d i j) (x - y)) volume x
  simp only [sub_sub_cancel] at he
  rw [(hasFDerivAt_schauderFarConvolution hd i j hf x).fderiv, ← he]
  simp_rw [sub_smul]
  have hic : Integrable (fun z => f x • fderiv ℝ (schauderFarKernel d i j) z) :=
    (integrable_fderiv_schauderFarKernel hd i j).smul (f x)
  rw [integral_sub hi hic, integral_smul, integral_fderiv_schauderFarKernel hd,
    smul_zero, sub_zero]

/-- A universal constant controls the far-field derivative for every Hölder
exponent in `(0,1)`, cutoff scale, integrable source and Hölder increment bound. -/
lemma exists_schauderFarConvolution_derivative_bound :
    ∃ C > 0, ∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ d > 0, ∀ A ≥ 0,
      ∀ (f : E₃ → ℝ), Integrable f →
      (∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) →
      ∀ (i j : Fin 3) (x : E₃),
        ‖fderiv ℝ (schauderFarConvolution d i j f) x‖ ≤
          C * A * (d / 2) ^ (α - 1) / (1 - α) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_schauderFarKernel_le
  refine ⟨C * (4 * Real.pi), by positivity, fun α hα hα1 d hd A hA f hf hinc i j x => ?_⟩
  obtain ⟨hi, hbound⟩ := schauder_far_derivative_weighted_bound hα hα1 hd hC.le
    i j (hb d hd i j)
  have hi' := integrable_schauderFarConvolution_derivative_sub hd i j hf x
  have hmaj : ∀ z : E₃,
      ‖(f (x - z) - f x) • fderiv ℝ (schauderFarKernel d i j) z‖ ≤
        A * (‖fderiv ℝ (schauderFarKernel d i j) z‖ * ‖z‖ ^ α) := by
    intro z
    have hz := hinc (x - z) x
    rw [show x - z - x = -z by abel, norm_neg] at hz
    rw [norm_smul]
    calc
      _ ≤ (A * ‖z‖ ^ α) * ‖fderiv ℝ (schauderFarKernel d i j) z‖ :=
        mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = _ := by ring
  rw [fderiv_schauderFarConvolution_eq_sub hd i j hf x]
  calc
    _ ≤ ∫ z, ‖(f (x - z) - f x) • fderiv ℝ (schauderFarKernel d i j) z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, A * (‖fderiv ℝ (schauderFarKernel d i j) z‖ * ‖z‖ ^ α) :=
      integral_mono hi'.norm (hi.const_mul A) hmaj
    _ = A * (∫ z, ‖fderiv ℝ (schauderFarKernel d i j) z‖ * ‖z‖ ^ α) :=
      integral_const_mul _ _
    _ ≤ A * (C * (4 * Real.pi * (d / 2) ^ (α - 1) / (1 - α))) :=
      mul_le_mul_of_nonneg_left hbound hA
    _ = _ := by ring

lemma exists_schauderFarConvolution_increment_bound :
    ∃ C > 0, ∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ d > 0, ∀ A ≥ 0,
      ∀ (f : E₃ → ℝ), Integrable f →
      (∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) →
      ∀ (i j : Fin 3) (x y : E₃),
        ‖schauderFarConvolution d i j f x - schauderFarConvolution d i j f y‖ ≤
          (C * A * (d / 2) ^ (α - 1) / (1 - α)) * ‖x - y‖ := by
  obtain ⟨C, hC, hb⟩ := exists_schauderFarConvolution_derivative_bound
  refine ⟨C, hC, fun α hα hα1 d hd A hA f hf hinc i j x y => ?_⟩
  exact (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hasFDerivAt_schauderFarConvolution hd i j hf z).differentiableAt)
    (fun z _ => hb α hα hα1 d hd A hA f hf hinc i j z) (mem_univ y) (mem_univ x)

end LiquidDrop
