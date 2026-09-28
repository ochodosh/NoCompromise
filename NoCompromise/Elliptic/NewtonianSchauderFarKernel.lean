import NoCompromise.Elliptic.NewtonianSchauderSplit

/-!
# The smooth far part of the Hessian kernel

Removing an explicit radial neighborhood of the singularity gives a globally
smooth even kernel. Its derivative is odd and has integral zero. A derivative
bound with a constant independent of the cutoff scale follows from the actual
third derivative bound and the scaled cutoff estimate.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma contDiffAt_schauderNewtonHessianEntry (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (schauderNewtonHessianEntry i j) x :=
  ((contDiffAt_schauderNewtonHessian hx).clm_apply contDiffAt_const).clm_apply
    contDiffAt_const

lemma norm_fderiv_schauderNewtonHessianEntry_le (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    ‖fderiv ℝ (schauderNewtonHessianEntry i j) x‖ ≤ ‖fderiv ℝ schauderNewtonHessian x‖ := by
  have hd := (contDiffAt_schauderNewtonHessian hx).differentiableAt (by simp)
  have h := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i 1) x)).clm_apply
    (hasFDerivAt_const (EuclideanSpace.single j 1) x)
  change HasFDerivAt (schauderNewtonHessianEntry i j) _ x at h
  rw [h.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simp only [ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  have hh := (((fderiv ℝ schauderNewtonHessian x v) (EuclideanSpace.single i 1)).le_opNorm
    (EuclideanSpace.single j 1)).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ schauderNewtonHessian x v).le_opNorm
      (EuclideanSpace.single i 1)) (norm_nonneg _))
  simp only [PiLp.norm_single, norm_one, mul_one] at hh
  exact hh.trans ((fderiv ℝ schauderNewtonHessian x).le_opNorm v)

lemma schauderNewtonHessianEntry_neg (i j : Fin 3) (x : E₃) :
    schauderNewtonHessianEntry i j (-x) = schauderNewtonHessianEntry i j x := by
  simp only [schauderNewtonHessianEntry_eq, norm_neg, PiLp.neg_apply]
  ring

/-- The far Hessian kernel at positive scale `d`. -/
def schauderFarKernel (d : ℝ) (i j : Fin 3) (x : E₃) : ℝ :=
  (1 - schauderRadialCutoff d x) * schauderNewtonHessianEntry i j x

lemma schauderFarKernel_eventually_zero {d : ℝ} (hd : 0 < d) (i j : Fin 3) {x : E₃}
    (hx : ‖x‖ < d) : schauderFarKernel d i j =ᶠ[𝓝 x] 0 := by
  filter_upwards [schauderRadialCutoff_eventually_one hd hx] with y hy
  simp [schauderFarKernel, hy]

lemma contDiff_schauderFarKernel {d : ℝ} (hd : 0 < d) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (schauderFarKernel d i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (schauderFarKernel_eventually_zero hd i j (by simpa using hd))
  · exact (contDiffAt_const.sub (contDiff_schauderRadialCutoff d).contDiffAt).mul
      (contDiffAt_schauderNewtonHessianEntry i j hx)

lemma schauderFarKernel_neg (d : ℝ) (i j : Fin 3) (x : E₃) :
    schauderFarKernel d i j (-x) = schauderFarKernel d i j x := by
  simp only [schauderFarKernel, schauderRadialCutoff_neg, schauderNewtonHessianEntry_neg]

lemma fderiv_schauderFarKernel_neg {d : ℝ} (hd : 0 < d) (i j : Fin 3) (x : E₃) :
    fderiv ℝ (schauderFarKernel d i j) (-x) = -fderiv ℝ (schauderFarKernel d i j) x := by
  have hf := (contDiff_schauderFarKernel hd i j).differentiable (by simp)
  have h := (hf (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have he : schauderFarKernel d i j ∘ (fun y : E₃ => -y) = schauderFarKernel d i j :=
    funext (schauderFarKernel_neg d i j)
  rw [he] at h
  have hh : -fderiv ℝ (schauderFarKernel d i j) (-x) =
      fderiv ℝ (schauderFarKernel d i j) x := by
    simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using
      h.unique (hf x).hasFDerivAt
  exact neg_eq_iff_eq_neg.mp hh

lemma integral_fderiv_schauderFarKernel {d : ℝ} (hd : 0 < d) (i j : Fin 3) :
    (∫ x, fderiv ℝ (schauderFarKernel d i j) x) = 0 := by
  let e : E₃ ≃ₗᵢ[ℝ] E₃ := LinearIsometryEquiv.neg ℝ
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => fderiv ℝ (schauderFarKernel d i j) x)
  change (∫ x, fderiv ℝ (schauderFarKernel d i j) (-x)) = _ at h
  simp_rw [fderiv_schauderFarKernel_neg hd, integral_neg] at h
  have hzero : (2 : ℝ) • (∫ x, fderiv ℝ (schauderFarKernel d i j) x) = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact h
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

lemma fderiv_schauderFarKernel_zero {d : ℝ} (hd : 0 < d) (i j : Fin 3) {x : E₃}
    (hx : ‖x‖ < d) : fderiv ℝ (schauderFarKernel d i j) x = 0 := by
  rw [(schauderFarKernel_eventually_zero hd i j hx).fderiv_eq]
  exact fderiv_const_apply (0 : ℝ)

/-- The far-kernel derivative has the inverse-quartic size bound with a single
constant valid for every positive cutoff scale and every coordinate entry. -/
lemma exists_norm_fderiv_schauderFarKernel_le :
    ∃ C > 0, ∀ d > 0, ∀ (i j : Fin 3) (x : E₃), x ≠ 0 →
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ ≤ C * (‖x‖ ^ 4)⁻¹ := by
  obtain ⟨A, hA, hAb⟩ := exists_norm_fderiv_schauderNewtonHessian_le
  obtain ⟨B, hB, hBb⟩ := exists_schauderRadialCutoff_derivative_bound
  refine ⟨A + 2 * B * Real.pi⁻¹, by positivity, fun d hd i j x hx => ?_⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : ‖fderiv ℝ (schauderRadialCutoff d) x‖ ≤ 2 * B / ‖x‖ := by
    by_cases hxd : ‖x‖ ≤ 2 * d
    · apply (hBb d hd x).trans
      apply (div_le_div_iff₀ hd hn).mpr
      nlinarith
    · rw [fderiv_schauderRadialCutoff_zero_outside hd (lt_of_not_ge hxd), norm_zero]
      positivity
  have hf := (contDiff_schauderRadialCutoff d).differentiable (by simp) x
  have hk := (contDiffAt_schauderNewtonHessianEntry i j hx).differentiableAt (by simp)
  have h := ((hasFDerivAt_const (1 : ℝ) x).sub hf.hasFDerivAt).mul hk.hasFDerivAt
  change HasFDerivAt (schauderFarKernel d i j) _ x at h
  have hm := schauderRadialCutoff_mem_Icc d x
  have h1 : ‖1 - schauderRadialCutoff d x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hm.2)]
    linarith [hm.1]
  rw [h.fderiv, zero_sub]
  calc
    _ ≤ ‖1 - schauderRadialCutoff d x‖ * ‖fderiv ℝ (schauderNewtonHessianEntry i j) x‖ +
        ‖schauderNewtonHessianEntry i j x‖ * ‖fderiv ℝ (schauderRadialCutoff d) x‖ := by
      apply (norm_add_le _ _).trans
      simp only [norm_smul, norm_neg, Pi.sub_apply]
      exact le_rfl
    _ ≤ 1 * (A * (‖x‖ ^ 4)⁻¹) + (Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹) * (2 * B / ‖x‖) := by
      apply add_le_add
      · exact mul_le_mul h1 ((norm_fderiv_schauderNewtonHessianEntry_le i j hx).trans
          (hAb x hx)) (norm_nonneg _) (by norm_num)
      · exact mul_le_mul (norm_schauderNewtonHessianEntry_le i j x) hc
          (norm_nonneg _) (by positivity)
    _ = _ := by
      field_simp

/-- The far derivative is absolutely integrable even after multiplication by the
Hölder weight. The radius `d / 2` keeps the majorant away from the origin. -/
lemma schauder_far_derivative_weighted_bound {α d C : ℝ}
    (hα : 0 ≤ α) (hα1 : α < 1) (hd : 0 < d) (_hC : 0 ≤ C)
    (i j : Fin 3)
    (hb : ∀ x : E₃, x ≠ 0 →
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ ≤ C * (‖x‖ ^ 4)⁻¹) :
    Integrable (fun x : E₃ => ‖fderiv ℝ (schauderFarKernel d i j) x‖ * ‖x‖ ^ α) ∧
    (∫ x : E₃, ‖fderiv ℝ (schauderFarKernel d i j) x‖ * ‖x‖ ^ α) ≤
      C * (4 * Real.pi * (d / 2) ^ (α - 1) / (1 - α)) := by
  let S : Set E₃ := {x | d / 2 < ‖x‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hi : Integrable (S.indicator (fun x : E₃ => C * ‖x‖ ^ (α - 4))) :=
    (integrable_indicator_iff hS).mpr
      ((integrableOn_schauder_far_power hα1 (by positivity : 0 < d / 2)).const_mul C)
  have hc : Continuous (fun x : E₃ =>
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ * ‖x‖ ^ α) :=
    ((contDiff_schauderFarKernel hd i j).continuous_fderiv (by simp)).norm.mul
      ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hmaj : ∀ x : E₃,
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ * ‖x‖ ^ α ≤
        S.indicator (fun x : E₃ => C * ‖x‖ ^ (α - 4)) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hn : 0 < ‖x‖ := (by positivity : 0 < d / 2).trans hx
      calc
        _ ≤ (C * (‖x‖ ^ 4)⁻¹) * ‖x‖ ^ α :=
          mul_le_mul_of_nonneg_right (hb x (norm_pos_iff.mp hn)) (by positivity)
        _ = _ := by
          rw [Real.rpow_sub hn α 4, Real.rpow_ofNat]
          ring
    · rw [indicator_of_notMem hx]
      have hn : ‖x‖ < d := by
        have hx' : ‖x‖ ≤ d / 2 := not_lt.mp hx
        linarith
      rw [fderiv_schauderFarKernel_zero hd i j hn, norm_zero, zero_mul]
  have hij : Integrable (fun x : E₃ =>
      ‖fderiv ℝ (schauderFarKernel d i j) x‖ * ‖x‖ ^ α) := by
    apply hi.mono' hc.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hmaj x)
  refine ⟨hij, (integral_mono hij hi hmaj).trans_eq ?_⟩
  rw [integral_indicator hS, integral_const_mul,
    integral_schauder_far_power hα1 (by positivity : 0 < d / 2)]

lemma integrable_fderiv_schauderFarKernel {d : ℝ} (hd : 0 < d) (i j : Fin 3) :
    Integrable (fderiv ℝ (schauderFarKernel d i j)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_schauderFarKernel_le
  have hi := (schauder_far_derivative_weighted_bound (α := 0) (by norm_num)
    (by norm_num) hd hC.le i j (hb d hd i j)).1
  simp only [Real.rpow_zero, mul_one] at hi
  exact (integrable_norm_iff
    ((contDiff_schauderFarKernel hd i j).continuous_fderiv (by simp)).aestronglyMeasurable).mp hi

end LiquidDrop
