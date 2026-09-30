module

public import NoCompromise.Elliptic.NewtonianSchauderIntegrals
public import NoCompromise.Elliptic.HolderInterpolationNorm

@[expose] public section

/-!
# Size and difference estimates for the Newtonian Hessian

These are bounds for the actual kernel. In particular the far-field estimate
follows from its proved third derivative bound and the mean-value theorem on a
ball that avoids the singularity.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma schauder_norm_sub_le_holder {α : ℝ} {f : E₃ → ℝ} {U : Set E₃}
    (hf : HasFiniteHolderNormOn α f U) {x y : E₃} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≠ y) :
    ‖f x - f y‖ ≤ holderSeminorm α f U * ‖x - y‖ ^ α := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hq : ‖f x - f y‖ / ‖x - y‖ ^ α ≤ holderSeminorm α f U := by
    apply le_csSup hf.seminorm_bounded
    exact mem_insert_of_mem 0 ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hn α)).mp hq

/-- A genuine mean-value estimate away from the singularity. -/
lemma exists_schauderNewtonHessian_sub_le :
    ∃ C > 0, ∀ x z : E₃, x ≠ 0 → ‖z‖ ≤ ‖x‖ / 2 →
      ‖schauderNewtonHessian (x - z) - schauderNewtonHessian x‖ ≤
        C * ‖z‖ * (‖x‖ ^ 4)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_fderiv_schauderNewtonHessian_le
  refine ⟨16 * C, by positivity, fun x z hx hz => ?_⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlow : ∀ y ∈ closedBall x (‖x‖ / 2), ‖x‖ / 2 ≤ ‖y‖ := by
    intro y hy
    have hy' : ‖x - y‖ ≤ ‖x‖ / 2 := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
    have htri := norm_le_norm_sub_add x y
    linarith
  have hnz : ∀ y ∈ closedBall x (‖x‖ / 2), y ≠ 0 := by
    intro y hy
    exact norm_pos_iff.mp ((half_pos hn).trans_le (hlow y hy))
  have hd : ∀ y ∈ closedBall x (‖x‖ / 2),
      DifferentiableAt ℝ schauderNewtonHessian y := by
    intro y hy
    exact (contDiffAt_schauderNewtonHessian (hnz y hy)).differentiableAt (by simp)
  have hb : ∀ y ∈ closedBall x (‖x‖ / 2),
      ‖fderiv ℝ schauderNewtonHessian y‖ ≤ C * ((‖x‖ / 2) ^ 4)⁻¹ := by
    intro y hy
    apply (hbound y (hnz y hy)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply inv_anti₀ (pow_pos (half_pos hn) _)
    exact pow_le_pow_left₀ (half_pos hn).le (hlow y hy) 4
  have hh := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le hd hb
    (mem_closedBall_self (half_pos hn).le)
    (show x - z ∈ closedBall x (‖x‖ / 2) by
      simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hz)
  have he : C * ((‖x‖ / 2) ^ 4)⁻¹ * ‖x - z - x‖ =
      16 * C * ‖z‖ * (‖x‖ ^ 4)⁻¹ := by
    rw [sub_sub_cancel_left, norm_neg]
    field_simp
    ring
  rwa [he] at hh

lemma measurable_schauderNewtonHessianEntry (i j : Fin 3) :
    Measurable (schauderNewtonHessianEntry i j) := by
  have he : schauderNewtonHessianEntry i j = fun x : E₃ => (4 * Real.pi)⁻¹ *
      ((if i = j then 1 else 0) * (‖x‖ ^ 3)⁻¹ -
        3 * (‖x‖ ^ 5)⁻¹ * x i * x j) :=
    funext (schauderNewtonHessianEntry_eq i j)
  rw [he]
  fun_prop

lemma norm_schauderNewtonHessianEntry_le (i j : Fin 3) (x : E₃) :
    ‖schauderNewtonHessianEntry i j x‖ ≤ Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ := by
  have h := ((schauderNewtonHessian x (EuclideanSpace.single i 1)).le_opNorm
    (EuclideanSpace.single j 1)).trans
    (mul_le_mul_of_nonneg_right ((schauderNewtonHessian x).le_opNorm
      (EuclideanSpace.single i 1)) (norm_nonneg _))
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (norm_schauderNewtonHessian_le x)

lemma schauder_continuousOn_of_finiteHolder {α : ℝ} (hα : 0 < α)
    {f : E₃ → ℝ} {U : Set E₃} (hf : HasFiniteHolderNormOn α f U) :
    ContinuousOn f U := by
  intro x hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun y : E₃ => holderSeminorm α f U * ‖y - x‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.sub continuous_const).norm)
  have ht : Tendsto (fun y : E₃ => holderSeminorm α f U * ‖y - x‖ ^ α)
      (𝓝[U] x) (𝓝 0) := by
    have ht0 : Tendsto (fun y : E₃ => holderSeminorm α f U * ‖y - x‖ ^ α)
        (𝓝 x) (𝓝 0) := by
      simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
    exact ht0.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun y => norm_nonneg (f y - f x))) _ ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  by_cases hyx : y = x
  · simp [hyx, Real.zero_rpow hα.ne']
  · exact schauder_norm_sub_le_holder hf hy hx hyx

/-- Absolute convergence and a quantitative near-field bound after subtracting
the source value. Only actual pointwise Hölder increments on this ball are used. -/
lemma schauder_near_integral_entry_bound {α R A : ℝ} (hα : 0 < α)
    (hR : 0 ≤ R) (hA : 0 ≤ A) {f : E₃ → ℝ} (hf : Measurable f)
    (x : E₃) (i j : Fin 3)
    (hinc : ∀ z ∈ ball (0 : E₃) R, ‖f (x - z) - f x‖ ≤ A * ‖z‖ ^ α) :
    IntegrableOn (fun z => schauderNewtonHessianEntry i j z * (f (x - z) - f x))
      (ball 0 R) ∧
    ‖∫ z in ball (0 : E₃) R,
      schauderNewtonHessianEntry i j z * (f (x - z) - f x)‖ ≤
        4 * A * R ^ α / α := by
  have hC : 0 ≤ Real.pi⁻¹ * A := by positivity
  have hb := (integrableOn_schauder_near_power (R := R) hα).const_mul (Real.pi⁻¹ * A)
  have hm : Measurable (fun z =>
      schauderNewtonHessianEntry i j z * (f (x - z) - f x)) :=
    (measurable_schauderNewtonHessianEntry i j).mul
      ((hf.comp (continuous_const.sub continuous_id).measurable).sub measurable_const)
  have hbound : ∀ z ∈ ball (0 : E₃) R,
      ‖schauderNewtonHessianEntry i j z * (f (x - z) - f x)‖ ≤
        (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      simp only [sub_zero, sub_self, mul_zero, norm_zero]
      positivity
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    calc
      _ ≤ (Real.pi⁻¹ * (‖z‖ ^ 3)⁻¹) * (A * ‖z‖ ^ α) := by
        rw [norm_mul]
        exact mul_le_mul (norm_schauderNewtonHessianEntry_le i j z)
          (hinc z hz) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [Real.rpow_sub hn α 3, Real.rpow_ofNat]
        ring
  have hae : ∀ᵐ z ∂volume.restrict (ball (0 : E₃) R),
      ‖schauderNewtonHessianEntry i j z * (f (x - z) - f x)‖ ≤
        (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hbound z hz
  have hi := hb.mono' hm.aestronglyMeasurable.restrict hae
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z in ball (0 : E₃) R,
        ‖schauderNewtonHessianEntry i j z * (f (x - z) - f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0 : E₃) R, (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3) :=
      integral_mono_ae hi.norm hb hae
    _ = _ := by
      rw [integral_const_mul, integral_schauder_near_power hα hR]
      field_simp

end LiquidDrop
