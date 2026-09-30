module

public import NoCompromise.BV.StrictApprox
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Differentiating compact tests along the dilation flow

All derivatives below are classical derivatives of actual test integrals.
Compact support supplies a common finite-volume dominating set on each bounded
time interval. The measurable set in the integration region needs no regularity.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tangent_divergence_radial {φ : AmbientSpace → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : AmbientSpace) :
    divergenceN (fun y => φ y • y) x = 3 * φ x + fderiv ℝ φ x x := by
  have hs : divergenceN (fun y => φ y • y) x =
      φ x * divergenceN (id : AmbientSpace → AmbientSpace) x +
        inner ℝ (gradient φ x) x := by
    simpa only [id_eq] using! (divergenceN_smul hφ contDiff_id x)
  rw [hs, inner_gradient_left]
  have hi : divergenceN (id : AmbientSpace → AmbientSpace) x = 3 := by
    simp [divergenceN]
  rw [hi]
  ring

lemma tangent_hasDerivAt_dilation_test {φ : AmbientSpace → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (y : AmbientSpace) :
    HasDerivAt (fun s : ℝ => Real.exp (3 * s) * φ (Real.exp s • y))
      (Real.exp (3 * t) * divergenceN (fun z => φ z • z) (Real.exp t • y)) t := by
  have hv := (Real.hasDerivAt_exp t).smul_const y
  have hψ := (hφ.differentiable one_ne_zero (Real.exp t • y)).hasFDerivAt.comp_hasDerivAt t hv
  have he := ((hasDerivAt_id t).const_mul 3).exp
  convert! he.mul hψ using 1
  rw [tangent_divergence_radial hφ]
  simp only [mul_one, id_eq, Function.comp_apply]
  ring

/-- Differentiation of the actual dilated test integral over an arbitrary set. -/
theorem tangent_hasDerivAt_dilation_integral (F : Set AmbientSpace)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y in F, Real.exp (3 * s) * φ (Real.exp s • y))
      (∫ y in F, Real.exp (3 * t) * divergenceN (fun z => φ z • z) (Real.exp t • y)) t := by
  let X : AmbientSpace → AmbientSpace := fun y => φ y • y
  have hX : ContDiff ℝ 1 X := by fun_prop
  let D : ℝ → AmbientSpace → ℝ := fun s y => Real.exp (3 * s) * divergenceN X (Real.exp s • y)
  have hD : Continuous (fun p : ℝ × AmbientSpace => D p.1 p.2) := by
    have hv := continuous_divergenceN hX
    dsimp [D]
    fun_prop
  obtain ⟨R, hR, hsupp⟩ := hcφ.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  let K : Set AmbientSpace := closedBall 0 (R / Real.exp (t - 1))
  have hK : IsCompact K := isCompact_closedBall _ _
  have hz (s : ℝ) (hs : s ∈ Icc (t - 1) (t + 1)) (y : AmbientSpace) (hy : y ∉ K) :
      D s y = 0 := by
    have hyn : R / Real.exp (t - 1) < ‖y‖ := by
      simpa only [K, mem_closedBall, dist_zero_right, not_le] using hy
    have he : Real.exp (t - 1) ≤ Real.exp s := Real.exp_le_exp.mpr hs.1
    have hout : Real.exp s • y ∉ tsupport φ := by
      intro hyφ
      have hnorm := hsupp hyφ
      simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos s)] at hnorm
      have hmul := (div_lt_iff₀ (Real.exp_pos (t - 1))).mp hyn
      have he' := mul_le_mul_of_nonneg_right he (norm_nonneg y)
      nlinarith
    have houtX : Real.exp s • y ∉ tsupport X := fun hh =>
      hout (tsupport_smul_subset_left φ (id : AmbientSpace → AmbientSpace) hh)
    simp only [D, divergenceN_eq_zero_of_notMem_tsupport houtX, mul_zero]
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hD.continuousOn
  let bound : AmbientSpace → ℝ := K.indicator (fun _ => max B 0)
  have hbound : ∀ᵐ y ∂volume.restrict F, ∀ s ∈ Icc (t - 1) (t + 1), ‖D s y‖ ≤ bound y := by
    apply Eventually.of_forall
    intro y s hs
    by_cases hy : y ∈ K
    · rw [show bound y = max B 0 from indicator_of_mem hy _]
      exact (hB (s, y) ⟨hs, hy⟩).trans (le_max_left _ _)
    · rw [hz s hs y hy]
      simp [bound, hy]
  have hib : Integrable bound (volume.restrict F) := by
    apply (integrable_indicator_iff hK.measurableSet).mpr
    exact integrableOn_const hK.measure_lt_top.ne
  have hi : Integrable (fun y => Real.exp (3 * t) * φ (Real.exp t • y)) (volume.restrict F) := by
    have hcomp : HasCompactSupport (fun y => φ (Real.exp t • y)) :=
      hcφ.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp t) (Real.exp_pos t).ne')
    exact (Continuous.integrable_of_hasCompactSupport (by fun_prop) hcomp.mul_left).integrableOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Eventually.of_forall (fun s => (show Continuous
      (fun y : AmbientSpace => Real.exp (3 * s) * φ (Real.exp s • y)) by
        fun_prop).aestronglyMeasurable))
    hi ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hbound hib (Eventually.of_forall fun y s _ => tangent_hasDerivAt_dilation_test hφ s y)
  exact hd.2

end LiquidDrop
