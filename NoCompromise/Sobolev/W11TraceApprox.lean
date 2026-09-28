import NoCompromise.Sobolev.W11TraceFlat
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Strong L¹ approximation and the weak flat trace

The normal-average trace is stable under strong L¹ convergence of a function
and its weak gradient. Smooth mollification identifies it with the boundary
restriction whenever the original representative is continuous.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma flatTraceFunction_sub_ae_of_integrable {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : Integrable f) (hG : Integrable G) (hh : Integrable h) (hH : Integrable H) :
    flatTraceFunction (f - h) (G - H) =ᵐ[volume]
      flatTraceFunction f G - flatTraceFunction h H := by
  filter_upwards [(integrable_flatTraceIntegrand hf hG).1.prod_right_ae,
    (integrable_flatTraceIntegrand hh hH).1.prod_right_ae] with x hx hy
  have heq : (fun t => flatTraceIntegrand (f - h) (G - H) (x, t)) =
      fun t => flatTraceIntegrand f G (x, t) - flatTraceIntegrand h H (x, t) := by
    funext t
    simp only [flatTraceIntegrand, Pi.sub_apply, PiLp.sub_apply]
    ring
  change (∫ t, flatTraceIntegrand (f - h) (G - H) (x, t) ∂flatTraceInterval) = _
  rw [heq, integral_sub hx hy]
  rfl

theorem integral_norm_flatTraceFunction_sub_le {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : Integrable f) (hG : Integrable G) (hh : Integrable h) (hH : Integrable H) :
    (∫ x, ‖flatTraceFunction f G x - flatTraceFunction h H x‖) ≤
      (∫ x, ‖f x - h x‖) + ∫ x, ‖G x - H x‖ := by
  have heq := flatTraceFunction_sub_ae_of_integrable hf hG hh hH
  calc
    _ = ∫ x, ‖flatTraceFunction (f - h) (G - H) x‖ :=
      integral_congr_ae (heq.symm.mono fun _ hx => congrArg norm hx)
    _ ≤ _ := (integrable_flatTraceFunction (hf.sub hh) (hG.sub hH)).2

theorem tendsto_integral_norm_flatTraceFunction {k : ℕ} {ι : Type*} {l : Filter ι}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {f' : ι → EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G' : ι → EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : Integrable f) (hG : Integrable G)
    (hf' : ∀ j, Integrable (f' j)) (hG' : ∀ j, Integrable (G' j))
    (hcf : Tendsto (fun j => ∫ x, ‖f' j x - f x‖) l (𝓝 0))
    (hcG : Tendsto (fun j => ∫ x, ‖G' j x - G x‖) l (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖flatTraceFunction (f' j) (G' j) x - flatTraceFunction f G x‖)
      l (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun j => integral_norm_flatTraceFunction_sub_le (hf' j) (hG' j) hf hG)
  simpa only [zero_add] using hcf.add hcG

theorem HasW11GradientOn.tendsto_flatTrace_bump_convolution {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasW11GradientOn f G univ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1)))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) (graphAppendN x 0) -
        flatTraceFunction f G x‖) l (𝓝 0) := by
  have hif : Integrable f := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_function
  have hiG : Integrable G := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_gradient
  have hconv := tendsto_integral_norm_flatTraceFunction hif hiG
    (fun j => (φ j).integrable_normed.integrable_convolution _ hif)
    (fun j => (φ j).integrable_normed.integrable_convolution _ hiG)
    (tendsto_integral_norm_bump_convolution_sub hif hφ)
    (tendsto_integral_norm_bump_convolution_sub hiG hφ)
  convert hconv using 1
  funext j
  congr 1
  funext x
  have hgrad := hf.toHasWeakGradientOn.gradient_convolution
    (show ContDiff ℝ 1 ((φ j).normed volume) from (φ j).contDiff_normed)
        (φ j).hasCompactSupport_normed
  have hsm : ContDiff ℝ 1 ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      hif.locallyIntegrable
  rw [← funext hgrad, flatTraceFunction_eq_restrict_of_contDiff hsm]

theorem flatTraceFunction_eq_restrict_ae_of_continuous_w11 {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasW11GradientOn f G univ) (hc : Continuous f) :
    flatTraceFunction f G =ᵐ[volume] (fun x => f (graphAppendN x 0)) := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1))) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) :=
    ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) (graphAppendN x 0)
  have hif : Integrable f := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_function
  have hiG : Integrable G := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_gradient
  have ht := (integrable_flatTraceFunction hif hiG).1
  have hv (j : ℕ) : Integrable (v j) := by
    have hgrad := hf.toHasWeakGradientOn.gradient_convolution
      (show ContDiff ℝ 1 ((φ j).normed volume) from (φ j).contDiff_normed)
        (φ j).hasCompactSupport_normed
    have hsm : ContDiff ℝ 1 ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) :=
      (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
        hif.locallyIntegrable
    apply (integrable_restrict_plane_of_contDiff_w11 hsm
      ((φ j).integrable_normed.integrable_convolution _ hif) ?_).1
    rw [funext hgrad]
    exact (φ j).integrable_normed.integrable_convolution _ hiG
  have hnorm : Tendsto (fun j => ∫ x, ‖v j x - flatTraceFunction f G x‖)
      atTop (𝓝 0) := hf.tendsto_flatTrace_bump_convolution hφ
  have hel : Tendsto (fun j => eLpNorm (v j - flatTraceFunction f G) 1 volume)
      atTop (𝓝 0) := by
    have hh := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
    have heq (j) : eLpNorm (v j - flatTraceFunction f G) 1 volume =
        ENNReal.ofReal (∫ x, ‖v j x - flatTraceFunction f G x‖) := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hv j).sub ht).1,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hv j).sub ht)]
      rfl
    simp_rw [heq]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using hh
  have him := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hel
  obtain ⟨s, hs, hsae⟩ := him.exists_seq_tendsto_ae
  filter_upwards [hsae] with x hx
  have hpoint := (ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) hφ hc
      (graphAppendN x 0)).comp hs.tendsto_atTop
  exact tendsto_nhds_unique hx hpoint

end LiquidDrop
