import NoCompromise.BV.StrictApprox

/-!
# Bounded indicator mollification and weighted convergence

Normalized nonnegative bumps preserve the indicator's unit bound. Lebesgue
differentiation and dominated convergence give convergence against every L¹ weight.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Convolution
namespace LiquidDrop

lemma norm_indicator_bump_convolution_le
    (φ : ContDiffBump (0 : AmbientSpace)) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (x : AmbientSpace) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      E.indicator (fun _ => (1 : ℝ))) x‖ ≤ 1 := by
  have hm := (locallyIntegrable_indicator_one hE).aestronglyMeasurable
  simpa only [dist_zero_right] using dist_convolution_le (μ := volume)
    (g := E.indicator (fun _ => (1 : ℝ))) (x₀ := x) (z₀ := (0 : ℝ)) zero_le_one
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hm
    (fun y _ => by by_cases hy : y ∈ E <;> simp [hy])

/-- Indicator mollifications converge against every integrable real weight. -/
theorem tendsto_integral_indicator_bump_convolution_mul
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0)) {C : ℝ}
    (hratio : ∀ᶠ j in atTop, (φ j).rOut ≤ C * (φ j).rIn)
    {q : AmbientSpace → ℝ} (hq : Integrable q) :
    Tendsto (fun j => ∫ x,
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        E.indicator (fun _ => (1 : ℝ))) x * q x) atTop (𝓝 (∫ x in E, q x)) := by
  have hf := locallyIntegrable_indicator_one hE
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hratio hf
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖q x‖)
    (fun j => (((φ j).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ j).continuous_normed hf).aestronglyMeasurable.mul
      hq.aestronglyMeasurable) hq.norm
    (fun j => Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_indicator_bump_convolution_le (φ j) hE x)
        (norm_nonneg _)).trans_eq (one_mul _))
    (hae.mono fun x hx => hx.mul_const (q x))
  have heq : (fun x => E.indicator (fun _ => (1 : ℝ)) x * q x) = E.indicator q := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  simpa only [Pi.mul_apply, heq, integral_indicator₀ hE] using! ht

end LiquidDrop
