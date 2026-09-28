import NoCompromise.DeGiorgi.PolarDifferentiation
import NoCompromise.BV.StrictApprox
import NoCompromise.Measure.ConvolutionPairing

/-!
# Mollification of the actual ambient perimeter derivative

Differentiating a compact smooth kernel and using the coordinate distributional
pairings identifies the mollified gradient with convolution of the full vector
polar density. No constant-normal or finite-total-perimeter hypothesis is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

/-- Exact vector-valued convolution of the distributional perimeter derivative. -/
theorem IsAmbientOutwardPerimeterPolar.gradient_convolution_eq
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    {k : AmbientSpace → ℝ} (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : AmbientSpace) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) x =
      -(∫ y, k (x - y) • ν y ∂μ) := by
  let φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun y => k (x - y), hk.continuous.comp (continuous_const.sub continuous_id)⟩,
      hck.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hf := locallyIntegrable_indicator_one hE
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiG := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => E.indicator (fun _ => (1 : ℝ)) y • gradient k (x - y)) at hiG
  have hiν : Integrable (fun y => k (x - y) • ν y) μ :=
    h.locallyIntegrable.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  rw [gradient_convolution_left hf hk hck x]
  apply PiLp.ext
  intro i
  rw [PiLp.neg_apply, eval_integral_piLp hiG.eval_piLp, eval_integral_piLp hiν.eval_piLp]
  have ht := h.coordinate_eq i φ hφ
  have hd (y : AmbientSpace) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hd, mul_neg, integral_neg, neg_neg] at ht
  simpa only [PiLp.smul_apply, smul_eq_mul] using! ht

/-- Mollified perimeter derivatives converge against every compact continuous
vector field, with the outward-normal sign fixed by the distributional identity. -/
theorem IsAmbientOutwardPerimeterPolar.tendsto_gradient_convolution_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (X : CompactlySupportedContinuousMap AmbientSpace AmbientSpace) :
    Tendsto (fun j => ∫ x, inner ℝ (X x)
      (gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        E.indicator (fun _ => (1 : ℝ))) x)) atTop
      (𝓝 (-∫ y, inner ℝ (X y) (ν y) ∂μ)) := by
  let := h.finiteOnCompacts
  have heq (j : ℕ) (x : AmbientSpace) := h.gradient_convolution_eq hE
    ((φ j).contDiff_normed (μ := volume))
      ((φ j).hasCompactSupport_normed (μ := volume)) x
  simp_rw [heq, inner_neg_right, integral_neg]
  exact (LocallyIntegrable.tendsto_integral_inner_measure_convolution h.locallyIntegrable hφ X).neg

end LiquidDrop
