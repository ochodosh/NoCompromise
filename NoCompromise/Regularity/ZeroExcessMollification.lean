import NoCompromise.DeGiorgi.HalfspaceRigidity
import Mathlib.Topology.MetricSpace.Thickening

/-! # Local constant-normal identities and mollified height ordering -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient CompactlySupported Convolution
namespace LiquidDrop

/-- The actual local distributional identity Dχ_E=−νμ. Only tests supported
in U occur, and no derivative information outside U is required. -/
def HasLocalConstantIndicatorPolar (E U : Set AmbientSpace) (μ : Measure AmbientSpace)
    (ν : AmbientSpace) : Prop :=
  ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ), ContDiff ℝ 1 φ →
    tsupport φ ⊆ U →
      -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, φ x * (-ν i) ∂μ

lemma HasLocalConstantIndicatorPolar.gradient_convolution_eq
    {E U : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasLocalConstantIndicatorPolar E U μ ν) (hE : NullMeasurableSet E volume)
    {k : AmbientSpace → ℝ} (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : AmbientSpace) (hs : tsupport (fun y => k (x - y)) ⊆ U) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) x =
      -(∫ y, k (x - y) ∂μ) • ν := by
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
  rw [gradient_convolution_left hf hk hck x]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiG.eval_piLp]
  have ht := h i φ hφ hs
  have hd (y : AmbientSpace) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hd, mul_neg, integral_neg, neg_neg] at ht
  rw [integral_mul_const] at ht
  change (∫ y, E.indicator (fun _ => (1 : ℝ)) y * gradient k (x - y) i) =
    -((∫ y, k (x - y) ∂μ) * ν i) at ht
  simpa only [PiLp.smul_apply, smul_eq_mul, neg_mul] using ht

lemma height_antitone_on_segment_of_gradient {f : AmbientSpace → ℝ} {ν x y : AmbientSpace}
    (hf : Differentiable ℝ f)
    (hgrad : ∀ z ∈ segment ℝ x y, ∃ a : ℝ, 0 ≤ a ∧ gradient f z = -a • ν)
    (hxy : inner ℝ ν x ≤ inner ℝ ν y) : f y ≤ f x := by
  obtain ⟨z, hzS, hz⟩ := domain_mvt (s := segment ℝ x y)
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  obtain ⟨a, ha, hza⟩ := hgrad z hzS
  rw [← inner_gradient_left, hza, inner_smul_left, inner_sub_right] at hz
  simp only [starRingEnd_apply, star_trivial] at hz
  have hnonpos : -a * (inner ℝ ν y - inner ℝ ν x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr hxy)
  linarith

lemma HasLocalConstantIndicatorPolar.bump_height_order
    {E U : Set AmbientSpace} {μ : Measure AmbientSpace} {ν x y : AmbientSpace}
    (h : HasLocalConstantIndicatorPolar E U μ ν) (hE : NullMeasurableSet E volume)
    (φ : ContDiffBump (0 : AmbientSpace))
    (hs : ∀ z ∈ segment ℝ x y, tsupport (fun w => φ.normed volume (z - w)) ⊆ U)
    (hxy : inner ℝ ν x ≤ inner ℝ ν y) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) y ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) x := by
  have hsm : ContDiff ℝ 1
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (locallyIntegrable_indicator_one hE)
  apply height_antitone_on_segment_of_gradient (hsm.differentiable one_ne_zero) _ hxy
  intro z hz
  exact ⟨∫ w, φ.normed volume (z - w) ∂μ,
    integral_nonneg (fun _ => φ.nonneg_normed (μ := volume) _),
    h.gradient_convolution_eq hE φ.contDiff_normed φ.hasCompactSupport_normed z (hs z hz)⟩

end LiquidDrop
