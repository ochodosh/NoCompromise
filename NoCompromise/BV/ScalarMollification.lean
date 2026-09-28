import NoCompromise.BV.PolarMollification

/-!
# Scalar BV mollification against compact continuous tests

The scalar convolution limit follows by embedding scalar densities in one unit
coordinate of the proved vector convolution theorem. The gradient formula uses
only the actual coordinate distributional pairing and local integrability.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

/-- Locally integrable scalar functions converge weakly against every compact
continuous weight under normalized bump convolution. -/
theorem tendsto_integral_scalar_bump_convolution_mul
    {f : AmbientSpace → ℝ} (hf : LocallyIntegrable f)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (q : CompactlySupportedContinuousMap AmbientSpace ℝ) :
    Tendsto (fun j => ∫ x, q x *
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x) atTop
      (𝓝 (∫ x, q x * f x)) := by
  let e : AmbientSpace := EuclideanSpace.single 0 1
  have he : inner ℝ e e = 1 := by simp [e]
  let X : CompactlySupportedContinuousMap AmbientSpace AmbientSpace :=
    ⟨⟨fun x => q x • e, q.continuous.smul continuous_const⟩, q.hasCompactSupport.smul_right⟩
  have hg : LocallyIntegrable (fun x => f x • e) := hf.smul_continuous continuous_const
  have h := LocallyIntegrable.tendsto_integral_inner_measure_convolution hg hφ X
  change Tendsto (fun j => ∫ x, inner ℝ (q x • e)
    (∫ y, (φ j).normed volume (x - y) • (f y • e))) atTop
    (𝓝 (∫ x, inner ℝ (q x • e) (f x • e))) at h
  simp_rw [smul_smul, integral_smul_const, real_inner_smul_left, inner_smul_right, he,
    mul_one] at h
  simpa only [convolution_lsmul_swap, smul_eq_mul] using! h

/-- A true distributional vector density convolves to the ordinary smooth gradient. -/
theorem gradient_convolution_eq_of_distributional_pairing
    {f : AmbientSpace → ℝ} (hf : LocallyIntegrable f)
    {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, φ x * σ x i ∂μ)
    {k : AmbientSpace → ℝ} (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : AmbientSpace) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
      ∫ y, k (x - y) • σ y ∂μ := by
  let φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun y => k (x - y), hk.continuous.comp (continuous_const.sub continuous_id)⟩,
      hck.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiG := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => f y • gradient k (x - y)) at hiG
  have hiσ : Integrable (fun y => k (x - y) • σ y) μ :=
    hσ.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  rw [gradient_convolution_left hf hk hck x]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiG.eval_piLp, eval_integral_piLp hiσ.eval_piLp]
  have ht := hpair i φ hφ
  have hd (y : AmbientSpace) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hd, mul_neg, integral_neg, neg_neg] at ht
  simpa only [PiLp.smul_apply, smul_eq_mul] using! ht

/-- Distributional gradients converge against compact continuous vector fields. -/
theorem tendsto_gradient_convolution_pairing_of_distributional_pairing
    {f : AmbientSpace → ℝ} (hf : LocallyIntegrable f)
    {μ : Measure AmbientSpace} [SFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, φ x * σ x i ∂μ)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (X : CompactlySupportedContinuousMap AmbientSpace AmbientSpace) :
    Tendsto (fun j => ∫ x, inner ℝ (X x)
      (gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x)) atTop
      (𝓝 (∫ y, inner ℝ (X y) (σ y) ∂μ)) := by
  have heq (j : ℕ) (x : AmbientSpace) :=
    gradient_convolution_eq_of_distributional_pairing hf hσ hpair
      ((φ j).contDiff_normed (μ := volume)) ((φ j).hasCompactSupport_normed (μ := volume)) x
  simp_rw [heq]
  exact LocallyIntegrable.tendsto_integral_inner_measure_convolution hσ hφ X

end LiquidDrop
