import NoCompromise.BV.ScalarMollification
import NoCompromise.BV.ScalarC1Transport
import NoCompromise.Variation.TransportPairing

/-!
# Scalar distributional transport through C¹ coordinates

A locally integrable scalar function with a genuine distributional derivative
measure satisfies the cofactor change-of-variables formula. Smooth convolution
is used only inside compact tests, so neither global integrability nor finite
global derivative mass is required.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

/-- Distributional change of variables for scalar functions under C¹ diffeomorphisms.
The density `σ` represents `Df`, with the positive distributional sign convention. -/
theorem scalar_distributional_transport_C1
    {f : AmbientSpace → ℝ} (hf : LocallyIntegrable f)
    {μ : Measure AmbientSpace} [SFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, φ x * σ x i ∂μ)
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) {s : ℝ}
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    (∫ y, f (Φ.symm y) * divergenceN X y) =
      -∫ x, inner ℝ (X (Φ x)) (s • cofactor3 (fderiv ℝ Φ x) (σ x)) ∂μ := by
  let φ (j : ℕ) : ContDiffBump (0 : AmbientSpace) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let u (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hu (j : ℕ) : ContDiff ℝ 1 (u j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed hf
  let Z : CompactlySupportedContinuousMap AmbientSpace AmbientSpace :=
    ⟨⟨piolaPullback Φ X, continuous_piolaPullback hΦ hX.continuous⟩,
      hasCompactSupport_piolaPullback Φ hcX⟩
  let q : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun x => |(fderiv ℝ Φ x).det| * divergenceN X (Φ x),
      ((ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv one_ne_zero)).abs).mul
        ((continuous_divergenceN hX).comp Φ.continuous)⟩, by
      have hcdiv : HasCompactSupport (divergenceN X) := by
        apply hcX.mono'
        intro x hx
        by_contra hx'
        exact hx (divergenceN_eq_zero_of_notMem_tsupport hx')
      exact (hcdiv.comp_homeomorph Φ).mul_left⟩
  have hleft := tendsto_integral_scalar_bump_convolution_mul hf hlim q
  have hgrad := tendsto_gradient_convolution_pairing_of_distributional_pairing
    hf hσ hpair hlim Z
  have hright := hgrad.const_mul (-s)
  have heq (j : ℕ) : (-s) * (∫ x, inner ℝ (Z x) (gradient (u j) x)) =
      ∫ x, q x * u j x := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm (q x) (u j x)))]
    exact (smooth_transport_pairing Φ hΦ hiΦ (hu j) hX hcX hsgn).symm
  change Tendsto (fun j => (-s) * (∫ x, inner ℝ (Z x) (gradient (u j) x))) atTop
    (𝓝 ((-s) * (∫ y, inner ℝ (Z y) (σ y) ∂μ))) at hright
  simp_rw [heq] at hright
  have hp : (∫ x, q x * f x) = (-s) * (∫ y, inner ℝ (Z y) (σ y) ∂μ) :=
    tendsto_nhds_unique hleft hright
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x (_ : x ∈ (univ : Set AmbientSpace)) =>
      (hΦ.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt)
    Φ.injective.injOn (fun y => f (Φ.symm y) * divergenceN X y)
  simp only [image_univ, Φ.surjective.range_eq, setIntegral_univ, smul_eq_mul,
    Φ.symm_apply_apply] at hchange
  calc
    _ = ∫ x, q x * f x := by
      rw [hchange]
      apply integral_congr_ae
      filter_upwards [] with x
      change _ = (|(fderiv ℝ Φ x).det| * divergenceN X (Φ x)) * f x
      ring
    _ = (-s) * (∫ y, inner ℝ (Z y) (σ y) ∂μ) := hp
    _ = _ := by
      rw [neg_mul, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      change s * inner ℝ ((cofactor3 (fderiv ℝ Φ x)).adjoint (X (Φ x))) (σ x) = _
      rw [(cofactor3 (fderiv ℝ Φ x)).adjoint_inner_left, inner_smul_right]

end LiquidDrop
