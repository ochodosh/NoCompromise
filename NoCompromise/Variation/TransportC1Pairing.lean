module

public import NoCompromise.Variation.TransportPairing
public import NoCompromise.BV.PolarMollification
public import NoCompromise.BV.IndicatorMollification
public import NoCompromise.Measure.NullChangeOfVariables

@[expose] public section

/-!
# Distributional perimeter transport under C¹ diffeomorphisms

Smooth indicator mollifications satisfy the classical change-of-variables and
integration-by-parts identity. Their derivatives converge against the continuous
compact cofactor pullback; their values converge against its divergence weight.
Thus no derivative of the continuous cofactor field is required.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

/-- The full C¹ transport pairing for an actual ambient outward perimeter polar. -/
theorem IsAmbientOutwardPerimeterPolar.integral_image_divergence_C1
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) {s : ℝ}
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    (∫ y in Φ '' E, divergenceN X y) =
      ∫ x, inner ℝ (X (Φ x)) (s • cofactor3 (fderiv ℝ Φ x) (ν x)) ∂μ := by
  let φ (j : ℕ) : ContDiffBump (0 : AmbientSpace) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hratio : ∀ᶠ j in atTop, (φ j).rOut ≤ 2 * (φ j).rIn := by
    filter_upwards with j
    dsimp only [φ]
    linarith
  let u (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
    E.indicator (fun _ => (1 : ℝ))
  have hu (j : ℕ) : ContDiff ℝ 1 (u j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      (locallyIntegrable_indicator_one hmE)
  let Z : CompactlySupportedContinuousMap AmbientSpace AmbientSpace :=
    ⟨⟨piolaPullback Φ X, continuous_piolaPullback hΦ hX.continuous⟩,
      hasCompactSupport_piolaPullback Φ hcX⟩
  let q (x : AmbientSpace) := |(fderiv ℝ Φ x).det| * divergenceN X (Φ x)
  have hqc : Continuous q :=
    ((ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv one_ne_zero)).abs).mul
      ((continuous_divergenceN hX).comp Φ.continuous)
  have hcdiv : HasCompactSupport (divergenceN X) := by
    apply hcX.mono'
    intro x hx
    by_contra hx'
    exact hx (divergenceN_eq_zero_of_notMem_tsupport hx')
  have hcq : HasCompactSupport q := (hcdiv.comp_homeomorph Φ).mul_left
  have hleft := tendsto_integral_indicator_bump_convolution_mul hmE
    hlim hratio (hqc.integrable_of_hasCompactSupport hcq)
  have hgrad := h.tendsto_gradient_convolution_pairing hmE hlim Z
  have hright := hgrad.const_mul (-s)
  have heq (j : ℕ) : (-s) * (∫ x, inner ℝ (Z x) (gradient (u j) x)) =
      ∫ x, u j x * q x :=
    (smooth_transport_pairing Φ hΦ hiΦ (hu j) hX hcX hsgn).symm
  change Tendsto (fun j => (-s) * (∫ x, inner ℝ (Z x) (gradient (u j) x))) atTop
    (𝓝 ((-s) * (-∫ y, inner ℝ (Z y) (ν y) ∂μ))) at hright
  simp_rw [heq] at hright
  have hp : (∫ x in E, q x) = (-s) * (-∫ y, inner ℝ (Z y) (ν y) ∂μ) :=
    tendsto_nhds_unique hleft hright
  calc
    _ = ∫ x in E, q x := by
      exact integral_image_eq_abs_det_fderiv_mul_of_nullMeasurable
        (hΦ.differentiable one_ne_zero) Φ.injective hmE (divergenceN X)
    _ = s * ∫ y, inner ℝ (Z y) (ν y) ∂μ := by rw [hp, neg_mul_neg]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change s * inner ℝ ((cofactor3 (fderiv ℝ Φ x)).adjoint (X (Φ x))) (ν x) = _
      rw [(cofactor3 (fderiv ℝ Φ x)).adjoint_inner_left, inner_smul_right]

end LiquidDrop
