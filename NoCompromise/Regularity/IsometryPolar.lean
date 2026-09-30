module

public import NoCompromise.Regularity.IsometryMinimal
public import NoCompromise.DeGiorgi.AmbientPolar

@[expose] public section

/-! # Actual perimeter polars under rigid coordinate changes -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma rigid_scalar_direction_derivative (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (v z : AmbientSpace) :
    fderiv ℝ (φ ∘ a.symm) z (a.linearIsometryEquiv v) = fderiv ℝ φ (a.symm z) v := by
  have hd := (hφ.differentiable one_ne_zero (a.symm z)).hasFDerivAt.comp z
    (hasFDerivAt_rigidPlacement a.symm z)
  have hh := congrArg (fun M => M (a.linearIsometryEquiv v)) hd.fderiv
  change fderiv ℝ (φ ∘ a.symm) z (a.linearIsometryEquiv v) =
    fderiv ℝ φ (a.symm z) (a.linearIsometryEquiv.symm (a.linearIsometryEquiv v)) at hh
  simpa only [a.linearIsometryEquiv.symm_apply_apply] using hh

lemma rigid_scalar_direction_divergence (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (v z : AmbientSpace) :
    divergenceN (fun y => φ (a.symm y) • a.linearIsometryEquiv v) z =
      fderiv ℝ φ (a.symm z) v := by
  change divergenceN (fun y => (φ ∘ a.symm) y • a.linearIsometryEquiv v) z = _
  rw [divergenceN_smul (hφ.comp (contDiff_rigidPlacement a.symm)) contDiff_const]
  have hz : divergenceN (fun _ : AmbientSpace => a.linearIsometryEquiv v) z = 0 := by
    simp [divergenceN]
  rw [hz, mul_zero, zero_add, inner_gradient_left]
  exact rigid_scalar_direction_derivative a hφ v z

/-- A rigid pullback has the pulled-back, rotated outward unit polar, as a
consequence of the actual distributional test pairings. -/
theorem IsAmbientOutwardPerimeterPolar.preimage_affineIsometry
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (hmE : NullMeasurableSet E volume)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    IsAmbientOutwardPerimeterPolar (a ⁻¹' E) (Measure.map a.symm.toHomeomorph μ)
      (fun y => a.linearIsometryEquiv.symm (σ (a y))) := by
  let := h.regular
  let := Measure.Regular.map (μ := μ) a.symm.toHomeomorph
  apply ambientOutwardPerimeterPolar_of_coordinate_pairing
    (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)
    (a.linearIsometryEquiv.symm.continuous.measurable.comp
      (h.measurable.comp a.continuous.measurable))
  · rw [a.symm.toHomeomorph.measurableEmbedding.ae_map_iff]
    change ∀ᵐ z ∂μ, ‖a.linearIsometryEquiv.symm (σ (a (a.symm z)))‖ = 1
    simpa only [a.apply_symm_apply, a.linearIsometryEquiv.symm.norm_map] using h.norm_ae
  · intro i φ hφ
    let v : AmbientSpace := EuclideanSpace.single i 1
    let X : AmbientSpace → AmbientSpace := fun z => φ (a.symm z) • a.linearIsometryEquiv v
    have hX : ContDiff ℝ 1 X := (hφ.comp (contDiff_rigidPlacement a.symm)).smul contDiff_const
    have hcX : HasCompactSupport X :=
      (φ.hasCompactSupport.comp_homeomorph a.symm.toHomeomorph).smul_right
    have ht := h.divergence_eq X hX hcX
    have hd (z : AmbientSpace) : divergenceN X z = fderiv ℝ φ (a.symm z) v :=
      rigid_scalar_direction_divergence a hφ v z
    simp only [hd, X, real_inner_smul_left] at ht
    have hi (z : AmbientSpace) : inner ℝ (a.linearIsometryEquiv v) (σ z) =
        a.linearIsometryEquiv.symm (σ z) i := by
      have he := a.linearIsometryEquiv.inner_map_map v (a.linearIsometryEquiv.symm (σ z))
      simpa only [a.linearIsometryEquiv.apply_symm_apply, v,
        EuclideanSpace.inner_single_left, one_mul, conj_trivial] using he
    simp_rw [hi] at ht
    have hvol := (measurePreserving_affineIsometry a).integral_comp
      a.toHomeomorph.measurableEmbedding
      (fun z => E.indicator (fun _ => (1 : ℝ)) z * fderiv ℝ φ (a.symm z) v)
    have hid (y : AmbientSpace) : E.indicator (fun _ => (1 : ℝ)) (a y) =
        (a ⁻¹' E).indicator (fun _ => (1 : ℝ)) y := by
      by_cases hy : a y ∈ E <;> simp [hy]
    simp only [a.symm_apply_apply, hid] at hvol
    have hprod : (fun z => E.indicator (fun _ => (1 : ℝ)) z *
        fderiv ℝ φ (a.symm z) v) = E.indicator (fun z => fderiv ℝ φ (a.symm z) v) := by
      funext z
      by_cases hz : z ∈ E <;> simp [hz]
    rw [hprod, integral_indicator₀ hmE] at hvol
    rw [a.symm.toHomeomorph.measurableEmbedding.integral_map]
    change -(∫ y, (a ⁻¹' E).indicator (fun _ => (1 : ℝ)) y * fderiv ℝ φ y v) =
      ∫ z, φ (a.symm z) * (-a.linearIsometryEquiv.symm (σ (a (a.symm z))) i) ∂μ
    simp only [a.apply_symm_apply, mul_neg, integral_neg]
    exact congrArg Neg.neg (hvol.trans ht)

end LiquidDrop
