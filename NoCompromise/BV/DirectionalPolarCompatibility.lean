import NoCompromise.BV.JumpDisintegration
import NoCompromise.DeGiorgi.Structure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Directional variation and the reduced normal component

Two locally finite scalar derivative representations with the same distributional
pairing are compared over their sum measure. The fundamental lemma for smooth
tests identifies the signed Radon–Nikodym densities; taking absolute values then
identifies the positive directional variation measure.

For a set of locally finite perimeter this gives the exact normal-component
measure, and the proved De Giorgi structure theorem expresses it as weighted
Hausdorff area on the reduced boundary.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma locallyIntegrable_toReal_rnDeriv_mul {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin n))} [SigmaFinite μ] [SigmaFinite ρ]
    (hμρ : μ ≪ ρ) {s : EuclideanSpace ℝ (Fin n) → ℝ}
    (hs : LocallyIntegrable s μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ρ x).toReal * s x) ρ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  rw [← integrable_indicator_iff hK.measurableSet]
  have hi := (integrable_toReal_rnDeriv_mul_iff hμρ).mpr
    ((hs.integrableOn_isCompact hK).integrable_indicator hK.measurableSet)
  have he : K.indicator (fun x => (μ.rnDeriv ρ x).toReal * s x) =
      (fun x => (μ.rnDeriv ρ x).toReal * K.indicator s x) := by
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [he]
  exact hi

/-- Scalar distributional pairings uniquely identify the positive total variation,
even when the compared densities are carried by different locally finite measures. -/
theorem IsDirectionalBVPolar.measure_eq_withDensity_of_pairing {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {τ μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]
    (h : IsDirectionalBVPolar f v τ s) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : Measurable w) (hwi : LocallyIntegrable w μ)
    (hpair : ∀ φ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      -(∫ x, f x * fderiv ℝ φ x v) = ∫ x, φ x * w x ∂μ) :
    τ = μ.withDensity (fun x => ENNReal.ofReal |w x|) := by
  let := h.finiteOnCompacts
  let ρ := τ + μ
  have hτρ : τ ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right μ
  have hμρ : μ ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right' τ
  have he : (fun x => (τ.rnDeriv ρ x).toReal * s x) =ᵐ[ρ]
      (fun x => (μ.rnDeriv ρ x).toReal * w x) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_toReal_rnDeriv_mul hτρ h.locallyIntegrable_density)
      (locallyIntegrable_toReal_rnDeriv_mul hμρ hwi)
    intro φ hφ hcφ
    have hc1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have ht := integral_toReal_rnDeriv_mul hτρ (f := fun x => φ x * s x)
    have hu := integral_toReal_rnDeriv_mul hμρ (f := fun x => φ x * w x)
    simp only [smul_eq_mul]
    calc
      (∫ x, φ x * ((τ.rnDeriv ρ x).toReal * s x) ∂ρ) =
          ∫ x, (τ.rnDeriv ρ x).toReal * (φ x * s x) ∂ρ :=
        integral_congr_ae (Eventually.of_forall fun _ => by ring)
      _ = ∫ x, φ x * s x ∂τ := ht
      _ = ∫ x, φ x * w x ∂μ := (h.test_eq φ hc1 hcφ).symm.trans (hpair φ hc1 hcφ)
      _ = ∫ x, (μ.rnDeriv ρ x).toReal * (φ x * w x) ∂ρ := hu.symm
      _ = ∫ x, φ x * ((μ.rnDeriv ρ x).toReal * w x) ∂ρ :=
        integral_congr_ae (Eventually.of_forall fun _ => by ring)
  have hn : ∀ᵐ x ∂ρ, τ.rnDeriv ρ x ≠ 0 → |s x| = 1 := by
    apply (ae_withDensity_iff (Measure.measurable_rnDeriv τ ρ)).mp
    rw [Measure.withDensity_rnDeriv_eq τ ρ hτρ]
    exact h.norm_ae
  have hr : τ.rnDeriv ρ =ᵐ[ρ]
      (fun x => μ.rnDeriv ρ x * ENNReal.ofReal |w x|) := by
    filter_upwards [he, hn, Measure.rnDeriv_lt_top τ ρ, Measure.rnDeriv_lt_top μ ρ]
      with x hx hs hτ hμ
    have hab := congrArg abs hx
    rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg] at hab
    have hs' : (τ.rnDeriv ρ x).toReal * |s x| = (τ.rnDeriv ρ x).toReal := by
      by_cases hz : τ.rnDeriv ρ x = 0
      · simp [hz]
      · rw [hs hz, mul_one]
    rw [hs'] at hab
    rw [← ENNReal.ofReal_toReal hτ.ne, hab, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hμ.ne]
  calc
    τ = ρ.withDensity (τ.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq τ ρ hτρ).symm
    _ = ρ.withDensity (fun x => μ.rnDeriv ρ x * ENNReal.ofReal |w x|) :=
      withDensity_congr_ae hr
    _ = μ.withDensity (fun x => ENNReal.ofReal |w x|) := by
      rw [show (fun x => μ.rnDeriv ρ x * ENNReal.ofReal |w x|) =
        (μ.rnDeriv ρ) * (fun x => ENNReal.ofReal |w x|) from rfl,
        withDensity_mul ρ (Measure.measurable_rnDeriv μ ρ)
          (by simpa only [Real.norm_eq_abs] using hw.norm.ennreal_ofReal),
        Measure.withDensity_rnDeriv_eq μ ρ hμρ]

lemma IsAmbientOutwardPerimeterPolar.directional_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    (v : AmbientSpace) {φ : AmbientSpace → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    -(∫ x, E.indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) =
      ∫ x, φ x * (-inner ℝ v (ν x)) ∂μ := by
  let X : AmbientSpace → AmbientSpace := fun x => φ x • v
  have hdiv (x : AmbientSpace) : divergenceN X x = fderiv ℝ φ x v := by
    rw [divergenceN_smul_of_differentiableAt (hφ.differentiable one_ne_zero x)
      (differentiableAt_const v)]
    simp [divergenceN, inner_gradient_left]
  have he := h.divergence_eq X (hφ.smul contDiff_const) hcφ.smul_right
  simp only [hdiv, X, real_inner_smul_left] at he
  have hind : (fun x => E.indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) =
      E.indicator (fun x => fderiv ℝ φ x v) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [hind, integral_indicator₀ hmE, he]
  simp only [mul_neg, integral_neg]

/-- The actual scalar directional variation is the absolute normal component
of any ambient outward perimeter polar. -/
theorem IsDirectionalBVPolar.measure_eq_normal_component
    {E : Set AmbientSpace} {τ μ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    {ν : AmbientSpace → AmbientSpace} {v : AmbientSpace}
    (h : IsDirectionalBVPolar (E.indicator (fun _ => (1 : ℝ))) v τ s)
    (hμ : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume) :
    τ = μ.withDensity (fun x => ENNReal.ofReal |inner ℝ v (ν x)|) := by
  let := hμ.finiteOnCompacts
  have hw : Measurable (fun x => -inner ℝ v (ν x)) :=
    ((innerSL ℝ v).continuous.measurable.comp hμ.measurable).neg
  have hwi : LocallyIntegrable (fun x => -inner ℝ v (ν x)) μ := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact ((innerSL ℝ v).integrable_comp (hμ.locallyIntegrable.integrableOn_isCompact hK)).neg
  have he := h.measure_eq_withDensity_of_pairing hw hwi
    (fun _ hφ hcφ => hμ.directional_pairing hmE v hφ hcφ)
  simpa only [abs_neg] using he

/-- The directional variation measure equals the normal-weighted Hausdorff area
on the actual reduced boundary. -/
theorem IsDirectionalBVPolar.measure_eq_reducedBoundary_normal_component
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {τ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    {v : AmbientSpace}
    (h : IsDirectionalBVPolar (E.indicator (fun _ => (1 : ℝ))) v τ s) :
    τ = ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).withDensity
      (fun x => ENNReal.ofReal |inner ℝ v (reducedNormal E hE hmE x)|) :=
  h.measure_eq_normal_component (reducedBoundary_outwardPerimeterPolar E hE hmE) hmE

lemma IsDirectionalBVPolar.integral_eq_reducedBoundary_normal_component
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {τ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    {v : AmbientSpace}
    (h : IsDirectionalBVPolar (E.indicator (fun _ => (1 : ℝ))) v τ s)
    (ζ : AmbientSpace → ℝ) :
    (∫ x, ζ x ∂τ) = ∫ x in reducedBoundary E hE hmE,
      ζ x * |inner ℝ v (reducedNormal E hE hmE x)| ∂hausdorffMeasure2 3 := by
  rw [h.measure_eq_reducedBoundary_normal_component hE hmE,
    integral_withDensity_eq_integral_toReal_smul
      (by simpa only [Real.norm_eq_abs, Function.comp_def, innerSL_apply_apply] using
        ((innerSL ℝ v).continuous.measurable.comp
          (measurable_reducedNormal E hE hmE)).norm.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ζ]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, mul_comm]

end LiquidDrop
