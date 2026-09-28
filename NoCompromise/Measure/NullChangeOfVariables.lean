import NoCompromise.BV.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables for Lebesgue-measurable sets

A globally differentiable map preserves volume-null sets. For injective maps,
a Borel representative therefore gives the usual integral formula on every
Lebesgue-measurable set, without changing the set itself.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LiquidDrop

lemma image_ae_eq_of_differentiable {Φ : AmbientSpace → AmbientSpace}
    (hΦ : Differentiable ℝ Φ) (hiΦ : Function.Injective Φ)
    {E F : Set AmbientSpace} (hEF : E =ᵐ[volume] F) :
    Φ '' E =ᵐ[volume] Φ '' F := by
  apply measure_symmDiff_eq_zero_iff.mp
  rw [← image_symmDiff hiΦ]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hΦ.differentiableOn (measure_symmDiff_eq_zero_iff.mpr hEF)

lemma nullMeasurableSet_image_of_differentiable
    {Φ : AmbientSpace → AmbientSpace} (hΦ : Differentiable ℝ Φ)
    (hiΦ : Function.Injective Φ) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) : NullMeasurableSet (Φ '' E) volume :=
  nullMeasurable_image_of_fderivWithin volume hE
    (fun x _ => (hΦ x).hasFDerivAt.hasFDerivWithinAt) hiΦ.injOn

/-- The ordinary Jacobian formula on an arbitrary Lebesgue-measurable set. -/
theorem integral_image_eq_abs_det_fderiv_mul_of_nullMeasurable
    {Φ : AmbientSpace → AmbientSpace} (hΦ : Differentiable ℝ Φ)
    (hiΦ : Function.Injective Φ) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (g : AmbientSpace → ℝ) :
    (∫ y in Φ '' E, g y) = ∫ x in E, |(fderiv ℝ Φ x).det| * g (Φ x) := by
  obtain ⟨F, _, hF, hFE⟩ := hE.exists_measurable_subset_ae_eq
  calc
    _ = ∫ y in Φ '' F, g y :=
      setIntegral_congr_set (image_ae_eq_of_differentiable hΦ hiΦ hFE).symm
    _ = ∫ x in F, |(fderiv ℝ Φ x).det| * g (Φ x) := by
      simpa only [smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume hF
          (fun x _ => (hΦ x).hasFDerivAt.hasFDerivWithinAt) hiΦ.injOn g
    _ = _ := setIntegral_congr_set hFE

end LiquidDrop
