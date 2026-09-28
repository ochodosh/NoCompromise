import NoCompromise.Regularity.ExcessScalingPolar
import NoCompromise.Regularity.ExcessScalingGeometry
import NoCompromise.Regularity.Excess

/-!
# Exact positive-blowup covariance of normal excess

Both the perimeter measure and the actual reduced normal are transformed by the
proved polar uniqueness theorem. Thus the formulas below concern the existing
geometric excess, with no transformed-normal premise.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- The unnormalized normal error scales by the inverse square of the blowup radius. -/
theorem normalExcessIntegral_blowupSet (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (U : Set AmbientSpace) (ν : AmbientSpace) :
    normalExcessIntegral (blowupSet E x r) (hE.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hmE x hr) U ν =
        r⁻¹ ^ 2 * normalExcessIntegral E hE hmE ((fun y => x + r • y) '' U) ν := by
  let hB := hE.blowupSet (by norm_num) x hr
  let hmB := nullMeasurableSet_blowupSet hmE x hr
  calc
    _ = ∫ y in U, ‖reducedNormal (blowupSet E x r) hB hmB y - ν‖ ^ 2
        ∂canonicalPerimeterMeasure (blowupSet E x r) hB hmB := by
      rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]
      rfl
    _ = ∫ y in U, ‖reducedNormal E hE hmE (x + r • y) - ν‖ ^ 2
        ∂blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r := by
      rw [canonicalPerimeterMeasure_blowupSet E hE hmE x hr]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (reducedNormal_blowupSet_ae E hE hmE x hr)]
        with y hy
      rw [hy]
    _ = r⁻¹ ^ 2 * ∫ y in (fun z => x + r • z) '' U,
        ‖reducedNormal E hE hmE y - ν‖ ^ 2 ∂canonicalPerimeterMeasure E hE hmE := by
      rw [setIntegral_blowupPolarMeasure _ x hr]
      simp [smul_smul, hr.ne']
    _ = _ := by rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]; rfl

/-- Exact cylindrical excess covariance, at arbitrary centers and radii in blowup coordinates. -/
theorem cylindricalExcess_blowupSet (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (y : AmbientSpace) (R : ℝ)
    (ν : AmbientSpace) :
    cylindricalExcess (blowupSet E x r) (hE.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hmE x hr) y R ν =
        cylindricalExcess E hE hmE (x + r • y) (r * R) ν := by
  rw [cylindricalExcess, normalExcessIntegral_blowupSet E hE hmE x hr,
    image_cylinder_translate_pos_smul x y ν hr R, cylindricalExcess]
  by_cases hR : R = 0
  · simp [hR]
  · field_simp

/-- The unit-cylinder excess of the blowup equals the original radius-`r` excess. -/
theorem cylindricalExcess_blowupSet_unit (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (ν : AmbientSpace) :
    cylindricalExcess (blowupSet E x r) (hE.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hmE x hr) 0 1 ν = cylindricalExcess E hE hmE x r ν := by
  simpa only [smul_zero, add_zero, mul_one] using
    cylindricalExcess_blowupSet E hE hmE x hr 0 1 ν

end LiquidDrop
