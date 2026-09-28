import NoCompromise.Regularity.IsometryExcess
import NoCompromise.Regularity.ReversePoincare

/-! # Reverse Poincaré in an arbitrary orthogonal coordinate frame -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma heightIntegral_preimage_linearIsometry
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (r c : ℝ) :
    (∫ y in standardCylinder r, (y 2 - c) ^ 2
      ∂canonicalPerimeterMeasure (Q.toAffineIsometryEquiv ⁻¹' E)
        (hE.preimage_affineIsometry hmE Q.toAffineIsometryEquiv)
        (hmE.preimage
          (measurePreserving_affineIsometry Q.toAffineIsometryEquiv).quasiMeasurePreserving)) =
      ∫ y in cylinder 0 r (Q (EuclideanSpace.single 2 1)) ∩ reducedBoundary E hE hmE,
        (inner ℝ (Q (EuclideanSpace.single 2 1)) y - c) ^ 2 ∂hausdorffMeasure2 3 := by
  let a := Q.toAffineIsometryEquiv
  rw [setIntegral_preimage_affineIsometry_perimeter E hE hmE a]
  have hs : a '' standardCylinder r = cylinder 0 r (Q (EuclideanSpace.single 2 1)) := by
    change Q '' standardCylinder r = _
    rw [standardCylinder_eq_cylinder, image_cylinder_linearIsometry, map_zero]
  rw [hs, canonicalPerimeterMeasure_eq_reducedBoundary_area,
    Measure.restrict_restrict (isOpen_cylinder _ _ _).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with y
  change (Q.symm y 2 - c) ^ 2 = _
  rw [linearIsometry_inverse_vertical]

/-- The original universal reverse-Poincaré constant works in every orthogonal
frame. Its slab and cap hypothesis refers to the actual transformed set. -/
theorem IsOmegaMinimal.reverse_poincare_rotated
    {E : Set AmbientSpace} {ω r c η : ℝ} (hE : IsOmegaMinimal E ω)
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (h : IsSlabCapConfiguration (Q.toAffineIsometryEquiv ⁻¹' E)
      (hE.locallyFinite.preimage_affineIsometry hE.nullMeasurable Q.toAffineIsometryEquiv)
      (hE.nullMeasurable.preimage
        (measurePreserving_affineIsometry Q.toAffineIsometryEquiv).quasiMeasurePreserving) r c η)
    (hr1 : r ≤ 1 / Real.sqrt 2) :
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
      (Q (EuclideanSpace.single 2 1)) ≤
      (reversePoincareConstant / r ^ 4) *
        (∫ y in cylinder 0 r (Q (EuclideanSpace.single 2 1)) ∩
          reducedBoundary E hE.locallyFinite hE.nullMeasurable,
          (inner ℝ (Q (EuclideanSpace.single 2 1)) y - c) ^ 2 ∂hausdorffMeasure2 3) +
        reversePoincareConstant * ω * r := by
  let hF := hE.preimage_affineIsometry Q.toAffineIsometryEquiv
  have hi := hF.reverse_poincare h hr1
  rw [cylindricalExcess_preimage_linearIsometry E hE.locallyFinite hE.nullMeasurable,
    map_zero] at hi
  have hs : (∫ y in standardCylinder r ∩
      reducedBoundary (Q.toAffineIsometryEquiv ⁻¹' E) hF.locallyFinite hF.nullMeasurable,
      (y 2 - c) ^ 2 ∂hausdorffMeasure2 3) =
      ∫ y in standardCylinder r, (y 2 - c) ^ 2
        ∂canonicalPerimeterMeasure (Q.toAffineIsometryEquiv ⁻¹' E)
          hF.locallyFinite hF.nullMeasurable := by
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area,
      Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet]
  rw [hs, heightIntegral_preimage_linearIsometry E hE.locallyFinite hE.nullMeasurable Q] at hi
  exact hi

end LiquidDrop
