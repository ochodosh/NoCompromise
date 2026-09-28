import NoCompromise.Regularity.DeformationExtensionPhases

/-! # Locality of the genuine perimeter measure for the slice extension -/

noncomputable section
open Set MeasureTheory
namespace LiquidDrop

lemma canonicalPerimeterMeasure_restrict_eq_of_indicator_ae
    {E F : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hF : HasLocallyFinitePerimeter F)
    (hmF : NullMeasurableSet F volume) {U : Set AmbientSpace} (hU : IsOpen U)
    (hEF : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U]
      F.indicator (fun _ => (1 : ℝ))) :
    (canonicalPerimeterMeasure E hE hmE).restrict U =
      (canonicalPerimeterMeasure F hF hmF).restrict U := by
  let := (canonicalPerimeterPolar E hE hmE).regular
  let := (canonicalPerimeterPolar F hF hmF).regular
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet,
    canonicalPerimeterMeasure_open E hE hmE (hO.inter hU),
    canonicalPerimeterMeasure_open F hF hmF (hO.inter hU)]
  exact variation_congr_ae (O ∩ U) (ae_restrict_of_ae_restrict_of_subset inter_subset_right hEF)

lemma verticalPhaseExtension_perimeter_locality {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r : ℝ}
    (hExt : HasLocallyFinitePerimeter (verticalPhaseExtension E r))
    (hmExt : NullMeasurableSet (verticalPhaseExtension E r) volume) :
    (canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt).restrict
      (standardCylinder r) = (canonicalPerimeterMeasure E hE hmE).restrict
        (standardCylinder r) := by
  apply canonicalPerimeterMeasure_restrict_eq_of_indicator_ae hExt hmExt hE hmE
    (isOpen_standardCylinder r)
  apply (ae_restrict_iff' (isOpen_standardCylinder r).measurableSet).mpr
  exact Filter.Eventually.of_forall fun x hx => by
    have he := verticalPhaseExtension_agrees_on_cylinder (E := E) hx
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem (he.mpr hxE), indicator_of_mem hxE]
    · rw [indicator_of_notMem (mt he.mp hxE), indicator_of_notMem hxE]

end LiquidDrop
