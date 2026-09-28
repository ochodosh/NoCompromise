import NoCompromise.Regularity.DeformationLocality

/-! # The extension's column perimeter is exactly the original cylinder perimeter -/

noncomputable section
open Set MeasureTheory Filter
namespace LiquidDrop

theorem IsSlabCapConfiguration.extension_perimeter_column
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hExt : HasLocallyFinitePerimeter (verticalPhaseExtension E r))
    (hmExt : NullMeasurableSet (verticalPhaseExtension E r) volume)
    {s : ℝ} (hs : s ≤ r) :
    (canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt).restrict
      {x | ‖graphProjectionN 2 x‖ < s} =
      (canonicalPerimeterMeasure E hE hmE).restrict
        ({x | ‖graphProjectionN 2 x‖ < s} ∩ standardCylinder r) := by
  let μ := canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt
  have hz := h.extension_perimeter_off_slab
  have hzL : μ (lowerPhaseColumn r (c - η * r)) = 0 := by
    rw [canonicalPerimeterMeasure_open _ hExt hmExt (isOpen_lowerPhaseColumn _ _)]
    exact hz.1
  have hzU : μ (upperPhaseColumn r (c + η * r)) = 0 := by
    rw [canonicalPerimeterMeasure_open _ hExt hmExt (isOpen_upperPhaseColumn _ _)]
    exact hz.2
  have hgapL : -r < c - η * r := by linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by linarith [le_abs_self c, h.1.2.2.2.1]
  have hae : ({x : AmbientSpace | ‖graphProjectionN 2 x‖ < s} : Set AmbientSpace) =ᵐ[μ]
      (({x : AmbientSpace | ‖graphProjectionN 2 x‖ < s} ∩
        standardCylinder r) : Set AmbientSpace) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hzL),
      (measure_eq_zero_iff_ae_notMem.mp hzU)] with x hxL hxU
    apply propext
    constructor
    · intro hx
      have hp : ‖graphProjectionN 2 x‖ < r := lt_of_lt_of_le hx hs
      have hlow : c - η * r ≤ x 2 := le_of_not_gt (fun hh => hxL ⟨hp, hh⟩)
      have hup : x 2 ≤ c + η * r := le_of_not_gt (fun hh => hxU ⟨hp, hh⟩)
      exact ⟨hx, hp, abs_lt.mpr ⟨hgapL.trans_le hlow, hup.trans_lt hgapU⟩⟩
    · intro hx
      exact hx.1
  have hS : MeasurableSet {x : AmbientSpace | ‖graphProjectionN 2 x‖ < s} :=
    (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).measurableSet
  calc
    μ.restrict {x | ‖graphProjectionN 2 x‖ < s} =
        μ.restrict ({x | ‖graphProjectionN 2 x‖ < s} ∩ standardCylinder r) :=
      Measure.restrict_congr_set hae
    _ = (μ.restrict (standardCylinder r)).restrict {x | ‖graphProjectionN 2 x‖ < s} :=
      (Measure.restrict_restrict hS).symm
    _ = ((canonicalPerimeterMeasure E hE hmE).restrict (standardCylinder r)).restrict
        {x | ‖graphProjectionN 2 x‖ < s} := by
      rw [verticalPhaseExtension_perimeter_locality hE hmE hExt hmExt]
    _ = _ := Measure.restrict_restrict hS

end LiquidDrop
