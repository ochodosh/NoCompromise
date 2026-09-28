import NoCompromise.Regularity.SlabCap
import NoCompromise.Regularity.Excess
import NoCompromise.Sobolev.Maximal

/-! # The genuine projected excess measure and its good base set -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Blueprint `def:projected-excess`: horizontal pushforward of the actual
quadratic reduced-normal error in the three-quarter cylinder. -/
def projectedExcessMeasure (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  Measure.map (graphProjectionN 2)
    (((canonicalPerimeterMeasure E hE hmE).restrict (standardCylinder (3 / 4))).withDensity
      (fun x => ENNReal.ofReal
        (‖reducedNormal E hE hmE x - EuclideanSpace.single 2 1‖ ^ 2)))

def projectedExcessMaximal (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
  truncatedMaximalMeasure (projectedExcessMeasure E hE hmE) (1 / 8)

def goodExcessBase (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | projectedExcessMaximal E hE hmE x ≤ ENNReal.ofReal (c * γ ^ 2)} ∩ ball 0 (1 / 2)

lemma projectedExcessMeasure_apply (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) :
    projectedExcessMeasure E hE hmE A =
      ∫⁻ x in (graphProjectionN 2 ⁻¹' A) ∩ standardCylinder (3 / 4) ∩
        reducedBoundary E hE hmE,
        ENNReal.ofReal (‖reducedNormal E hE hmE x - EuclideanSpace.single 2 1‖ ^ 2)
          ∂hausdorffMeasure2 3 := by
  rw [projectedExcessMeasure, Measure.map_apply (graphProjectionN 2).measurable hA,
    withDensity_apply _ (hA.preimage (graphProjectionN 2).measurable),
    Measure.restrict_restrict (hA.preimage (graphProjectionN 2).measurable),
    canonicalPerimeterMeasure_eq_reducedBoundary_area,
    Measure.restrict_restrict
      ((hA.preimage (graphProjectionN 2).measurable).inter
        (isOpen_standardCylinder (3 / 4)).measurableSet)]

lemma projectedExcessMeasure_univ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    projectedExcessMeasure E hE hmE univ = ENNReal.ofReal
      (normalExcessIntegral E hE hmE (standardCylinder (3 / 4))
        (EuclideanSpace.single 2 1)) := by
  rw [projectedExcessMeasure, Measure.map_apply (graphProjectionN 2).measurable MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    canonicalPerimeterMeasure_eq_reducedBoundary_area]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_normal_excess E hE hmE (isBounded_standardCylinder (3 / 4)) _)
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm

instance projectedExcessMeasure_finite (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : IsFiniteMeasure (projectedExcessMeasure E hE hmE) :=
  ⟨by rw [projectedExcessMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

lemma projectedExcessMeasure_mass_le (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    projectedExcessMeasure E hE hmE univ ≤ ENNReal.ofReal
      (cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1)) := by
  rw [projectedExcessMeasure_univ]
  apply ENNReal.ofReal_le_ofReal
  simp only [cylindricalExcess, one_pow, div_one]
  apply normalExcessIntegral_mono E hE hmE
    (isBounded_cylinder 0 1 (ν := EuclideanSpace.single 2 1) (by simp))
  rw [standardCylinder_eq_cylinder]
  exact cylinder_mono (by norm_num)

end LiquidDrop
