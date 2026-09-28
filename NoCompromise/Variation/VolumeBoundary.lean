import NoCompromise.Variation.Volume
import NoCompromise.DeGiorgi.Structure

/-!
# First variation of volume with the actual boundary integral

Gauss–Green identifies the already proved bulk volume derivative with the
Hausdorff integral of the outward reduced normal. The set may be merely
Lebesgue measurable and have infinite total perimeter.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace LiquidDrop

/-- The volume derivative under a compactly supported C¹ straight perturbation. -/
theorem first_variation_volume (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEfin : volume E < ∞) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    HasDerivAt (fun t : ℝ => (volume (straightPerturbation X t '' E)).toReal)
      (∫ x in reducedBoundary E hE hmE, inner ℝ (X x) (reducedNormal E hE hmE x)
        ∂hausdorffMeasure2 3) 0 := by
  rw [← gauss_green E hE hmE X hX hcX]
  exact hasDerivAt_volume_straightPerturbation_image hX hcX hmE hEfin

/-- The derivative equals both the bulk divergence and the boundary normal flux. -/
theorem first_variation_volume_eq (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEfin : volume E < ∞) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    deriv (fun t : ℝ => (volume (straightPerturbation X t '' E)).toReal) 0 =
      ∫ x in E, divergenceN X x ∧
    (∫ x in E, divergenceN X x) =
      ∫ x in reducedBoundary E hE hmE, inner ℝ (X x) (reducedNormal E hE hmE x)
        ∂hausdorffMeasure2 3 :=
  ⟨(hasDerivAt_volume_straightPerturbation_image hX hcX hmE hEfin).deriv,
    gauss_green E hE hmE X hX hcX⟩

end LiquidDrop
