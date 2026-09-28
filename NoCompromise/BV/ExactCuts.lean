import NoCompromise.BV.RadialCuts
import NoCompromise.BV.PlanarCuts

/-!
# Exact spherical and planar cuts

This combines all clauses of the blueprint proposition, retaining extended
perimeter values and assuming only local finite perimeter and measurability.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Blueprint `prop:cut-identities`: both exact spherical identities at every
good radius and both halfspace identities at almost every height. -/
theorem exact_cut_identities {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    (∀ (c : AmbientSpace) (r : ℝ), IsGoodRadius E hE hmE c r →
      (perimeter (E ∩ ball c r) = perimeterIn E (ball c r) +
        hausdorffMeasure2 3 (densityOne E ∩ sphere c r)) ∧
      perimeter (E \ ball c r) = perimeterIn E (closedBall c r)ᶜ +
        hausdorffMeasure2 3 (densityOne E ∩ sphere c r)) ∧
    (∀ ν : AmbientSpace, ‖ν‖ = 1 → ∀ᵐ a : ℝ,
      (perimeter (E ∩ {z | inner ℝ ν z < a}) =
        perimeterIn E {z | inner ℝ ν z < a} +
          hausdorffMeasure2 3 (densityOne E ∩ {z | inner ℝ ν z = a})) ∧
      perimeter (E \ {z | inner ℝ ν z < a}) =
        perimeterIn E {z | a < inner ℝ ν z} +
          hausdorffMeasure2 3 (densityOne E ∩ {z | inner ℝ ν z = a})) :=
  ⟨fun _ _ hg => hg.perimeter_cut_identities,
    fun _ hν => ae_perimeter_halfspace_cut_identities hE hmE hν⟩

end LiquidDrop
