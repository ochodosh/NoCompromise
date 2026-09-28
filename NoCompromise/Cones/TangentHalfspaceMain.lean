import NoCompromise.Cones.TwoDimChord
import NoCompromise.Cones.TangentHalfspace

/-!
# Halfspace tangents of three-dimensional minimising cones, unconditionally

`lem:cone-2d` (`cone2d_halfplane`) discharges the hypothesis `Cone2dHalfplaneStatement` of
`Cones/TangentHalfspace.lean`: at every nonzero boundary point of a nontrivial locally
perimeter-minimising cone in `ℝ³`, every nontrivial tangent limit is an open halfspace with normal
orthogonal to the point, and such a tangent limit exists (first step of `lem:cone-smooth`).
-/

noncomputable section
namespace LiquidDrop

/-- Blueprint `lem:cone-2d`, in the form used by `Cones/TangentHalfspace.lean`. -/
theorem cone2dHalfplaneStatement_holds : Cone2dHalfplaneStatement :=
  fun _ hm hmin hcone hnt => cone2d_halfplane hm hmin hcone hnt

/-- Every nontrivial tangent limit at a nonzero boundary point of a nontrivial minimising cone in
`ℝ³` is an open halfspace whose normal is orthogonal to the point. -/
theorem cone_tangent_halfspace_of_ne_zero {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) {F : Set AmbientSpace}
    (hF : IsConeTangentLimit C p F) (hFnt : 0 < MeasureTheory.volume F ∧
      0 < MeasureTheory.volume Fᶜ) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧ densityOne F = {x | 0 < inner ℝ ν x} :=
  cone_tangent_halfspace cone2dHalfplaneStatement_holds hC hp hp0 hF hFnt

/-- At every nonzero boundary point of a nontrivial minimising cone in `ℝ³` there is a tangent
limit which is an open halfspace with normal orthogonal to the point. -/
theorem cone_exists_halfspace_tangent_of_ne_zero {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) :
    ∃ F : Set AmbientSpace, IsConeTangentLimit C p F ∧
      ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧ densityOne F = {x | 0 < inner ℝ ν x} :=
  cone_exists_halfspace_tangent cone2dHalfplaneStatement_holds hC hp hp0

end LiquidDrop
