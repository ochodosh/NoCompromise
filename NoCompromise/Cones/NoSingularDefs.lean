module

public import NoCompromise.Regularity.SlabCap
public import NoCompromise.Regularity.IsometryExcess

@[expose] public section

/-!
# Regular boundary points (`prop:no-singular-points`, chapter 26)

Blueprint `prop:no-singular-points` says that every boundary point of the density-one
representative `Ω` of an `ω`-minimal set is *regular*: it has a `C^{1,1/2}` graph
neighbourhood (the conclusion of `thm:eps-regularity`).  `IsRegularBoundaryPoint Ω x` records
exactly this, in the rotated and rescaled cylinder `x + s • Q (standardCylinder (1/4))`,
`Q = verticalAxisIsometry ν`:

* inside that cylinder `Ω` is the strict subgraph `{y 2 < f y'}` and `∂Ω` is the graph
  `{y 2 = f y'}`;
* `|f| < 1/8` on the base disk of radius `1/4`;
* `f` is differentiable at every point of the disk and `Df` is `1/2`-Hölder there (`C^{1,1/2}`).
-/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- `x` is a regular boundary point of `Ω`: a one-sided `C^{1,1/2}` graph chart in a rotated,
rescaled cylinder centred at `x`. -/
def IsRegularBoundaryPoint (Ω : Set AmbientSpace) (x : AmbientSpace) : Prop :=
  ∃ (ν : AmbientSpace) (s K : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
    ‖ν‖ = 1 ∧ 0 < s ∧
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), DifferentiableAt ℝ f x') ∧
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
      ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
        ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ K * Real.sqrt ‖x' - y'‖) ∧
    (∀ y ∈ standardCylinder (1 / 4),
      (x + s • verticalAxisIsometry ν y ∈ Ω ↔ y 2 < f (graphProjectionN 2 y))) ∧
    (∀ y ∈ standardCylinder (1 / 4),
      (x + s • verticalAxisIsometry ν y ∈ frontier Ω ↔ y 2 = f (graphProjectionN 2 y)))

end LiquidDrop
