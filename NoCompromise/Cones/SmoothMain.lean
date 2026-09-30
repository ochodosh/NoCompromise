module

public import NoCompromise.Cones.SmoothExcess
public import NoCompromise.Cones.SmoothGraph

@[expose] public section

/-!
# `lem:cone-smooth`: `C^{1,1/2}` regularity of the punctured boundary of a 3-d minimising cone

Assembly of blueprint `lem:cone-smooth` (chapter 25) up to the Schauder step:

* `cone_C1half_graph_of_ne_zero` : unconditionally, near every nonzero boundary point `p` of a
  nontrivial locally perimeter-minimising cone `C ⊂ ℝ³`, the boundary of `densityOne C` is, in the
  rotated and rescaled cylinder `p + s • Q (standardCylinder (1/4))` (`Q = verticalAxisIsometry ν`,
  `ν ⊥ p` the outward normal of a halfspace tangent), the graph of a `C^{1,1/2}` function with
  arbitrarily small Hölder constant, at arbitrarily small scale `s`;
* `cone_smooth_graph_of_ne_zero` : the same graph is smooth, assuming the Schauder step
  `MinimalGraphSmoothStatement` (stated explicitly in `Cones/SmoothGraph.lean`, not proved).
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace LiquidDrop

/-- **`lem:cone-smooth`, `C^{1,1/2}` part, unconditionally.** -/
theorem cone_C1half_graph_of_ne_zero {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
    ∀ {δ s₀ : ℝ}, 0 < δ → 0 < s₀ →
    ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧ s ≤ 1 ∧
      ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (νΩ : AmbientSpace → AmbientSpace),
        (∀ y ∈ standardCylinder (1 / 4),
          (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
            ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), graphAppendN x' (f x') = y)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          graphAppendN x' (f x') ∈ standardCylinder (1 / 4)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          HasFDerivAt f (-(νΩ (graphAppendN x' (f x')) 2)⁻¹ •
            innerSL ℝ (graphProjectionN 2 (νΩ (graphAppendN x' (f x'))))) x') ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ‖νΩ (graphAppendN x' (f x'))‖ = 1) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ δ * Real.sqrt ‖x' - y'‖) := by
  obtain ⟨ν, hν, hνp, r, hr, hr0, hexc⟩ := cone_tendsto_cylindricalExcess_of_ne_zero hC hp hp0
  exact ⟨ν, hν, hνp, fun hδ hs₀ =>
    cone_C1half_graph_of_tendsto_excess hC hν hp hr hr0 hexc hδ hs₀⟩

/-- **`lem:cone-smooth` from the Schauder step.**  Under `MinimalGraphSmoothStatement`, near every
nonzero boundary point the boundary of `densityOne C` is a smooth graph over the tangent plane
`ν^⊥ ∋ p`, at arbitrarily small scale. -/
theorem cone_smooth_graph_of_ne_zero (hS : MinimalGraphSmoothStatement) {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
    ∀ {s₀ : ℝ}, 0 < s₀ →
    ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        (∀ y ∈ standardCylinder (1 / 4),
          (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
            ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), graphAppendN x' (f x') = y)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        ContDiffOn ℝ ∞ f (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) := by
  obtain ⟨ν, hν, hνp, r, hr, hr0, hexc⟩ := cone_tendsto_cylindricalExcess_of_ne_zero hC hp hp0
  exact ⟨ν, hν, hνp, fun hs₀ =>
    cone_smooth_graph_of_tendsto_excess hS hC hν hp hr hr0 hexc hs₀⟩

end LiquidDrop
