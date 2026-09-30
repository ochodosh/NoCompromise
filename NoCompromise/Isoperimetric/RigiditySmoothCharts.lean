module

public import NoCompromise.BV.SmoothApproxBoundary

@[expose] public section

/-!
# Smooth boundary from `C³` constant-mean-curvature charts

Blueprint `thm:isoperimetric-rigidity`, Step 2, last clause: "the bootstrap of `sec:bootstrap`
with `v_Ω` replaced by `0` makes it smooth". Chapter 28 (`prop:bootstrap-C3`) stops at `C³`;
the passage from `C³` to `C^∞` for the weak constant-mean-curvature graph equation is the
local interior-regularity statement `CMCGraphSmoothStatement`, taken here as a named
hypothesis. This file proves the global assembly: `C³` graph charts at every boundary point in
which the height solves the weak equation with one constant forcing give `HasSmoothBoundary`.
-/

noncomputable section

open Set Metric

namespace LiquidDrop

/-- Interior regularity of the weak constant-mean-curvature graph equation, `C³` to `C^∞`, as a
named hypothesis: if `f` is `C³` on a disk `B_ρ(y₀) ⊂ ℝ²` and
`∫ ∇f · ∇φ / √(1 + |∇f|²) = ∫ λ φ` for every smooth `φ` compactly supported in the disk, then
`f` is `C^∞` on the disk. Mathematically this is the iteration to all orders of the
differentiation step of `prop:bootstrap-C3` (`thm:nondiv-schauder` applied to the
differentiated equation, in the Hölder scale); it is not in Lean yet. -/
def CMCGraphSmoothStatement : Prop :=
  ∀ (lam ρ : ℝ) (y0 : EuclideanSpace ℝ (Fin 2)) (f : EuclideanSpace ℝ (Fin 2) → ℝ), 0 < ρ →
    ContDiffOn ℝ 3 f (ball y0 ρ) →
    (∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball y0 ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) / Real.sqrt (1 + ‖gradient f y‖ ^ 2)) =
        ∫ y, lam * φ y) →
    ContDiffOn ℝ (⊤ : ℕ∞) f (ball y0 ρ)

/-- Global assembly: if every boundary point of `Ω` lies in a one-sided graph chart whose height
is `C³` on a disk around the base point and solves the weak constant-mean-curvature equation
with forcing `lam` there, then `Ω` has smooth boundary, given `CMCGraphSmoothStatement`. -/
theorem hasSmoothBoundary_of_C3_charts_weak_cmc (hS : CMCGraphSmoothStatement)
    {Ω : Set AmbientSpace} {lam : ℝ}
    (h : ∀ p ∈ frontier Ω, ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧ ∃ ρ > 0,
      ContDiffOn ℝ 3 c.height (ball (graphProjectionN 2 (c.placement.symm p)) ρ) ∧
      ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ ball (graphProjectionN 2 (c.placement.symm p)) ρ →
        (∫ y, inner ℝ (gradient c.height y) (gradient φ y) /
          Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) = ∫ y, lam * φ y) :
    HasSmoothBoundary Ω := by
  apply hasSmoothBoundary_of_local_graphs
  intro x hx
  obtain ⟨c, hc, hxc, ρ, hρ, h3, hweak⟩ := h x hx
  refine ⟨c.placement, c.height, ball (graphProjectionN 2 (c.placement.symm x)) ρ, c.region,
    isOpen_ball, hS lam ρ _ c.height hρ h3 hweak, mem_ball_self hρ, c.isOpen_region, hxc, ?_⟩
  intro z hz
  exact hc z hz

end LiquidDrop
