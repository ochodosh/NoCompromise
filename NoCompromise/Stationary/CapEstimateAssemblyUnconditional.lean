module

public import NoCompromise.Capacity.HullPotentialBoundaryC2
public import NoCompromise.Classification.CapEstimateFinal
public import NoCompromise.Surface.TotalCurvatureBoundMain

@[expose] public section

/-!
# `lem:integrate-EL` and `lem:two-bounds-I` for stationary domains, unconditionally

`integrate_EL_hull` and `two_bounds_I_hull` (Stationary/CapEstimateAssembly.lean) take the `C²`
extension `g` of the capacitary potential of `K = filledHull Ω` across `∂K` as an argument, and
`two_bounds_I_hull` also takes `TotalCurvatureBound` and `CapacitaryInequalitiesStatement`. A
stationary domain has `C³` boundary (`IsStationaryDomain.boundary_C3`), so
`hullPotentialBoundaryC2` supplies `g`; the other two inputs are `total_curvature_bound_forall`
(`thm:total-curvature-bound`) and `capacitaryInequalitiesStatement`
(`thm:capacitary-inequalities`).
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology

namespace LiquidDrop

/-- Blueprint `lem:integrate-EL` (`eq:integrate-EL`) for the capacitary potential `u` of the
filled hull `K` of a stationary domain `Ω ∋ 0`, `V > 0`: some `C²` function `g` with `u = g` on
`closure Kᶜ` satisfies `λ Cap(K) - V = (4π)⁻¹ ∫_{∂K} H |∇g| dH²`, for `H` the mean curvature of
`∂K` in the `C²` charts of `int K`. The conclusion after the extension is that of
`integrate_EL_hull`. -/
theorem integrate_EL_hull_unconditional {V lam : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (h : IsStationaryDomain V lam Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {H : AmbientSpace → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
      H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      lam * capacityOf (filledHull Ω) u - V = (4 * Real.pi)⁻¹ *
        ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨g, hg, hug⟩ :=
    hullPotentialBoundaryC2 Ω h.isOpen h.isBounded h.boundary_C3 h0 u hu hh hb hinf
  exact ⟨g, hg, hug, integrate_EL_hull hV h h0 hu hh hb hinf hg hug hH⟩

/-- Blueprint `lem:two-bounds-I` (with `eq:integrate-EL-bound` of `lem:integrate-EL`),
`eq:I-bound-combined`, for the capacitary potential `u` of the filled hull `K` of a stationary
domain `Ω ∋ 0`, `V > 0`: `Cap(K) > 0`, `Per(Ω) > 0` and
`λ Cap(K) - V ≥ max {2, 16π Cap(K)²/Per(Ω) - 2}`. Exactly the conclusion of
`two_bounds_I_hull`, with no hypotheses beyond stationarity and `u` being the potential. -/
theorem two_bounds_I_hull_unconditional {V lam : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (h : IsStationaryDomain V lam Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    0 < capacityOf (filledHull Ω) u ∧ 0 < (perimeter Ω).toReal ∧
      lam * capacityOf (filledHull Ω) u - V ≥
        max 2 (16 * Real.pi * capacityOf (filledHull Ω) u ^ 2 / (perimeter Ω).toReal - 2) := by
  obtain ⟨g, hg, hug⟩ :=
    hullPotentialBoundaryC2 Ω h.isOpen h.isBounded h.boundary_C3 h0 u hu hh hb hinf
  exact two_bounds_I_hull total_curvature_bound_forall capacitaryInequalitiesStatement hV h h0
    hu hh hb hinf hg hug

end LiquidDrop
