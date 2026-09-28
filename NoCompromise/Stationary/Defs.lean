import NoCompromise.Surface.Geometry
import NoCompromise.Energy.CoulombDefs
import NoCompromise.Elliptic.HopfC2Boundary

/-!
# Stationary domains

Blueprint `def:stationary`. Boundary regularity uses the one-sided rigid graph
charts of `HasC1Boundary`/`HasC2Boundary`, with the height of class `C^k`.
The mean curvature is the intrinsic `meanCurvature` of `Surface/Geometry.lean`
(blueprint `conv:curvature`: outward normal, so that round spheres have
`H = 2 / R > 0`, see `meanCurvature_sphere`), computed with the outward normal
field `C1BoundaryChart.outwardNormal` of a boundary chart. The pointwise
Euler--Lagrange equation `H + v_Ω = λ` is required in *every* boundary chart
whose height is at least `C²` (so that the normal field is differentiable);
by `tangentShapeOperator_congr` the value does not depend on the chart.
-/

noncomputable section
open Set MeasureTheory
namespace LiquidDrop

/-- `C^k` boundary in the one-sided rigid graph convention of `HasC1Boundary`:
every boundary point lies in a chart for `D` whose height is `C^k`. -/
def HasCkBoundary (k : ℕ∞) (D : Set AmbientSpace) : Prop :=
  ∀ p ∈ frontier D, ∃ c : C1BoundaryChart,
    c.IsChartFor D ∧ p ∈ c.region ∧ ContDiff ℝ k c.height

theorem HasCkBoundary.hasC1Boundary {k : ℕ∞} {D : Set AmbientSpace}
    (hD : HasCkBoundary k D) : HasC1Boundary D := by
  intro p hp
  obtain ⟨c, hc, hp, _⟩ := hD p hp
  exact ⟨c, hc, hp⟩

theorem HasCkBoundary.mono {k l : ℕ∞} {D : Set AmbientSpace}
    (hD : HasCkBoundary k D) (hlk : l ≤ k) : HasCkBoundary l D := by
  intro p hp
  obtain ⟨c, hc, hp, hk⟩ := hD p hp
  exact ⟨c, hc, hp, hk.of_le (by exact_mod_cast hlk)⟩

theorem HasSmoothBoundary.hasCkBoundary {D : Set AmbientSpace}
    (hD : HasSmoothBoundary D) (k : ℕ∞) : HasCkBoundary k D := by
  intro p hp
  obtain ⟨c, hc, hp, hk⟩ := hD p hp
  exact ⟨c, hc, hp, hk.of_le (by exact_mod_cast le_top)⟩

/-- Blueprint `def:stationary`: a stationary domain of volume `V` with multiplier
`lam` is a bounded connected open set of volume `V` with `C³` boundary on which
`H + v_Ω = lam` holds pointwise, `H` being the mean curvature for the outward
normal (`conv:curvature`) and `v_Ω` the Coulomb potential (`def:coulomb`). -/
structure IsStationaryDomain (V lam : ℝ) (Ω : Set AmbientSpace) : Prop where
  isOpen : IsOpen Ω
  isConnected : IsConnected Ω
  isBounded : Bornology.IsBounded Ω
  volume_eq : volume Ω = ENNReal.ofReal V
  boundary_C3 : HasCkBoundary 3 Ω
  eulerLagrange : ∀ p ∈ frontier Ω, ∀ c : C1BoundaryChart, c.IsChartFor Ω →
    p ∈ c.region → ContDiff ℝ 2 c.height →
    meanCurvature (frontier Ω) c.outwardNormal p + (coulombPotential Ω p).toReal = lam

namespace IsStationaryDomain

variable {V lam : ℝ} {Ω : Set AmbientSpace}

theorem hasC1Boundary (h : IsStationaryDomain V lam Ω) : HasC1Boundary Ω :=
  h.boundary_C3.hasC1Boundary

theorem hasC2Boundary (h : IsStationaryDomain V lam Ω) : HasC2Boundary Ω := by
  intro p hp
  obtain ⟨c, hc, hp, hk⟩ := h.boundary_C3 p hp
  exact ⟨c, hc, hp, hk.of_le (by norm_num)⟩

/-- At every boundary point the Euler--Lagrange equation holds in some `C³` chart. -/
theorem exists_chart (h : IsStationaryDomain V lam Ω) {p : AmbientSpace}
    (hp : p ∈ frontier Ω) : ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧
      ContDiff ℝ 3 c.height ∧
      meanCurvature (frontier Ω) c.outwardNormal p + (coulombPotential Ω p).toReal = lam := by
  obtain ⟨c, hc, hpc, hk⟩ := h.boundary_C3 p hp
  exact ⟨c, hc, hpc, hk, h.eulerLagrange p hp c hc hpc (hk.of_le (by norm_num))⟩

theorem volume_toReal (h : IsStationaryDomain V lam Ω) (hV : 0 ≤ V) :
    (volume Ω).toReal = V := by
  rw [h.volume_eq, ENNReal.toReal_ofReal hV]

end IsStationaryDomain

end LiquidDrop
