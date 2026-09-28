import NoCompromise.Stationary.BootstrapC3Global
import NoCompromise.Stationary.MinimizerC1Holder

/-!
# The minimiser representative is a smooth stationary domain

Blueprint `prop:bootstrap-C2`, `prop:bootstrap-C3`, `cor:EL-pointwise` and
`cor:minimizer-stationary` for the fixed representative of `not:minimizer-rep`, with the
`C^{1,1/2}` boundary supplied by `thm:eps-regularity` (`MinimizerRep.hasC1HolderBoundary`).
-/

noncomputable section
open Set Metric
namespace LiquidDrop

variable {V : ℝ} {Ω : Set AmbientSpace}

/-- Blueprint `prop:bootstrap-C2`: at every boundary point of the minimiser there is a chart
whose height is globally `C²` and `C^{2,β}` near the base point, for every `0 < β < 1`. -/
theorem MinimizerRep.exists_c2Holder_chart_all (h : MinimizerRep V Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧ ContDiff ℝ 2 c.height ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
        (ball (graphProjectionN 2 (c.placement.symm p)) ρ) :=
  h.exists_c2_chart (by norm_num) (by norm_num) h.hasC1HolderBoundary hp

/-- Blueprint `prop:bootstrap-C3` (`eq:C3-boundary`): the minimiser has `C³` boundary. -/
theorem MinimizerRep.hasC3Boundary (h : MinimizerRep V Ω) : HasCkBoundary 3 Ω :=
  h.hasCkBoundary_three_of_c1Holder (by norm_num) (by norm_num) h.hasC1HolderBoundary

/-- Blueprint `cor:EL-pointwise`: `H + v_Ω = λ` at every boundary point, in a chart with
globally `C²` height (and in every such chart, `MinimizerRep.eulerLagrange_pointwise`). -/
theorem MinimizerRep.eulerLagrange_at_boundary (h : MinimizerRep V Ω) :
    ∀ p ∈ frontier Ω, ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧
      p ∈ c.region ∧ ContDiff ℝ 2 c.height ∧
      meanCurvature (frontier Ω) c.outwardNormal p + (coulombPotential Ω p).toReal =
        minimizerMultiplier V Ω :=
  (h.eulerLagrange_everywhere (by norm_num) (by norm_num) h.hasC1HolderBoundary).2

/-- Blueprint `cor:minimizer-stationary`: the minimiser representative is a stationary
domain with multiplier `λ`, and the scaling identity holds. -/
theorem MinimizerRep.isStationaryDomain (h : MinimizerRep V Ω) :
    IsStationaryDomain V (minimizerMultiplier V Ω) Ω ∧
      3 * V * minimizerMultiplier V Ω =
        2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * minimizerMultiplier V Ω =
        5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal :=
  h.isStationaryDomain_of_c1Holder (by norm_num) (by norm_num) h.hasC1HolderBoundary

end LiquidDrop
