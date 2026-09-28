import NoCompromise.Isoperimetric.RigidityBootstrap
import NoCompromise.Isoperimetric.RigiditySmoothCharts
import NoCompromise.Isoperimetric.RigidityStatement

/-!
# Isoperimetric rigidity modulo `lem:abp-neumann` and `C³ → C^∞` for CMC graphs

Blueprint `thm:isoperimetric-rigidity`. Steps 1–2 are proved down to the local statement
`CMCGraphSmoothStatement` (the passage `C³ → C^∞` for the weak constant-mean-curvature graph
equation, beyond `prop:bootstrap-C3`): a perimeter minimiser with `C¹` boundary has `C³` graph
charts solving the weak equation with forcing `2 Per(Ω) / (3V)`
(`IsLebesgueFixedVolumePerimeterMinimizer.exists_C3_chart_weak_cmc`), and such charts give a
smooth boundary (`hasSmoothBoundary_of_C3_charts_weak_cmc`). Steps 3–5 are proved modulo
`ABPNeumannSolvable` (`lem:abp-neumann`).
-/

noncomputable section

open MeasureTheory

namespace LiquidDrop

/-- `PerimeterMinimizerSmoothBootstrap` from the local `C³ → C^∞` statement for CMC graphs. -/
theorem perimeterMinimizerSmoothBootstrap_of_cmcGraphSmooth (hS : CMCGraphSmoothStatement) :
    PerimeterMinimizerSmoothBootstrap :=
  fun _V _Ω hV hΩo _hb _hreg hC1 hmin =>
    hasSmoothBoundary_of_C3_charts_weak_cmc hS
      (fun _p hp => hmin.exists_C3_chart_weak_cmc hV hΩo hC1 hp)

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 1–2 (`IsoperimetricEqualityRegularity`), from
`lem:abp-neumann` and `CMCGraphSmoothStatement`. -/
theorem isoperimetricEqualityRegularity_of_cmcGraphSmooth (hN : ABPNeumannSolvable)
    (hS : CMCGraphSmoothStatement) : IsoperimetricEqualityRegularity :=
  isoperimetricEqualityRegularity_of_smoothBootstrap hN
    (perimeterMinimizerSmoothBootstrap_of_cmcGraphSmooth hS)

/-- Blueprint `thm:isoperimetric-rigidity`, direct half, from `lem:abp-neumann` and
`CMCGraphSmoothStatement`. -/
theorem isoperimetric_rigidity_of_cmcGraphSmooth (hN : ABPNeumannSolvable)
    (hS : CMCGraphSmoothStatement) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ⊤)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueBallUpToNull (volume E).toReal E :=
  isoperimetric_rigidity hN (isoperimetricEqualityRegularity_of_cmcGraphSmooth hN hS)
    hE hpos hfin heq

/-- `IsoperimetricRigidityStatement` (the form used by Chapters 34–35) from `lem:abp-neumann`
and `CMCGraphSmoothStatement`. -/
theorem isoperimetricRigidityStatement_of_cmcGraphSmooth (hN : ABPNeumannSolvable)
    (hS : CMCGraphSmoothStatement) : IsoperimetricRigidityStatement :=
  isoperimetricRigidityStatement_of_regularity hN
    (isoperimetricEqualityRegularity_of_cmcGraphSmooth hN hS)

end LiquidDrop
