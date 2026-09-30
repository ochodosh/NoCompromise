module

public import NoCompromise.Isoperimetric.RigidityRegularity
public import NoCompromise.Classification.Subcritical

@[expose] public section

/-!
# Isoperimetric rigidity in the form used by Chapters 34–35

The classification chapters take blueprint `thm:isoperimetric-rigidity` (forward direction) as
the named predicate `IsoperimetricRigidityStatement` (`Classification/Subcritical.lean`). This
file discharges that predicate from the hypotheses under which the theorem is proved in
`Isoperimetric/Rigidity.lean` and `Isoperimetric/RigidityRegularity.lean`.
-/

noncomputable section

open MeasureTheory

namespace LiquidDrop

/-- `IsoperimetricRigidityStatement` from `lem:abp-neumann` and Steps 1–2 of the proof
(`IsoperimetricEqualityRegularity`). -/
theorem isoperimetricRigidityStatement_of_regularity (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) : IsoperimetricRigidityStatement :=
  fun _E hE hpos hfin _hper heq => isoperimetric_rigidity hN hR hE hpos hfin heq

/-- `IsoperimetricRigidityStatement` from `lem:abp-neumann` and the smooth Coulomb-free
bootstrap `PerimeterMinimizerSmoothBootstrap`. -/
theorem isoperimetricRigidityStatement_of_smoothBootstrap (hN : ABPNeumannSolvable)
    (hS : PerimeterMinimizerSmoothBootstrap) : IsoperimetricRigidityStatement :=
  isoperimetricRigidityStatement_of_regularity hN
    (isoperimetricEqualityRegularity_of_smoothBootstrap hN hS)

end LiquidDrop
