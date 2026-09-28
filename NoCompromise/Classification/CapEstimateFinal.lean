import NoCompromise.Classification.CapEstimate
import NoCompromise.CapacitaryK.InequalitiesFinal

/-! # `prop:cap-estimate` modulo `thm:boundary-C2a` and `thm:total-curvature-bound`

`CapacitaryInequalitiesStatement` is discharged by the Chapter-31 theorem
`CapacitaryK.capacitary_inequalities_of_C2_extension_final`, so `CapEstimateStatement` rests on
`HullPotentialBoundaryC2` and `TotalCurvatureBound` alone.
-/

namespace LiquidDrop

/-- `CapacitaryInequalitiesStatement` holds (`thm:capacitary-inequalities`). -/
theorem capacitaryInequalitiesStatement : CapacitaryInequalitiesStatement :=
  fun _K hK hKconn hcompl hreg hC2 hzero _u hu hh hb hinf _g hg hug htc _H hH =>
    CapacitaryK.capacitary_inequalities_of_C2_extension_final hK hKconn hcompl hreg hC2 hzero
      hu hh hb hinf hg hug htc hH

/-- Blueprint `prop:cap-estimate` (`CapEstimateStatement`) modulo exactly
`HullPotentialBoundaryC2` (`thm:boundary-C2a`) and `TotalCurvatureBound`
(`thm:total-curvature-bound`). -/
theorem capEstimateStatement_of_boundaryC2 (hC2 : HullPotentialBoundaryC2)
    (htc : TotalCurvatureBound) : CapEstimateStatement :=
  capEstimateStatement_of_hull hC2 htc capacitaryInequalitiesStatement

end LiquidDrop

