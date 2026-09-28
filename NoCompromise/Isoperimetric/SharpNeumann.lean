import NoCompromise.Isoperimetric.Components
import NoCompromise.Isoperimetric.ABPNeumann
import NoCompromise.Value.Defs

/-!
# The sharp isoperimetric inequality from the ABP Neumann problem

Blueprint `thm:sharp-isoperimetric` follows from `prop:iso-smooth` (Isoperimetric/ABPNeumann.lean),
`cor:iso-smooth-components` (Isoperimetric/Components.lean) and the smooth approximation
passage (Isoperimetric/Sharp.lean). The only remaining hypothesis is `ABPNeumannSolvable`,
the existence assertion of `lem:abp-neumann`, which rests on `thm:boundary-neumann`
(Chapter 10). In particular `SharpIsoperimetric`, the named hypothesis of Chapters 17–18,
is a consequence of `ABPNeumannSolvable`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- `cor:iso-smooth-components`, second inequality, for every bounded open set with smooth
boundary, given `lem:abp-neumann`. -/
theorem smoothIsoperimetric_of_abpNeumann (h : ABPNeumannSolvable) : SmoothIsoperimetric :=
  smoothIsoperimetric_of_connected fun _ hGo hGb hGc hGs => iso_smooth h hGo hGb hGc hGs

/-- Blueprint `thm:sharp-isoperimetric`, given `lem:abp-neumann`. -/
theorem sharp_isoperimetric (h : ABPNeumannSolvable) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hfin : volume E < ∞) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter E :=
  sharp_isoperimetric_of_smooth (smoothIsoperimetric_of_abpNeumann h) hE hfin

/-- The named hypothesis `SharpIsoperimetric` of Chapters 17–18 follows from
`lem:abp-neumann`. -/
theorem sharpIsoperimetric_of_abpNeumann (h : ABPNeumannSolvable) : SharpIsoperimetric :=
  fun _ hE hfin => sharp_isoperimetric h hE hfin

end LiquidDrop
