import NoCompromise.Isoperimetric.ABPNeumannC1
import NoCompromise.Isoperimetric.ABPNeumannC3Local
import NoCompromise.Isoperimetric.RigidityC3

/-!
# The isoperimetric chapter without hypotheses

`ABPNeumannSolvableC3` (`lem:abp-neumann` for domains with `C³` boundary) is proved as
`abpNeumannSolvableC3` (Isoperimetric/ABPNeumannC3Local.lean). Every statement of
Isoperimetric/ComponentsC3.lean and Isoperimetric/RigidityC3.lean that takes it as a hypothesis
therefore holds unconditionally; this file records these instances with the original
conclusions. In particular:

* `isoperimetric_rigidity_unconditional`: blueprint `thm:isoperimetric-rigidity`, direct half;
* `isoperimetricRigidityStatement_holds`, `isoperimetricEqualityRegularity_holds`,
  `perimeterMinimizerSmoothBootstrap_holds`: the named predicates `IsoperimetricRigidityStatement`
  (Classification/Subcritical.lean), `IsoperimetricEqualityRegularity` (Isoperimetric/Rigidity.lean)
  and `PerimeterMinimizerSmoothBootstrap` (Isoperimetric/RigidityRegularity.lean) hold.

`thm:sharp-isoperimetric` is already stated without hypotheses as
`sharp_isoperimetric_unconditional`, and `SharpIsoperimetric` as `sharpIsoperimetric_holds`
(Isoperimetric/ABPNeumannC1.lean).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/-! ### `cor:iso-smooth-components` for `C³` domains -/

/-- Blueprint `cor:iso-smooth-components` for bounded open sets with `C³` boundary, without
hypotheses. -/
theorem iso_C3_components_unconditional
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasCkBoundary 3 S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) *
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ))
          ≤ perimeter S ∧
      volume S ^ (2 / (3 : ℝ)) ≤
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ)) :=
  iso_C3_components_of_abpNeumannSolvableC3 abpNeumannSolvableC3 hS hSb hSs

/-- Blueprint `cor:iso-smooth-components`, consequence for `C³` domains, without hypotheses:
`Per(S) ≥ (36π)^{1/3} |S|^{2/3}` for every bounded open set with `C³` boundary. -/
theorem iso_C3_bounded_unconditional
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasCkBoundary 3 S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter S :=
  iso_C3_of_abpNeumannSolvableC3 abpNeumannSolvableC3 hS hSb hSs

/-! ### `thm:isoperimetric-rigidity`, Steps 3–5 for `C³` domains -/

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 4–5 for a bounded connected open set with `C³`
boundary, without hypotheses: `Per(G)^3 ≤ 36π|G|^2` forces `G` to be a ball. -/
theorem iso_C3_rigidity_connected_unconditional {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hG : HasCkBoundary 3 G)
    (heq : (perimeter G).toReal ^ 3 ≤ 36 * Real.pi * volume.real G ^ 2) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ G = ball p r :=
  iso_C3_rigidity_connected abpNeumannSolvableC3 hGo hGb hGc hG heq

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 3–5 for a bounded open set with `C³` boundary,
without hypotheses: if `0 < |S|` and `Per(S) ≤ (36π)^{1/3} |S|^{2/3}`, then `S` is a ball. -/
theorem iso_C3_rigidity_unconditional {S : Set AmbientSpace}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S) (hSs : HasCkBoundary 3 S)
    (hpos : 0 < volume S)
    (heq : perimeter S ≤
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ S = ball p r :=
  iso_C3_rigidity abpNeumannSolvableC3 hSo hSb hSs hpos heq

/-- The `P_B(V)` form of `thm:isoperimetric-rigidity` (Steps 3–5) for `C³` domains, without
hypotheses: a bounded open set with `C³` boundary, volume `V > 0` and `Per(Ω) ≤ P_B(V)` is a
ball of radius `ballRadius V`. -/
theorem eq_ball_of_perimeter_le_ballPerimeter_C3_unconditional {V : ℝ}
    (hV : 0 < V) {Ω : Set AmbientSpace} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩs : HasCkBoundary 3 Ω) (hvol : volume Ω = ENNReal.ofReal V)
    (hP : perimeter Ω ≤ ballPerimeter V) :
    ∃ p : AmbientSpace, Ω = ball p (ballRadius V) :=
  eq_ball_of_perimeter_le_ballPerimeter_C3 abpNeumannSolvableC3 hV hΩo hΩb hΩs hvol hP

/-! ### `thm:isoperimetric-rigidity`, Steps 1–2 -/

/-- Blueprint `thm:isoperimetric-rigidity`, Step 1, first sentence, without hypotheses: an
equality set is a perimeter minimiser among Lebesgue-measurable sets of its volume. -/
theorem isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq_unconditional
    {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueFixedVolumePerimeterMinimizer (volume E).toReal E :=
  isLebesgueFixedVolumePerimeterMinimizer_of_isoperimetric_eq_C3 abpNeumannSolvableC3 hE hfin heq

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 1–2 up to `C³`, without hypotheses: for an
equality set `E` (`0 < |E| < ∞`, `Per(E) = c_I |E|^{2/3}`), the density-one representative
`Ω = E^{(1)}` is a bounded open perimeter minimiser of volume `|E|` with `C³` boundary, and
`Ω = E` almost everywhere. -/
theorem isoperimetric_equality_C3_representative_unconditional
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueFixedVolumePerimeterMinimizer (volume E).toReal (densityOne E) ∧
      IsOpen (densityOne E) ∧ Bornology.IsBounded (densityOne E) ∧
      HasCkBoundary 3 (densityOne E) ∧ densityOne E =ᵐ[volume] E :=
  isoperimetric_equality_C3_representative abpNeumannSolvableC3 hE hpos hfin heq

/-! ### `thm:isoperimetric-rigidity` -/

/-- **thm:isoperimetric-rigidity** (direct half), without hypotheses: if `0 < |E| < ∞` and
`Per(E) = (36π)^{1/3} |E|^{2/3}`, then `E` is, up to a null set, a translate of a ball of volume
`|E|`. -/
theorem isoperimetric_rigidity_unconditional
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞)
    (heq : perimeter E =
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))) :
    IsLebesgueBallUpToNull (volume E).toReal E :=
  isoperimetric_rigidity_of_abpNeumannSolvableC3 abpNeumannSolvableC3 hE hpos hfin heq

/-- Blueprint `thm:isoperimetric-rigidity` as an equivalence, for `0 < |E| < ∞`, without
hypotheses. -/
theorem isoperimetric_rigidity_iff_unconditional
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hpos : 0 < volume E)
    (hfin : volume E < ∞) :
    perimeter E =
        ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ))) ↔
      IsLebesgueBallUpToNull (volume E).toReal E :=
  isoperimetric_rigidity_iff_of_abpNeumannSolvableC3 abpNeumannSolvableC3 hE hpos hfin

/-- The `P_B(V)` form of `thm:isoperimetric-rigidity` used by `prop:classification`, without
hypotheses: a set of volume `V > 0` with `Per(E) ≤ P_B(V)` is a ball of volume `V` up to a null
set. -/
theorem isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter_unconditional
    {V : ℝ} (hV : 0 < V) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hvol : volume E = ENNReal.ofReal V)
    (hP : perimeter E ≤ ballPerimeter V) : IsLebesgueBallUpToNull V E :=
  isLebesgueBallUpToNull_of_perimeter_le_ballPerimeter_of_abpNeumannSolvableC3
    abpNeumannSolvableC3 hV hE hvol hP

/-! ### The named predicates -/

/-- `IsoperimetricRigidityStatement` (blueprint `thm:isoperimetric-rigidity`, forward direction,
in the form used by Chapters 34–35) holds. -/
theorem isoperimetricRigidityStatement_holds : IsoperimetricRigidityStatement :=
  isoperimetricRigidityStatement_of_abpNeumannSolvableC3 abpNeumannSolvableC3

/-- `IsoperimetricEqualityRegularity` (Steps 1–2 of blueprint `thm:isoperimetric-rigidity`,
with a smooth representative) holds. -/
theorem isoperimetricEqualityRegularity_holds : IsoperimetricEqualityRegularity :=
  isoperimetricEqualityRegularity_of_abpNeumannSolvableC3 abpNeumannSolvableC3

/-- `PerimeterMinimizerSmoothBootstrap` (the Coulomb-free smooth bootstrap in Step 2 of blueprint
`thm:isoperimetric-rigidity`: a bounded open perimeter minimiser of volume `V > 0` whose
boundary points are all regular and which has `C¹` boundary has smooth boundary) holds. -/
theorem perimeterMinimizerSmoothBootstrap_holds : PerimeterMinimizerSmoothBootstrap :=
  perimeterMinimizerSmoothBootstrap_of_abpNeumannSolvableC3 abpNeumannSolvableC3

end LiquidDrop
