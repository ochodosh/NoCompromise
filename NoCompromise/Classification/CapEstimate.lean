module

public import NoCompromise.Classification.Subcritical
public import NoCompromise.Stationary.CapEstimateAssembly
public import NoCompromise.Stationary.TranslateDomain

@[expose] public section

/-! # `prop:cap-estimate` as the predicate `CapEstimateStatement`

Blueprint `prop:cap-estimate` for every bounded connected `C³` stationary domain: translate so
that `0 ∈ Ω` (`IsStationaryDomain.image_add_left`, `perimeter_image_translate`) and apply
`cap_estimate_of_stationary_of_zero_mem`. The named inputs are `HullPotentialBoundaryC2`
(`thm:boundary-C2a`), `TotalCurvatureBound` (`thm:total-curvature-bound`), and
`CapacitaryInequalitiesStatement`, the statement of the Chapter-31 theorem
`CapacitaryK.capacitary_inequalities_of_C2_extension_final` (proved on that branch from
`thm:total-curvature-bound` and the `C²` extension; not yet on `main`).
-/

noncomputable section

open MeasureTheory Set

namespace LiquidDrop

/-- Blueprint `prop:cap-estimate` (`eq:cap-estimate`), i.e. `CapEstimateStatement`, modulo
`HullPotentialBoundaryC2` (`thm:boundary-C2a`), `TotalCurvatureBound`
(`thm:total-curvature-bound`) and `CapacitaryInequalitiesStatement`
(`thm:capacitary-inequalities`). -/
theorem capEstimateStatement_of_hull (hC2 : HullPotentialBoundaryC2)
    (htc : TotalCurvatureBound) (hineq : CapacitaryInequalitiesStatement) :
    CapEstimateStatement := by
  intro V lam Ω hV h
  obtain ⟨x₀, hx₀⟩ := h.isConnected.nonempty
  have h' := h.image_add_left (-x₀)
  have h0 : (0 : AmbientSpace) ∈ (fun x => -x₀ + x) '' Ω := ⟨x₀, hx₀, neg_add_cancel x₀⟩
  have hP : perimeter ((fun x => -x₀ + x) '' Ω) = perimeter Ω :=
    perimeter_image_translate h.isOpen.measurableSet.nullMeasurableSet (-x₀)
  have hcap := cap_estimate_of_stationary_of_zero_mem hC2 htc hineq hV h' h0
  rwa [hP] at hcap

end LiquidDrop

#print axioms LiquidDrop.capEstimateStatement_of_hull
