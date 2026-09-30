module

public import NoCompromise.Classification.Unconditional
public import NoCompromise.Classification.CapEstimateFinal
public import NoCompromise.Surface.TotalCurvatureBoundMain

@[expose] public section

/-!
# The main theorem modulo `thm:boundary-C2a` for the hull potential

`HullPotentialBoundaryC2` (a C² extension of the capacitary potential of the filled hull across
its boundary, blueprint `thm:boundary-C2a` applied in chapter 30) is the last named input:
with the total-curvature bound proved, it gives `prop:cap-estimate`, and hence `thm:main` in
the exact form of `LiquidDrop.main`.
-/

namespace LiquidDrop

/-- Blueprint `prop:cap-estimate` (`CapEstimateStatement`) modulo `thm:boundary-C2a` alone. -/
theorem capEstimateStatement_of_hullPotentialBoundaryC2 (hC2 : HullPotentialBoundaryC2) :
    CapEstimateStatement :=
  capEstimateStatement_of_boundaryC2 hC2 total_curvature_bound_forall

/-- Blueprint `thm:main` modulo `thm:boundary-C2a` for the hull potential; the conclusion is
the exact statement of `LiquidDrop.main`. -/
theorem main_of_hullPotentialBoundaryC2 (hC2 : HullPotentialBoundaryC2) (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) :=
  main_of_capEstimate (capEstimateStatement_of_hullPotentialBoundaryC2 hC2) V hV

end LiquidDrop
