import NoCompromise.Classification.MainOfBoundaryC2
import NoCompromise.Capacity.HullPotentialBoundaryC2
import NoCompromise.Nonexistence.SharpUnconditional

/-!
# The endgame, unconditionally

`hullPotentialBoundaryC2` (chapter 30 via `thm:boundary-C2a`) discharges the last named input,
so `prop:cap-estimate`, `prop:classification`, `prop:endpoint`, `cor:nonexistence`,
`prop:nonexistence-6`, `prop:nonexistence-8` and `thm:main-binding` hold with no hypotheses.
-/

namespace LiquidDrop

/-- Blueprint `prop:cap-estimate`: the capacitary estimate for every bounded connected C³
stationary domain. -/
theorem capEstimateStatement_holds : CapEstimateStatement :=
  capEstimateStatement_of_hullPotentialBoundaryC2 hullPotentialBoundaryC2

/-- Blueprint `prop:classification` (Lebesgue minimisers). -/
theorem classification_unconditional {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsLebesgueFixedVolumeMinimizer V Ω) :
    IsLebesgueBallUpToNull V Ω :=
  classification_of_capEstimate capEstimateStatement_holds hV hVc hΩ

/-- Blueprint `prop:classification` (Borel minimisers). -/
theorem classification_borel_unconditional {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume)
    {Ω : Set AmbientSpace} (hΩ : IsFixedVolumeMinimizer V Ω) : IsBallUpToNull V Ω :=
  classification_borel_of_capEstimate capEstimateStatement_holds hV hVc hΩ

/-- Blueprint `prop:endpoint`. -/
theorem endpoint_unconditional :
    valueFunction criticalVolume = energy (ballByVolume criticalVolume) ∧
      IsFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      IsLebesgueFixedVolumeMinimizer criticalVolume (ballByVolume criticalVolume) ∧
      ∀ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer criticalVolume Ω →
        IsLebesgueBallUpToNull criticalVolume Ω :=
  endpoint_of_capEstimate capEstimateStatement_holds

/-- Blueprint `cor:nonexistence` (Lebesgue minimisers). -/
theorem nonexistence_unconditional {V : ℝ} (hV : criticalVolume < V) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω :=
  nonexistence_of_capEstimate capEstimateStatement_holds hV

/-- Blueprint `cor:nonexistence` (Borel minimisers). -/
theorem nonexistence_borel_unconditional {V : ℝ} (hV : criticalVolume < V) :
    ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω :=
  nonexistence_borel_of_capEstimate capEstimateStatement_holds hV

/-- Blueprint `prop:nonexistence-6`. -/
theorem nonexistence_six_unconditional {V : ℝ} (hVstar : criticalVolume < V) (hV6 : V ≤ 6) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω :=
  nonexistence_six_of_capEstimate capEstimateStatement_holds hVstar hV6

/-- Blueprint `prop:nonexistence-8`. -/
theorem nonexistence_eight_unconditional {V : ℝ} (hV6 : 6 < V) (hV8 : V ≤ 8) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω :=
  nonexistence_eight_of_capEstimate capEstimateStatement_holds hV6 hV8

/-- Blueprint `thm:main-binding`. -/
theorem main_binding_unconditional :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E :=
  main_binding_of_capEstimate capEstimateStatement_holds

end LiquidDrop
