import Mathlib
import NoCompromise.Ball.Defs
import NoCompromise.Energy.Defs
import NoCompromise.Threshold.Defs
import NoCompromise.Classification.MainOfBoundaryC2
import NoCompromise.Capacity.HullPotentialBoundaryC2

noncomputable section

open MeasureTheory Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/--
For every `V > 0`, balls are the only fixed-volume minimizers up to translation
and null sets when `V ≤ V_*`; when `V > V_*`, no minimizer exists.
-/
theorem main (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) :=
  main_of_hullPotentialBoundaryC2 hullPotentialBoundaryC2 V hV

end LiquidDrop
