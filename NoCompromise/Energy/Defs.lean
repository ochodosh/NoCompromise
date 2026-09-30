module

public import NoCompromise.BV.Defs
public import NoCompromise.Energy.CoulombDefs

@[expose] public section

/-!
# Energy and minimizers

Blueprint `def:energy` and both measurability formulations of `def:minimizer`.
The original showcase definitions are unchanged. In this Euclidean
measurable-space instance, `MeasurableSet` means Borel measurable, while
`NullMeasurableSet E volume` is Lebesgue measurability. The representative and
competitor bridges are proved in `Energy/NullInvariance`. Positivity of `V`
remains an external hypothesis, as in the showcase's main theorem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LiquidDrop

/-- The liquid-drop energy `𝓔(Ω) = P(Ω) + D(Ω)`. -/
def energy (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  perimeter Ω + coulombEnergy Ω

/-- A fixed-volume minimizer of the liquid-drop energy, with the showcase's conventions. -/
def IsFixedVolumeMinimizer (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  MeasurableSet Ω ∧
    volume Ω = ENNReal.ofReal V ∧
    perimeter Ω < ∞ ∧
    ∀ F : Set AmbientSpace,
      MeasurableSet F → volume F = ENNReal.ofReal V → energy Ω ≤ energy F

/-- A fixed-volume minimizer among all Lebesgue-measurable competitors.
This is the blueprint's completed-measure convention; `0 < V` is imposed separately. -/
def IsLebesgueFixedVolumeMinimizer (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  NullMeasurableSet Ω volume ∧
    volume Ω = ENNReal.ofReal V ∧
    perimeter Ω < ∞ ∧
    ∀ F : Set AmbientSpace,
      NullMeasurableSet F volume → volume F = ENNReal.ofReal V → energy Ω ≤ energy F

end LiquidDrop
