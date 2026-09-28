import NoCompromise.Conventions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Threshold constants

Blueprint `def:threshold`. The definition of `criticalVolume` is the original
showcase definition; `Threshold/Algebra` proves its equivalent formula in `q`.
-/

noncomputable section

namespace LiquidDrop

/-- The positive real cube root of two, denoted `q` in the blueprint. -/
def q : ℝ := (2 : ℝ) ^ (1 / (3 : ℝ))

/-- The critical volume `V_* = 5 (2 - 2^(2/3)) / (2^(2/3) - 1)`. -/
def criticalVolume : ℝ :=
  5 * (2 - (2 : ℝ) ^ ((2 : ℝ) / 3)) / ((2 : ℝ) ^ ((2 : ℝ) / 3) - 1)

end LiquidDrop
