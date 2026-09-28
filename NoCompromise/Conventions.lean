import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Ambient space

The ambient-space part of blueprint `conv:ambient`. Other conventions in the
blueprint will be implemented with the geometric objects to which they apply.
-/

namespace LiquidDrop

/-- The ambient Euclidean space `ℝ³`. -/
abbrev AmbientSpace := EuclideanSpace ℝ (Fin 3)

end LiquidDrop
