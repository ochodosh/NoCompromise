module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The model quadratic forms of `eq:morse-normal-form`
-/

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Model quadratic forms of `eq:morse-normal-form`: index `0`, `1`, and (for every other
value, in particular `2`) the negative definite form. -/
noncomputable def morseModel (k : ℕ) (y : E2) : ℝ :=
  if k = 0 then y 0 ^ 2 + y 1 ^ 2 else if k = 1 then y 0 ^ 2 - y 1 ^ 2
    else -(y 0 ^ 2) - y 1 ^ 2

end LiquidDrop
