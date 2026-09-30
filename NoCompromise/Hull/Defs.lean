module

public import NoCompromise.DeGiorgi.SmoothBoundary

@[expose] public section

/-! # The filled hull (blueprint `def:hull`) -/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- Blueprint `def:hull`: `U_∞`, realised canonically as the union of the unbounded connected
components of `(closure Ω)ᶜ`; for bounded `Ω` it is the unique unbounded component. -/
def hullExterior (Ω : Set AmbientSpace) : Set AmbientSpace :=
  {x | ¬ Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x)}

/-- Blueprint `def:hull` (`eq:hull`): the filled hull `K := ℝ³ \ U_∞`. -/
def filledHull (Ω : Set AmbientSpace) : Set AmbientSpace := (hullExterior Ω)ᶜ

end LiquidDrop
