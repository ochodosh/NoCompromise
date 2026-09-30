module

public import NoCompromise.Energy.Defs
public import NoCompromise.Energy.Coulomb
public import NoCompromise.DeGiorgi.SmoothBoundary

@[expose] public section

/-!
# The fixed minimizer representative

Blueprint `not:minimizer-rep`. The bounded open representative with compact
`C^{1,1/2}` boundary is produced in earlier chapters; here it is recorded as a
bundle of hypotheses together with the elementary consequences used by the
Euler--Lagrange chapter.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- Blueprint `not:minimizer-rep`: the fixed bounded open representative of a
fixed-volume minimizer, with its `C¹` boundary. -/
structure MinimizerRep (V : ℝ) (Ω : Set AmbientSpace) : Prop where
  volume_pos : 0 < V
  isOpen : IsOpen Ω
  bounded : Bornology.IsBounded Ω
  c1Boundary : HasC1Boundary Ω
  minimizer : IsLebesgueFixedVolumeMinimizer V Ω

namespace MinimizerRep

variable {V : ℝ} {Ω : Set AmbientSpace}

theorem nullMeasurableSet (h : MinimizerRep V Ω) : NullMeasurableSet Ω volume :=
  h.minimizer.1

theorem volume_eq (h : MinimizerRep V Ω) : volume Ω = ENNReal.ofReal V :=
  h.minimizer.2.1

theorem perimeter_lt_top (h : MinimizerRep V Ω) : perimeter Ω < ∞ :=
  h.minimizer.2.2.1

theorem le_energy (h : MinimizerRep V Ω) {F : Set AmbientSpace}
    (hF : NullMeasurableSet F volume) (hFV : volume F = ENNReal.ofReal V) :
    energy Ω ≤ energy F :=
  h.minimizer.2.2.2 F hF hFV

theorem hasLocallyFinitePerimeter (h : MinimizerRep V Ω) : HasLocallyFinitePerimeter Ω :=
  h.c1Boundary.hasLocallyFinitePerimeter h.isOpen

theorem volume_lt_top (h : MinimizerRep V Ω) : volume Ω < ∞ :=
  h.bounded.measure_lt_top

theorem coulombEnergy_lt_top (h : MinimizerRep V Ω) : coulombEnergy Ω < ∞ :=
  LiquidDrop.coulombEnergy_lt_top Ω h.volume_lt_top

theorem energy_lt_top (h : MinimizerRep V Ω) : energy Ω < ∞ :=
  ENNReal.add_lt_top.mpr ⟨h.perimeter_lt_top, h.coulombEnergy_lt_top⟩

theorem volume_toReal (h : MinimizerRep V Ω) : (volume Ω).toReal = V := by
  rw [h.volume_eq, ENNReal.toReal_ofReal h.volume_pos.le]

end MinimizerRep

end LiquidDrop
