module

public import NoCompromise.BV.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Ball definitions

Blueprint `not:BV`. For `V > 0`, `ballRadius V` is the radius prescribed there.
The volume and perimeter formulas are subsequent proof obligations. The
showcase's `IsBallUpToNull` definition is moved unchanged; it explicitly requires
the ball's volume, independently of those future formulas. The corresponding
Lebesgue-measurable predicate and its representative bridges are given below.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/-- The radius prescribed by the blueprint for a positive volume `V`. -/
def ballRadius (V : ℝ) : ℝ := (3 * V / (4 * Real.pi)) ^ (1 / (3 : ℝ))

/-- The centered ball with the prescribed radius; its volume formula is proved later. -/
def ballByVolume (V : ℝ) : Set AmbientSpace := ball 0 (ballRadius V)

/-- The blueprint's `P_B(V)`. -/
def ballPerimeter (V : ℝ) : ℝ≥0∞ := perimeter (ballByVolume V)

/-- A measurable set that agrees almost everywhere with a ball of volume `V`. -/
def IsBallUpToNull (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  MeasurableSet Ω ∧
    ∃ (c : AmbientSpace) (r : ℝ),
      0 < r ∧
        volume (ball c r) = ENNReal.ofReal V ∧
        volume (Ω ∆ ball c r) = 0

/-- A Lebesgue-measurable set agreeing almost everywhere with a ball of volume `V`. -/
def IsLebesgueBallUpToNull (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  NullMeasurableSet Ω volume ∧
    ∃ (c : AmbientSpace) (r : ℝ),
      0 < r ∧
        volume (ball c r) = ENNReal.ofReal V ∧
        volume (Ω ∆ ball c r) = 0

theorem IsBallUpToNull.toLebesgue {V : ℝ} {Ω : Set AmbientSpace}
    (hΩ : IsBallUpToNull V Ω) : IsLebesgueBallUpToNull V Ω :=
  ⟨hΩ.1.nullMeasurableSet, hΩ.2⟩

theorem isBallUpToNull_iff_lebesgue (V : ℝ) (Ω : Set AmbientSpace) (hΩ : MeasurableSet Ω) :
    IsBallUpToNull V Ω ↔ IsLebesgueBallUpToNull V Ω := by
  exact ⟨IsBallUpToNull.toLebesgue, fun h => ⟨hΩ, h.2⟩⟩

theorem isLebesgueBallUpToNull_congr_ae (V : ℝ) {E F : Set AmbientSpace}
    (hEF : E =ᵐ[volume] F) : IsLebesgueBallUpToNull V E ↔ IsLebesgueBallUpToNull V F := by
  have hm : NullMeasurableSet E volume ↔ NullMeasurableSet F volume :=
    ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩
  have hd (c : AmbientSpace) (r : ℝ) :
      volume (E ∆ ball c r) = volume (F ∆ ball c r) :=
    measure_congr (hEF.symmDiff (Filter.EventuallyEq.refl _ _))
  simp only [IsLebesgueBallUpToNull, hm, hd]

theorem IsLebesgueBallUpToNull.toBorel {V : ℝ} {Ω : Set AmbientSpace}
    (hΩ : IsLebesgueBallUpToNull V Ω) : IsBallUpToNull V (toMeasurable volume Ω) := by
  apply (isBallUpToNull_iff_lebesgue V _ (measurableSet_toMeasurable _ _)).mpr
  exact (isLebesgueBallUpToNull_congr_ae V hΩ.1.toMeasurable_ae_eq).mpr hΩ

end LiquidDrop
