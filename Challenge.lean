/-
Copyright (c) 2026 Otis Chodosh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# No compromise in the liquid drop model: statements

A self-contained statement, depending only on Mathlib, of the main results of
O. Chodosh and M. Gianocca, *No compromise in the liquid drop model*, arXiv:2608.11517.

This is the challenge module for `leanprover/comparator`. The theorems below are stated with
`sorry`; `Solution.lean` proves theorems with the same names and types from the rest of this
repository, and `comparator.json` lists them.

For a set `Ω ⊆ ℝ³` the liquid-drop energy is

  `𝓔(Ω) = P(Ω) + (1/2) ∫_Ω ∫_Ω |x - y|⁻¹ dx dy`,

where `P` is the De Giorgi perimeter. Both terms take values in `[0, ∞]`. The measure is
Mathlib's `volume` on `EuclideanSpace ℝ (Fin 3)`, which is Lebesgue measure. `MeasurableSet`
means Borel measurable, and `NullMeasurableSet · volume` means Lebesgue measurable.

* `main`: let `V_* = 5 (2 - 2^{2/3}) / (2^{2/3} - 1)` and `V > 0`. If `V ≤ V_*`, the minimisers
  of `𝓔` among Borel sets of volume `V` are exactly the sets that agree with a ball of volume
  `V` up to a null set. If `V > V_*`, there is no minimiser.
* `main_lebesgue`: the same statement for Lebesgue-measurable sets and competitors.
* `main_binding`: the infimum of `𝓔(E) / |E|` over Lebesgue-measurable sets with
  `0 < |E| < ∞` equals `3 (9π/5)^{1/3}`. It is attained, and every set attaining it agrees
  with a ball of volume `5/2` up to a null set.

The file ends with sanity checks on the definitions: the perimeter and Coulomb energy of a ball,
numerical bounds on `V_*`, and existence of minimizers below the threshold (so that `main` is
not vacuous).
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal symmDiff

namespace NoCompromise

/-! ## Definitions -/

/-- The ambient space `ℝ³`, with the Euclidean norm and Lebesgue measure `volume`. -/
abbrev AmbientSpace := EuclideanSpace ℝ (Fin 3)

/-- The divergence `div X = ∑ᵢ ∂ᵢ Xᵢ` of a vector field on `ℝ³`. -/
def divergence (X : AmbientSpace → AmbientSpace) (x : AmbientSpace) : ℝ :=
  ∑ i, fderiv ℝ X x (EuclideanSpace.single i 1) i

/-- The De Giorgi perimeter
`P(Ω) = sup { ∫_Ω div X : X ∈ C¹_c(ℝ³; ℝ³), |X| ≤ 1 } ∈ [0, ∞]`.
Taking `ENNReal.ofReal` of each integral does not change the supremum, because the admissible
fields are closed under `X ↦ -X` and include `X = 0`. -/
def perimeter (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  ⨆ (X : AmbientSpace → AmbientSpace)
    (_ : ContDiff ℝ 1 X)
    (_ : HasCompactSupport X)
    (_ : ∀ x, ‖X x‖ ≤ 1),
    ENNReal.ofReal (∫ x in Ω, divergence X x)

/-- The Coulomb self-energy `D(Ω) = (1/2) ∫_Ω ∫_Ω |x - y|⁻¹ dx dy ∈ [0, ∞]`. The integrand
equals `∞` on the diagonal, which is a null set of `ℝ³ × ℝ³`. -/
def coulombEnergy (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ p in Ω ×ˢ Ω, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹

/-- The liquid-drop energy `𝓔(Ω) = P(Ω) + D(Ω)`. -/
def energy (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  perimeter Ω + coulombEnergy Ω

/-- `Ω` is a Borel set of volume `V` and finite perimeter whose energy is at most that of
every Borel set of volume `V`. -/
def IsFixedVolumeMinimizer (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  MeasurableSet Ω ∧
    volume Ω = ENNReal.ofReal V ∧
    perimeter Ω < ∞ ∧
    ∀ F : Set AmbientSpace,
      MeasurableSet F → volume F = ENNReal.ofReal V → energy Ω ≤ energy F

/-- `Ω` is a Lebesgue-measurable set of volume `V` and finite perimeter whose energy is at most
that of every Lebesgue-measurable set of volume `V`. -/
def IsLebesgueFixedVolumeMinimizer (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  NullMeasurableSet Ω volume ∧
    volume Ω = ENNReal.ofReal V ∧
    perimeter Ω < ∞ ∧
    ∀ F : Set AmbientSpace,
      NullMeasurableSet F volume → volume F = ENNReal.ofReal V → energy Ω ≤ energy F

/-- `Ω` is a Borel set that agrees with a ball of volume `V` up to a null set. -/
def IsBallUpToNull (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  MeasurableSet Ω ∧
    ∃ (c : AmbientSpace) (r : ℝ),
      0 < r ∧
        volume (ball c r) = ENNReal.ofReal V ∧
        volume (Ω ∆ ball c r) = 0

/-- `Ω` is a Lebesgue-measurable set that agrees with a ball of volume `V` up to a null set. -/
def IsLebesgueBallUpToNull (V : ℝ) (Ω : Set AmbientSpace) : Prop :=
  NullMeasurableSet Ω volume ∧
    ∃ (c : AmbientSpace) (r : ℝ),
      0 < r ∧
        volume (ball c r) = ENNReal.ofReal V ∧
        volume (Ω ∆ ball c r) = 0

/-- The critical volume `V_* = 5 (2 - 2^{2/3}) / (2^{2/3} - 1)`. -/
def criticalVolume : ℝ :=
  5 * (2 - (2 : ℝ) ^ ((2 : ℝ) / 3)) / ((2 : ℝ) ^ ((2 : ℝ) / 3) - 1)

/-- The optimal energy per unit volume, `inf { 𝓔(E) / |E| : E Lebesgue measurable,
0 < |E| < ∞ } ∈ [0, ∞]`. -/
def globalEnergyRatio : ℝ≥0∞ :=
  ⨅ (E : Set AmbientSpace) (_ : NullMeasurableSet E volume)
    (_ : 0 < volume E) (_ : volume E < ∞), energy E / volume E

/-- `E` is a Lebesgue-measurable set with `0 < |E| < ∞` attaining `globalEnergyRatio`. -/
def IsGlobalRatioOptimizer (E : Set AmbientSpace) : Prop :=
  NullMeasurableSet E volume ∧ 0 < volume E ∧ volume E < ∞ ∧
    energy E / volume E = globalEnergyRatio

-- END OF DEFINITIONS (`Solution/Defs.lean` repeats everything above this line verbatim.)

/-! ## Results -/

/-- **Main theorem**, for Borel sets. For `0 < V ≤ V_*` the fixed-volume minimisers are exactly
the balls of volume `V` up to null sets; for `V > V_*` no minimiser exists. -/
theorem main (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) := by
  sorry

/-- **Main theorem**, for Lebesgue-measurable sets. -/
theorem main_lebesgue (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsLebesgueFixedVolumeMinimizer V Ω ↔ IsLebesgueBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω) := by
  sorry

/-- **Binding energy.** The optimal energy per unit volume is `3 (9π/5)^{1/3}`, it is attained,
and every optimiser is a ball of volume `5/2` up to a null set. -/
theorem main_binding :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E := by
  sorry

/-! ## Sanity checks on the definitions -/

/-- The perimeter of a ball of radius `R` is `4πR²`. -/
theorem perimeter_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    perimeter (ball c R) = ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  sorry

/-- The Coulomb energy of a ball of radius `R` is `(16π²/15) R⁵`. -/
theorem coulombEnergy_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    coulombEnergy (ball c R) = ENNReal.ofReal (16 * Real.pi ^ 2 / 15 * R ^ 5) := by
  sorry

/-- The critical volume is `V_* ≈ 3.512`. -/
theorem criticalVolume_bounds : 3.51 < criticalVolume ∧ criticalVolume < 3.52 := by
  sorry

/-- Minimizers exist for `0 < V ≤ V_*`, so the first part of `main` is not vacuous. -/
theorem exists_minimizer {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume) :
    ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω := by
  sorry

end NoCompromise
