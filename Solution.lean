/-
Copyright (c) 2026 Otis Chodosh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Solution.Defs
import NoCompromise.Showcase
import NoCompromise.Main
import NoCompromise.Classification.MainUnconditional

/-!
# Proofs of the challenge statements

`Solution.Defs` repeats the definitions of `Challenge.lean` verbatim, in a module with the same
imports, so that `comparator` sees the same constants in the challenge and in the solution.

Each challenge definition agrees with the definition of the same name in the `LiquidDrop`
namespace of this library by `rfl`. The three theorems then follow from `LiquidDrop.main`,
`LiquidDrop.main_statement_iff_lebesgue` and `LiquidDrop.main_binding_unconditional`.
-/

namespace NoCompromise

/-! ## The challenge definitions are the library definitions -/

theorem ambientSpace_eq : AmbientSpace = LiquidDrop.AmbientSpace := rfl

theorem divergence_eq : divergence = LiquidDrop.divergence := rfl

theorem perimeter_eq : perimeter = LiquidDrop.perimeter := rfl

theorem coulombEnergy_eq : coulombEnergy = LiquidDrop.coulombEnergy := rfl

theorem energy_eq : energy = LiquidDrop.energy := rfl

theorem isFixedVolumeMinimizer_eq :
    IsFixedVolumeMinimizer = LiquidDrop.IsFixedVolumeMinimizer := rfl

theorem isLebesgueFixedVolumeMinimizer_eq :
    IsLebesgueFixedVolumeMinimizer = LiquidDrop.IsLebesgueFixedVolumeMinimizer := rfl

theorem isBallUpToNull_eq : IsBallUpToNull = LiquidDrop.IsBallUpToNull := rfl

theorem isLebesgueBallUpToNull_eq :
    IsLebesgueBallUpToNull = LiquidDrop.IsLebesgueBallUpToNull := rfl

theorem criticalVolume_eq : criticalVolume = LiquidDrop.criticalVolume := rfl

theorem globalEnergyRatio_eq : globalEnergyRatio = LiquidDrop.globalEnergyRatio := rfl

theorem isGlobalRatioOptimizer_eq :
    IsGlobalRatioOptimizer = LiquidDrop.IsGlobalRatioOptimizer := rfl

/-! ## Results -/

theorem main (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) := by
  rw [isFixedVolumeMinimizer_eq, isBallUpToNull_eq, criticalVolume_eq]
  exact LiquidDrop.main V hV

theorem main_lebesgue (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsLebesgueFixedVolumeMinimizer V Ω ↔ IsLebesgueBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω) := by
  rw [isLebesgueFixedVolumeMinimizer_eq, isLebesgueBallUpToNull_eq, criticalVolume_eq]
  exact (LiquidDrop.main_statement_iff_lebesgue V).mp (LiquidDrop.main V hV)

theorem main_binding :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E := by
  rw [globalEnergyRatio_eq, isGlobalRatioOptimizer_eq, isLebesgueBallUpToNull_eq]
  exact LiquidDrop.main_binding_unconditional

end NoCompromise
