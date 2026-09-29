/-
Copyright (c) 2026 Otis Chodosh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Solution.Defs
import NoCompromise.Showcase
import NoCompromise.Main
import NoCompromise.Classification.MainUnconditional
import NoCompromise.Ball.Perimeter
import NoCompromise.Ball.Potential

/-!
# Proofs of the challenge statements

`Solution.Defs` repeats the definitions of `Challenge.lean` verbatim, in a module with the same
imports, so that `comparator` sees the same constants in the challenge and in the solution.

Each challenge definition agrees with the definition of the same name in the `LiquidDrop`
namespace of this library by `rfl`. The three theorems then follow from `LiquidDrop.main`,
`LiquidDrop.main_statement_iff_lebesgue` and `LiquidDrop.main_binding_unconditional`.
-/

open MeasureTheory Metric
open scoped ENNReal symmDiff

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

/-! ## Sanity checks -/

theorem perimeter_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    perimeter (ball c R) = ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  rw [perimeter_eq]
  exact LiquidDrop.perimeter_ball c hR

theorem coulombEnergy_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    coulombEnergy (ball c R) = ENNReal.ofReal (16 * Real.pi ^ 2 / 15 * R ^ 5) := by
  rw [coulombEnergy_eq]
  exact LiquidDrop.coulombEnergy_ball c hR

theorem criticalVolume_bounds : 3.51 < criticalVolume ∧ criticalVolume < 3.52 := by
  have h3 : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  unfold criticalVolume
  set a := (2 : ℝ) ^ ((2 : ℝ) / 3)
  have ha : 0 < a := by positivity
  have hlo : 1.587 < a := by
    by_contra h
    have : a ^ 3 ≤ 1.587 ^ 3 := pow_le_pow_left₀ ha.le (not_lt.mp h) 3
    norm_num at this
    linarith
  have hhi : a < 1.5875 := by
    by_contra h
    have : 1.5875 ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by norm_num) (not_lt.mp h) 3
    norm_num at this
    linarith
  have hd : 0 < a - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]
    linarith
  · rw [div_lt_iff₀ hd]
    linarith

theorem exists_minimizer {V : ℝ} (hV : 0 < V) (hVc : V ≤ criticalVolume) :
    ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω := by
  refine ⟨ball 0 (LiquidDrop.ballRadius V), ((main V hV).1 hVc _).mpr ?_⟩
  exact ⟨measurableSet_ball, 0, LiquidDrop.ballRadius V, LiquidDrop.ballRadius_pos hV,
    LiquidDrop.volume_ballByVolume hV, by simp⟩

end NoCompromise
