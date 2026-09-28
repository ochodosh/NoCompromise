import NoCompromise.Binding.Ratio
import NoCompromise.Binding.RelaxedAttained
import NoCompromise.Main

/-!
# The binding main theorem

Blueprint Chapter 38, `thm:main-binding`: the global energy-to-volume ratio infimum
`e_* = inf {𝓔(E)/|E| : 0 < |E| < ∞}` equals `3 (9π/5)^{1/3}`, it is attained, and every
optimiser is a translate of a ball of volume `5/2` up to a Lebesgue-null set.

In `main_binding_of_main_of_attained` the main theorem `thm:main` enters as the hypothesis `hmain` (verbatim the statement of
`LiquidDrop.main`), and `lem:relaxed-attained` as the hypothesis `hatt`, which through
`lem:stabilization` (`exists_isGlobalRatioOptimizer_of_attained`) gives an optimiser.
By `lem:ratio-is-fixed` an optimiser `E` is a fixed-volume minimiser at `M = |E|`, so
`hmain` forces `M ≤ V_*` and makes `E` a ball of volume `M` up to translation and null sets;
comparing with the competitor `B_{5/2}` and `lem:optimal-ball-volume` then forces `M = 5/2`
and gives the value `eq:e-star-value`.

`main_binding` discharges `hmain` by `main_of_sharp_of_capEstimate_of_rigidity` and `hatt` by
`relaxed_attained`, so it depends only on `SharpIsoperimetric`, `CapEstimateStatement` and
`IsoperimetricRigidityStatement`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal symmDiff

namespace LiquidDrop

/-- The energy of a positive-volume ball is finite. -/
theorem binding_energy_ballByVolume_ne_top {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) ≠ ∞ := by
  rw [energy_ballByVolume hV]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballPerimeter_lt_top hV).ne

/-- The extended-real ball ratio `𝓔(B_V)/|B_V|` is the real ball ratio of
`lem:optimal-ball-volume`. -/
theorem binding_ball_ratio_eq_ofReal {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) / ENNReal.ofReal V =
      ENNReal.ofReal ((energy (ballByVolume V)).toReal / V) := by
  rw [ENNReal.ofReal_div_of_pos hV, ENNReal.ofReal_toReal (binding_energy_ballByVolume_ne_top hV)]

/-- The core of `thm:main-binding`: from `thm:main` (hypothesis `hmain`), every global ratio
optimiser is a ball of volume `5/2` up to translation and null sets, and the global ratio
infimum is the ratio of `B_{5/2}`. -/
theorem IsGlobalRatioOptimizer.binding_of_main
    (hmain : ∀ V : ℝ, 0 < V →
      (V ≤ criticalVolume →
        ∀ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
      (criticalVolume < V → ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω))
    {E : Set AmbientSpace} (hE : IsGlobalRatioOptimizer E) :
    IsLebesgueBallUpToNull (5 / 2) E ∧
      globalEnergyRatio = ENNReal.ofReal ((energy (ballByVolume (5 / 2))).toReal / (5 / 2)) := by
  set M : ℝ := (volume E).toReal with hMdef
  have hM : 0 < M := ENNReal.toReal_pos hE.2.1.ne' hE.2.2.1.ne
  have hmin : IsLebesgueFixedVolumeMinimizer M E := hE.isLebesgueFixedVolumeMinimizer
  have hmainM := (main_statement_iff_lebesgue M).mp (hmain M hM)
  have hMc : M ≤ criticalVolume := le_of_not_gt fun hlt => hmainM.2 hlt ⟨E, hmin⟩
  have hball : IsLebesgueBallUpToNull M E := ((hmainM.1 hMc) E).mp hmin
  -- The ratio of `E` is the ratio of `B_M`.
  have hratioE : globalEnergyRatio =
      ENNReal.ofReal ((energy (ballByVolume M)).toReal / M) := by
    rw [← hE.2.2.2, hball.energy_eq hM,
      hball.volume_eq, binding_ball_ratio_eq_ofReal hM]
  -- The ball `B_{5/2}` is a competitor for the global infimum.
  have h52 : (0 : ℝ) < 5 / 2 := by norm_num
  have hcomp : globalEnergyRatio ≤
      ENNReal.ofReal ((energy (ballByVolume (5 / 2))).toReal / (5 / 2)) := by
    have h := globalEnergyRatio_le
      (show NullMeasurableSet (ballByVolume (5 / 2)) volume from
        measurableSet_ball.nullMeasurableSet)
      (by rw [volume_ballByVolume h52]; exact ENNReal.ofReal_pos.mpr h52)
      (by rw [volume_ballByVolume h52]; exact ENNReal.ofReal_lt_top)
    rwa [volume_ballByVolume h52, binding_ball_ratio_eq_ofReal h52] at h
  have hnn : 0 ≤ (energy (ballByVolume (5 / 2))).toReal / (5 / 2) :=
    div_nonneg ENNReal.toReal_nonneg h52.le
  have hle : (energy (ballByVolume M)).toReal / M ≤
      (energy (ballByVolume (5 / 2))).toReal / (5 / 2) := by
    rw [hratioE] at hcomp
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hcomp
  have hMeq : M = 5 / 2 :=
    (ball_energy_ratio_eq_min_iff hM).mp (le_antisymm hle (ball_energy_ratio_min hM))
  rw [hMeq] at hball hratioE
  exact ⟨hball, hratioE⟩

/-- Blueprint `thm:main-binding`, from `thm:main` (hypothesis `hmain`, verbatim the statement
of `LiquidDrop.main`) and `lem:relaxed-attained` (hypothesis `hatt`): the global ratio infimum
`e_*` equals `3 (9π/5)^{1/3}` (`eq:e-star-value`), it is attained, and every optimiser is a
translate of a ball of volume `5/2` up to a Lebesgue-null set. -/
theorem main_binding_of_main_of_attained
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E)
    (hmain : ∀ V : ℝ, 0 < V →
      (V ≤ criticalVolume →
        ∀ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
      (criticalVolume < V → ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω)) :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E := by
  obtain ⟨E, hE⟩ := exists_isGlobalRatioOptimizer_of_attained hatt
  refine ⟨?_, ⟨E, hE⟩, fun F hF => (hF.binding_of_main hmain).1⟩
  rw [(hE.binding_of_main hmain).2, optimal_ball_volume.1]

/-- Blueprint `thm:main-binding` with `thm:main` supplied by
`main_of_sharp_of_capEstimate_of_rigidity`: modulo `lem:relaxed-attained` (`hatt`),
`SharpIsoperimetric` (`thm:sharp-isoperimetric`), `CapEstimateStatement` (`prop:cap-estimate`)
and `IsoperimetricRigidityStatement` (`thm:isoperimetric-rigidity`). -/
theorem main_binding_of_attained (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement)
    (hrig : IsoperimetricRigidityStatement)
    (hatt : ∀ A : ℝ, 0 < A → ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E) :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E :=
  main_binding_of_main_of_attained hatt (main_of_sharp_of_capEstimate_of_rigidity hiso hcap hrig)

/-- Blueprint `thm:main-binding`, with `lem:relaxed-attained` supplied by `relaxed_attained`:
modulo `SharpIsoperimetric` (`thm:sharp-isoperimetric`), `CapEstimateStatement`
(`prop:cap-estimate`) and `IsoperimetricRigidityStatement` (`thm:isoperimetric-rigidity`). -/
theorem main_binding (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement)
    (hrig : IsoperimetricRigidityStatement) :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E :=
  main_binding_of_attained hiso hcap hrig fun _ hA => relaxed_attained hiso hA

/-- Blueprint `thm:main-binding` modulo `ABPNeumannSolvable` (`lem:abp-neumann`),
`IsoperimetricEqualityRegularity` (Steps 1–2 of `thm:isoperimetric-rigidity`) and
`CapEstimateStatement` (`prop:cap-estimate`). -/
theorem main_binding_of_abpNeumann (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) (hcap : CapEstimateStatement) :
    globalEnergyRatio = ENNReal.ofReal (3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ))) ∧
      (∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E) ∧
      ∀ E : Set AmbientSpace, IsGlobalRatioOptimizer E → IsLebesgueBallUpToNull (5 / 2) E :=
  main_binding (sharpIsoperimetric_of_abpNeumann hN) hcap
    (isoperimetricRigidityStatement_of_abpNeumann hN hR)

end LiquidDrop

#print axioms LiquidDrop.main_binding_of_main_of_attained
#print axioms LiquidDrop.main_binding_of_attained
#print axioms LiquidDrop.main_binding
#print axioms LiquidDrop.main_binding_of_abpNeumann
