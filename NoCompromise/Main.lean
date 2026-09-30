module

public import NoCompromise.Ball.Defs
public import NoCompromise.Energy.NullInvariance
public import NoCompromise.Threshold.Defs
public import NoCompromise.Classification.Endpoint
public import NoCompromise.Nonexistence.Sharp
public import NoCompromise.Nonexistence.Slicing
public import NoCompromise.Value.Subadditivity
public import NoCompromise.Threshold.Comparison

@[expose] public section

/-!
# Assembly of the main theorem

Blueprint Chapter 37 (`ch:assembly`), `thm:main`.

* `classification_iff_lebesgue`, `main_statement_iff_lebesgue`: the Borel and Lebesgue
  formulations of the target statement are equivalent.
* `nonexistence`, `nonexistence_borel`: blueprint `cor:nonexistence` for fixed-volume
  minimisers. The algebraic core `nonexistence_above_threshold_of_slicing`
  (Nonexistence/Sharp.lean) is applied to the bounded open `C¹` representative
  `densityOne Ω` (`not:minimizer-rep`), with `eq:slice-coulomb` from `slicing_inequality`,
  `eq:scaling-identity` from `cor:minimizer-stationary`, `lem:two-ball-comparison` from
  `two_ball_lambda_bound`, `z_small`, `lem:subadditivity` and `prop:two-ball`, `δ ≥ 0` from
  `SharpIsoperimetric`, boundary regularity from the proved `prop:no-singular-points`, and
  `eq:cap-estimate` from the named hypothesis `CapEstimateStatement`.
* `main_of_classification_of_nonexistence`: `thm:main` from `prop:classification` (`hclass`)
  and `cor:nonexistence` (`hnon`), via `prop:existence-subcritical` and `prop:endpoint`.
* `main_of_sharp_of_capEstimate_of_rigidity`: `thm:main` modulo `SharpIsoperimetric`
  (`thm:sharp-isoperimetric`), `CapEstimateStatement` (`prop:cap-estimate`) and
  `IsoperimetricRigidityStatement` (`thm:isoperimetric-rigidity`).
* `main_of_abpNeumann_of_regularity_of_capEstimate`: `thm:main` modulo `ABPNeumannSolvable`
  (`lem:abp-neumann`), `IsoperimetricEqualityRegularity` (Steps 1–2 of
  `thm:isoperimetric-rigidity`) and `CapEstimateStatement` (`prop:cap-estimate`).

The conclusions are verbatim the statement of `LiquidDrop.main` in the showcase, which is
not imported here and remains unfinished.
-/

open MeasureTheory

namespace LiquidDrop

/-- Classification of all minimizers is equivalent with either measurability convention. -/
theorem classification_iff_lebesgue (V : ℝ) :
    (∀ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ↔
      ∀ Ω : Set AmbientSpace,
        IsLebesgueFixedVolumeMinimizer V Ω ↔ IsLebesgueBallUpToNull V Ω := by
  constructor
  · intro h Ω
    constructor
    · intro hΩ
      have hball := ((h (toMeasurable volume Ω)).mp hΩ.toBorel).toLebesgue
      exact (isLebesgueBallUpToNull_congr_ae V hΩ.1.toMeasurable_ae_eq).mp hball
    · intro hΩ
      have hmin := ((h (toMeasurable volume Ω)).mpr hΩ.toBorel).toLebesgue
      exact (isLebesgueFixedVolumeMinimizer_congr_ae V hΩ.1.toMeasurable_ae_eq).mp hmin
  · intro h Ω
    constructor
    · intro hΩ
      exact (isBallUpToNull_iff_lebesgue V Ω hΩ.1).mpr ((h Ω).mp hΩ.toLebesgue)
    · intro hΩ
      exact (isFixedVolumeMinimizer_iff_lebesgue V Ω hΩ.1).mpr ((h Ω).mpr hΩ.toLebesgue)

/-- The two full target propositions are equivalent, without assuming either is proved.
This applies in particular at every positive volume appearing in blueprint `thm:main`. -/
theorem main_statement_iff_lebesgue (V : ℝ) :
    ((V ≤ criticalVolume →
        ∀ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
      (criticalVolume < V → ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω)) ↔
    ((V ≤ criticalVolume →
        ∀ Ω : Set AmbientSpace,
          IsLebesgueFixedVolumeMinimizer V Ω ↔ IsLebesgueBallUpToNull V Ω) ∧
      (criticalVolume < V → ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω)) := by
  rw [classification_iff_lebesgue, exists_fixedVolumeMinimizer_iff_lebesgue]

/-! ## Blueprint `cor:nonexistence` for fixed-volume minimisers -/

section Nonexistence

open Set Metric
open scoped ENNReal

/-- Blueprint `cor:nonexistence`: no fixed-volume minimiser (Lebesgue-measurable convention)
exists at any volume `V > V_*`, modulo `thm:sharp-isoperimetric` (`SharpIsoperimetric`) and
`prop:cap-estimate` (`CapEstimateStatement`). Boundary regularity of the representative is the
proved `prop:no-singular-points` (`noSingularPointsStatement`). -/
theorem nonexistence (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement) {V : ℝ}
    (hV : criticalVolume < V) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω := by
  rintro ⟨Ω₀, hΩ₀⟩
  have hV0 : 0 < V := criticalVolume_pos.trans hV
  have h : MinimizerRep V (densityOne Ω₀) := (hΩ₀.minimizerRep_densityOne noSingularPointsStatement hV0).1
  generalize densityOne Ω₀ = Ω at h
  have hmeas : MeasurableSet Ω := h.isOpen.measurableSet
  have hmin : IsFixedVolumeMinimizer V Ω :=
    (isFixedVolumeMinimizer_iff_lebesgue V Ω hmeas).mpr h.minimizer
  have hvolR : (volume Ω).toReal = V := h.volume_toReal
  have hstat := h.isStationaryDomain
  -- `lem:ball-perimeter` data for `B_V`
  have hPBpos : 0 < (ballPerimeter V).toReal :=
    ENNReal.toReal_pos (ballPerimeter_pos hV0).ne' (ballPerimeter_lt_top hV0).ne
  have hR : 0 < ballRadius V := ballRadius_pos hV0
  have hPBR : (ballPerimeter V).toReal = 4 * Real.pi * ballRadius V ^ 2 :=
    ballPerimeter_toReal_eq_radius hV0
  -- the isoperimetric inequality gives `P_B(V) ≤ Per(Ω)`, i.e. `δ ≥ 0` (`not:z-delta`)
  have hisoP : ballPerimeter V ≤ perimeter Ω := by
    have := hiso.ballPerimeter_le h.nullMeasurableSet h.volume_lt_top
      (by rw [h.volume_eq]; exact ENNReal.ofReal_pos.mpr hV0)
    rwa [hvolR] at this
  have hPBP : (ballPerimeter V).toReal ≤ (perimeter Ω).toReal :=
    ENNReal.toReal_mono h.perimeter_lt_top.ne hisoP
  have hratio : 1 ≤ (perimeter Ω).toReal / (ballPerimeter V).toReal :=
    (one_le_div hPBpos).mpr hPBP
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ,
      z = Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal) := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by
    have := Real.sqrt_le_sqrt hratio
    rw [Real.sqrt_one, ← hzdef] at this
    exact this
  have hδ : 0 ≤ z - 1 := by linarith
  have hz : z = 1 + (z - 1) := by ring
  -- the identities `eq:z-identities`
  have hz2 : (perimeter Ω).toReal = (ballPerimeter V).toReal * z ^ 2 := by
    rw [hzdef, Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      mul_div_cancel₀ _ hPBpos.ne']
  have hsqrt : Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) = ballRadius V * z := by
    have hpi : (4 * Real.pi) ≠ 0 := by positivity
    have hsq : (perimeter Ω).toReal / (4 * Real.pi) = (ballRadius V * z) ^ 2 := by
      rw [div_eq_iff hpi, hz2, hPBR]
      ring
    rw [hsq, Real.sqrt_sq (mul_nonneg hR.le (by linarith))]
  -- minimality against two balls of volume `V/2` (`prop:two-ball`)
  have hEm : energy Ω ≤ valueFunction V :=
    le_iInf fun F => le_iInf fun hF => le_iInf fun hvol => h.le_energy hF hvol
  have hsub : valueFunction V ≤ 2 * energy (ballByVolume (V / 2)) := by
    have h2 : 0 < V / 2 := half_pos hV0
    have := valueFunction_add_le h2 h2
    rw [add_halves] at this
    refine this.trans ?_
    rw [two_mul]
    exact add_le_add (valueFunction_le_ball h2) (valueFunction_le_ball h2)
  have hEcomp : energy Ω ≤ ENNReal.ofReal (twoBallL V / 5) * ballPerimeter V := by
    rw [twoBallL, ← two_ball_energy_eq_L hV0]
    exact hEm.trans hsub
  have hcomp : (energy Ω).toReal ≤ twoBallL V / 5 * (ballPerimeter V).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ballPerimeter_lt_top hV0).ne) hEcomp
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg (twoBallL_pos hV0).le (by norm_num))] at this
    exact this
  have hPE : (perimeter Ω).toReal ≤ (energy Ω).toReal :=
    ENNReal.toReal_mono h.energy_lt_top.ne
      (show perimeter Ω ≤ perimeter Ω + coulombEnergy Ω from le_add_right le_rfl)
  refine nonexistence_above_threshold_of_slicing Ω hmeas h.volume_lt_top.ne
    (δ := z - 1) (z := z) (lam := minimizerMultiplier V Ω) (P := (perimeter Ω).toReal)
    (by rw [hvolR]; exact hV) ?_ hδ hz ?_ ?_ ?_
  · intro ν hν
    have hν1 : ‖ν‖ = 1 := by simpa [mem_sphere_iff_norm] using hν
    filter_upwards [slicing_inequality hmin h.bounded hν1] with ℓ hℓ
    exact hℓ.2
  · intro h8
    rw [hvolR] at h8
    exact (z_small hPBpos h8 hz2 hPE hcomp).2.2.2
  · intro _
    rw [hvolR]
    exact two_ball_lambda_bound hV0 hR hz1 (radius_mul_ballPerimeter hV0) hstat.2.2 hz2
      hsqrt hcomp
  · rw [hvolR]
    exact hcap V _ Ω hV0 hstat.1

/-- Blueprint `cor:nonexistence` in the Borel convention of `thm:main`. -/
theorem nonexistence_borel (hiso : SharpIsoperimetric) (hcap : CapEstimateStatement) {V : ℝ}
    (hV : criticalVolume < V) : ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω := by
  rw [exists_fixedVolumeMinimizer_iff_lebesgue]
  exact nonexistence hiso hcap hV

end Nonexistence

/-! ## Blueprint `thm:main` -/

/-- Blueprint `thm:main`, assembled as in `ch:assembly` from the classification
`prop:classification` (`hclass`) and nonexistence `cor:nonexistence` (`hnon`).
For `0 < V < V_*`, `prop:existence-subcritical` and `prop:classification` give
`m(V) = 𝓔(B_V)` (`valueFunction_eq_ball_of_classification`); at `V = V_*` this is
`prop:endpoint` (`endpoint_of_classification`). Hence every translate of `B_V` up to null
sets is a minimiser, and `prop:classification` gives the converse. -/
theorem main_of_classification_of_nonexistence (hiso : SharpIsoperimetric)
    (hclass : ∀ V : ℝ, 0 < V → V ≤ criticalVolume → ∀ Ω : Set AmbientSpace,
      IsLebesgueFixedVolumeMinimizer V Ω → IsLebesgueBallUpToNull V Ω)
    (hnon : ∀ V : ℝ, criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω)
    (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) := by
  refine ⟨fun hVc Ω => ?_, fun hVc => ?_⟩
  · have hm : valueFunction V = energy (ballByVolume V) := by
      rcases hVc.lt_or_eq with hlt | heq
      · exact valueFunction_eq_ball_of_classification hiso hclass hV hlt
      · rw [heq]
        exact (endpoint_of_classification hiso hclass).1
    constructor
    · intro hΩ
      exact (isBallUpToNull_iff_lebesgue V Ω hΩ.1).mpr (hclass V hV hVc Ω hΩ.toLebesgue)
    · exact isFixedVolumeMinimizer_of_ballUpToNull hV hm
  · rw [exists_fixedVolumeMinimizer_iff_lebesgue]
    exact hnon V hVc

/-- Blueprint `thm:main`, modulo `thm:sharp-isoperimetric` (`SharpIsoperimetric`),
`prop:cap-estimate` (`CapEstimateStatement`) and `thm:isoperimetric-rigidity`
(`IsoperimetricRigidityStatement`): `prop:classification` is `classification`,
`cor:nonexistence` is `nonexistence`. -/
theorem main_of_sharp_of_capEstimate_of_rigidity (hiso : SharpIsoperimetric)
    (hcap : CapEstimateStatement) (hrig : IsoperimetricRigidityStatement)
    (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) :=
  main_of_classification_of_nonexistence hiso
    (fun _ hV' hVc _ hΩ => classification hiso hcap hrig hV' hVc hΩ)
    (fun _ hV' => nonexistence hiso hcap hV') V hV

/-- Blueprint `thm:main`, modulo `lem:abp-neumann` (`ABPNeumannSolvable`, which gives
`thm:sharp-isoperimetric`), Steps 1–2 of `thm:isoperimetric-rigidity`
(`IsoperimetricEqualityRegularity`) and `prop:cap-estimate` (`CapEstimateStatement`). -/
theorem main_of_abpNeumann_of_regularity_of_capEstimate (hN : ABPNeumannSolvable)
    (hR : IsoperimetricEqualityRegularity) (hcap : CapEstimateStatement)
    (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω) :=
  main_of_sharp_of_capEstimate_of_rigidity (sharpIsoperimetric_of_abpNeumann hN) hcap
    (isoperimetricRigidityStatement_of_abpNeumann hN hR) V hV

end LiquidDrop

#print axioms LiquidDrop.classification_iff_lebesgue
#print axioms LiquidDrop.main_statement_iff_lebesgue
#print axioms LiquidDrop.nonexistence
#print axioms LiquidDrop.nonexistence_borel
#print axioms LiquidDrop.main_of_classification_of_nonexistence
#print axioms LiquidDrop.main_of_sharp_of_capEstimate_of_rigidity
#print axioms LiquidDrop.main_of_abpNeumann_of_regularity_of_capEstimate
