module

public import NoCompromise.Classification.Unconditional

@[expose] public section

/-!
# `lem:two-ball-comparison`, `prop:nonexistence-6`, `prop:nonexistence-8` for minimisers

The algebraic cores in Nonexistence/Sharp.lean take the geometric inputs as named hypotheses:
`two_ball_lambda_bound` and `z_small` (`lem:two-ball-comparison`) take `lem:ball-perimeter`,
`prop:scaling-identity`, the identities `eq:z-identities` and minimality against two balls of
volume `V/2` (`prop:two-ball`); `nonexistence_six` and `nonexistence_eight` take in addition
`δ ≥ 0` and the capacitary lower bound `eq:cap-estimate`.

For a fixed-volume minimiser all of these are proved except `eq:cap-estimate`:

* the bounded open `C¹` representative `densityOne Ω₀` (`MinimizerRep`,
  `IsLebesgueFixedVolumeMinimizer.minimizerRep_densityOne` with `noSingularPointsStatement`);
* `prop:scaling-identity` in the form `3Vλ = 5𝓔(Ω) − 3Per(Ω)` with `λ = minimizerMultiplier V Ω`
  (`MinimizerRep.isStationaryDomain`, `cor:minimizer-stationary`);
* `lem:ball-perimeter` (`radius_mul_ballPerimeter`, `ballPerimeter_toReal_eq_radius`);
* `eq:z-identities` for `z = √(Per(Ω)/P_B(V))`, with `z ≥ 1` from `thm:sharp-isoperimetric`
  (`sharpIsoperimetric_holds`);
* `𝓔(Ω) ≤ m(V) ≤ 2𝓔(B_{V/2}) = (L/5) P_B(V)` (`valueFunction_add_le`, `valueFunction_le_ball`,
  `two_ball_energy_eq_L`, i.e. `lem:subadditivity` and `prop:two-ball`);
* `δ ≥ 0` (`isoDeficit_nonneg_unconditional`, `not:z-delta`).

`eq:cap-estimate` is `CapEstimateStatement` (`prop:cap-estimate`), left as the only named
hypothesis of the two nonexistence propositions, exactly as in `main_of_capEstimate`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LiquidDrop

/-- **`lem:two-ball-comparison`** for the bounded open `C¹` representative `Ω` of a fixed-volume
minimiser (`MinimizerRep V Ω`, so `V > 0`) at volume `V ≤ 8`, with no named hypothesis. With
`λ = minimizerMultiplier V Ω` the multiplier of `cor:minimizer-stationary`,
`z = √(Per(Ω)/P_B(V))` (`not:z-delta`) and `L = q⁻²(V + 10)` (`not:L`, `twoBallL V`):
`λ √(Per(Ω)/4π) ≤ (L − 3z²) z` (`eq:two-ball-lambda`) and
`z² ≤ L/5 < q⁴`, hence `z < q²` and `q⁻² z < 1` (`eq:z-small`). -/
theorem MinimizerRep.two_ball_comparison_bounds {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) (hV8 : V ≤ 8) {z : ℝ}
    (hzdef : z = Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal)) :
    minimizerMultiplier V Ω * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) ≤
        (twoBallL V - 3 * z ^ 2) * z ∧
      z ^ 2 ≤ twoBallL V / 5 ∧ twoBallL V / 5 < q ^ 4 ∧ z < q ^ 2 ∧ (q ^ 2)⁻¹ * z < 1 := by
  have hV0 : 0 < V := h.volume_pos
  have hvolR : (volume Ω).toReal = V := h.volume_toReal
  have hstat := h.isStationaryDomain
  -- `lem:ball-perimeter` data for `B_V`
  have hPBpos : 0 < (ballPerimeter V).toReal :=
    ENNReal.toReal_pos (ballPerimeter_pos hV0).ne' (ballPerimeter_lt_top hV0).ne
  have hR : 0 < ballRadius V := ballRadius_pos hV0
  have hPBR : (ballPerimeter V).toReal = 4 * Real.pi * ballRadius V ^ 2 :=
    ballPerimeter_toReal_eq_radius hV0
  -- `thm:sharp-isoperimetric` gives `P_B(V) ≤ Per(Ω)`, i.e. `z ≥ 1`
  have hisoP : ballPerimeter V ≤ perimeter Ω := by
    have := sharpIsoperimetric_holds.ballPerimeter_le h.nullMeasurableSet h.volume_lt_top
      (by rw [h.volume_eq]; exact ENNReal.ofReal_pos.mpr hV0)
    rwa [hvolR] at this
  have hPBP : (ballPerimeter V).toReal ≤ (perimeter Ω).toReal :=
    ENNReal.toReal_mono h.perimeter_lt_top.ne hisoP
  have hratio : 1 ≤ (perimeter Ω).toReal / (ballPerimeter V).toReal :=
    (one_le_div hPBpos).mpr hPBP
  have hz1 : 1 ≤ z := by
    have := Real.sqrt_le_sqrt hratio
    rw [Real.sqrt_one, ← hzdef] at this
    exact this
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
  -- minimality against two balls of volume `V/2` (`lem:subadditivity`, `prop:two-ball`)
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
  exact ⟨two_ball_lambda_bound hV0 hR hz1 (radius_mul_ballPerimeter hV0) hstat.2.2 hz2 hsqrt
    hcomp, z_small hPBpos hV8 hz2 hPE hcomp⟩

/-- **`lem:two-ball-comparison`** for a fixed-volume minimiser `Ω` (Lebesgue-measurable
convention) at volume `0 < V ≤ 8`, with no named hypothesis, stated for `Ω` itself: with
`λ = minimizerMultiplier V Ω`, `z = √(Per(Ω)/P_B(V))` and `L = q⁻²(V + 10)`,
`λ √(Per(Ω)/4π) ≤ (L − 3z²) z` (`eq:two-ball-lambda`) and `z² ≤ L/5 < q⁴`, `z < q²`,
`q⁻² z < 1` (`eq:z-small`). `Per` and `λ` agree with those of the representative
`densityOne Ω` (null-set invariance). -/
theorem IsLebesgueFixedVolumeMinimizer.two_ball_comparison_bounds {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hV8 : V ≤ 8) (hΩ : IsLebesgueFixedVolumeMinimizer V Ω)
    {z : ℝ} (hzdef : z = Real.sqrt ((perimeter Ω).toReal / (ballPerimeter V).toReal)) :
    minimizerMultiplier V Ω * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi)) ≤
        (twoBallL V - 3 * z ^ 2) * z ∧
      z ^ 2 ≤ twoBallL V / 5 ∧ twoBallL V / 5 < q ^ 4 ∧ z < q ^ 2 ∧ (q ^ 2)⁻¹ * z < 1 := by
  obtain ⟨h, hae⟩ := hΩ.minimizerRep_densityOne noSingularPointsStatement hV
  have hP : perimeter (densityOne Ω) = perimeter Ω := perimeter_congr_ae hae
  have hlam : minimizerMultiplier V (densityOne Ω) = minimizerMultiplier V Ω := by
    unfold minimizerMultiplier
    rw [hP, coulombEnergy_congr_ae hae]
  have := h.two_ball_comparison_bounds hV8 (z := z) (by rw [hP]; exact hzdef)
  rwa [hlam, hP] at this

/-- **`prop:nonexistence-6`**, modulo `CapEstimateStatement` (`prop:cap-estimate`) only: no
fixed-volume minimiser (Lebesgue-measurable convention) exists at a volume `V` with
`V_* < V ≤ 6`. -/
theorem nonexistence_six_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hVstar : criticalVolume < V) (hV6 : V ≤ 6) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω := by
  rintro ⟨Ω₀, hΩ₀⟩
  have hV0 : 0 < V := criticalVolume_pos.trans hVstar
  obtain ⟨h, -⟩ := hΩ₀.minimizerRep_densityOne noSingularPointsStatement hV0
  obtain ⟨hupper, -, -, -, hzq⟩ := h.two_ball_comparison_bounds (by linarith) rfl
  exact nonexistence_six hVstar hV6 (isoDeficit_nonneg_unconditional hV0 h.minimizer)
    (one_add_isoDeficit V (densityOne Ω₀)).symm hzq hupper
    ((hcap V _ (densityOne Ω₀) hV0 h.isStationaryDomain.1).1 hV6)

/-- **`prop:nonexistence-6`** in the Borel convention of `def:minimizer`, modulo
`CapEstimateStatement` (`prop:cap-estimate`) only. -/
theorem nonexistence_six_borel_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hVstar : criticalVolume < V) (hV6 : V ≤ 6) :
    ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω := by
  rw [exists_fixedVolumeMinimizer_iff_lebesgue]
  exact nonexistence_six_of_capEstimate hcap hVstar hV6

/-- **`prop:nonexistence-8`**, modulo `CapEstimateStatement` (`prop:cap-estimate`) only: no
fixed-volume minimiser (Lebesgue-measurable convention) exists at a volume `V` with
`6 < V ≤ 8`. -/
theorem nonexistence_eight_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hV6 : 6 < V) (hV8 : V ≤ 8) :
    ¬ ∃ Ω : Set AmbientSpace, IsLebesgueFixedVolumeMinimizer V Ω := by
  rintro ⟨Ω₀, hΩ₀⟩
  have hV0 : 0 < V := by linarith
  obtain ⟨h, -⟩ := hΩ₀.minimizerRep_densityOne noSingularPointsStatement hV0
  obtain ⟨hupper, -⟩ := h.two_ball_comparison_bounds hV8 rfl
  exact nonexistence_eight hV6 hV8 (Real.sqrt_nonneg _) hupper
    ((hcap V _ (densityOne Ω₀) hV0 h.isStationaryDomain.1).2 hV6.le)

/-- **`prop:nonexistence-8`** in the Borel convention of `def:minimizer`, modulo
`CapEstimateStatement` (`prop:cap-estimate`) only. -/
theorem nonexistence_eight_borel_of_capEstimate (hcap : CapEstimateStatement) {V : ℝ}
    (hV6 : 6 < V) (hV8 : V ≤ 8) :
    ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω := by
  rw [exists_fixedVolumeMinimizer_iff_lebesgue]
  exact nonexistence_eight_of_capEstimate hcap hV6 hV8

end LiquidDrop
