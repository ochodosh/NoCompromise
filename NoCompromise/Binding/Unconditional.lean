module

public import NoCompromise.Isoperimetric.ABPNeumannC1
public import NoCompromise.Value.Defs
public import NoCompromise.Binding.Splitting
public import NoCompromise.Binding.Strict
public import NoCompromise.Existence.Subcritical
public import NoCompromise.Binding.RelaxedAttained

@[expose] public section

/-!
# Chapters 17–19 and 38 with `thm:sharp-isoperimetric` discharged

`SharpIsoperimetric` (`eq:sharp-isoperimetric`, Value/Defs.lean) holds unconditionally
(`sharpIsoperimetric_holds`, Isoperimetric/ABPNeumannC1.lean). This file records the
unconditional instances, with the original conclusions, of the statements of Value/Defs.lean,
Binding/Splitting.lean, Binding/Strict.lean, Existence/Subcritical.lean and
Binding/RelaxedAttained.lean that take it as their only named hypothesis:

* `lem:m-finite`: `valueFunction_pos_unconditional`, `valueFunction_pos_lt_top_unconditional`;
* `lem:scaling-lower`: `scaling_lower_unconditional`, `scaling_lower_toReal_unconditional`;
* `lem:two-piece`: `two_piece_unconditional`;
* `prop:strict-binding`: `strict_binding_quantitative_unconditional`,
  `strict_binding_unconditional`, `strictBinding_holds`;
* `prop:existence-subcritical`: `exists_minimizer_subcritical`;
* `lem:relaxed-attained`: `relaxed_attained_unconditional`;
* `lem:stabilization`: `stabilization_unconditional`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-! ### `lem:m-finite` -/

/-- The isoperimetric inequality in the `P_B` form used in Chapter 18
(`eq:sharp-isoperimetric`), without hypotheses: `P_B(|E|) ≤ Per(E)` for `0 < |E| < ∞`. -/
theorem ballPerimeter_le_perimeter_unconditional
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hfin : volume E < ∞)
    (hpos : 0 < volume E) : ballPerimeter (volume E).toReal ≤ perimeter E :=
  sharpIsoperimetric_holds.ballPerimeter_le hE hfin hpos

/-- Blueprint `lem:m-finite`, positivity half, without hypotheses: `0 < m(V)` for `V > 0`. -/
theorem valueFunction_pos_unconditional {V : ℝ} (hV : 0 < V) : 0 < valueFunction V :=
  valueFunction_pos sharpIsoperimetric_holds hV

/-- Blueprint `lem:m-finite`, without hypotheses: `0 < m(V) ≤ 𝓔(B_V) < ∞` for `V > 0`. -/
theorem valueFunction_pos_lt_top_unconditional {V : ℝ} (hV : 0 < V) :
    0 < valueFunction V ∧ valueFunction V ≤ energy (ballByVolume V) ∧
      energy (ballByVolume V) < ∞ :=
  valueFunction_pos_lt_top sharpIsoperimetric_holds hV

/-! ### `lem:scaling-lower` and `lem:two-piece` -/

/-- Blueprint `lem:scaling-lower` (ENNReal form), without hypotheses. -/
theorem scaling_lower_unconditional {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ENNReal.ofReal (s ^ ((5 : ℝ) / 3)) * valueFunction V +
        ENNReal.ofReal ((1 - s) * s ^ ((2 : ℝ) / 3)) * ballPerimeter V ≤
      valueFunction (s * V) :=
  scaling_lower sharpIsoperimetric_holds hV hs0 hs1

/-- Blueprint `lem:scaling-lower`, real form, without hypotheses. -/
theorem scaling_lower_toReal_unconditional {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    s ^ ((5 : ℝ) / 3) * (valueFunction V).toReal +
        (1 - s) * s ^ ((2 : ℝ) / 3) * (ballPerimeter V).toReal ≤
      (valueFunction (s * V)).toReal :=
  scaling_lower_toReal sharpIsoperimetric_holds hV hs0 hs1

/-- Blueprint `lem:two-piece`, without hypotheses. -/
theorem two_piece_unconditional {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (ballPerimeter V).toReal * splittingD s * (splittingF s - V / 5) ≤
      (valueFunction (s * V)).toReal + (valueFunction ((1 - s) * V)).toReal -
        (valueFunction V).toReal :=
  two_piece sharpIsoperimetric_holds hV hs0 hs1

/-! ### `prop:strict-binding` -/

/-- Blueprint `prop:strict-binding`, quantitative form, without hypotheses. -/
theorem strict_binding_quantitative_unconditional {V s : ℝ} (hV : 0 < V)
    (hVc : V < criticalVolume) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < (ballPerimeter V).toReal * splittingD s * ((criticalVolume - V) / 5) ∧
    (ballPerimeter V).toReal * splittingD s * ((criticalVolume - V) / 5) ≤
      (valueFunction (s * V)).toReal + (valueFunction ((1 - s) * V)).toReal -
        (valueFunction V).toReal :=
  strict_binding_quantitative sharpIsoperimetric_holds hV hVc hs0 hs1

/-- Blueprint `prop:strict-binding`, without hypotheses:
`m(V) < m(sV) + m((1-s)V)` for `0 < V < V_*` and `s ∈ (0, 1)`. -/
theorem strict_binding_unconditional {V s : ℝ} (hV : 0 < V)
    (hVc : V < criticalVolume) (hs0 : 0 < s) (hs1 : s < 1) :
    valueFunction V < valueFunction (s * V) + valueFunction ((1 - s) * V) :=
  strict_binding sharpIsoperimetric_holds hV hVc hs0 hs1

/-- Blueprint `prop:strict-binding` in the form of the named predicate `StrictBinding`
(Existence/Subcritical.lean), without hypotheses. -/
theorem strictBinding_holds : StrictBinding :=
  strictBinding_of_sharpIsoperimetric sharpIsoperimetric_holds

/-! ### `prop:existence-subcritical` -/

/-- Blueprint `prop:existence-subcritical`, without hypotheses: for `0 < V < V_*` the infimum
`m(V)` is attained. -/
theorem exists_minimizer_subcritical {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    ∃ Ω : Set AmbientSpace, MeasurableSet Ω ∧ IsLebesgueFixedVolumeMinimizer V Ω ∧
      energy Ω = valueFunction V :=
  exists_minimizer_subcritical_of_sharp_isoperimetric sharpIsoperimetric_holds hV hVc

/-! ### `lem:relaxed-attained` and `lem:stabilization` -/

/-- The isoperimetric lower volume bound for sets of bounded energy-to-volume ratio (proof of
`lem:relaxed-attained`), without hypotheses: if `𝓔(E) ≤ M |E|` with `M > 0`, then
`|E| ≥ ((36π)^{1/3} / M)^3`. -/
theorem volume_ge_of_energy_le_mul_volume_unconditional {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞)
    {M : ℝ} (hM : 0 < M)
    (hratio : energy E ≤ ENNReal.ofReal M * volume E) :
    ENNReal.ofReal (((36 * Real.pi) ^ (1 / (3 : ℝ)) / M) ^ 3) ≤ volume E :=
  volume_ge_of_energy_le_mul_volume sharpIsoperimetric_holds hE hpos hfin hM hratio

/-- Blueprint `lem:relaxed-attained`, without hypotheses: for every `A > 0` the relaxed ratio
infimum `e_≤(A) = inf {𝓔(E)/|E| : 0 < |E| ≤ A}` is attained. -/
theorem relaxed_attained_unconditional {A : ℝ} (hA : 0 < A) :
    ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E :=
  relaxed_attained sharpIsoperimetric_holds hA

/-- Blueprint `lem:stabilization`, without hypotheses: `e_≤` is nonincreasing, constant equal to
`e_≤(8)` for `A ≥ 8`, the global ratio infimum equals `e_≤(8)`, and it is attained. -/
theorem stabilization_unconditional :
    Antitone relaxedEnergyRatio ∧
      (∀ A : ℝ, 8 ≤ A → relaxedEnergyRatio A = relaxedEnergyRatio 8) ∧
      globalEnergyRatio = relaxedEnergyRatio 8 ∧
      ∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E :=
  stabilization sharpIsoperimetric_holds

end LiquidDrop
