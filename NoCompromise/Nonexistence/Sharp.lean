import NoCompromise.Threshold.Ledger
import NoCompromise.Nonexistence.Slicing
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Sharp nonexistence above the threshold

The algebraic core of blueprint Chapter 36 (`ch:nonexistence`), section
"Sharp nonexistence for `V_* < V ≤ 8`".

Everything here is real-number algebra.  The geometric inputs
(`prop:scaling-identity` of Chapter 28, `prop:cap-estimate` of Chapter 33,
minimality against two balls of volume `V/2` from `prop:two-ball`, the ball
identity `lem:ball-perimeter`, and the isoperimetric normalisation
`not:z-delta`) enter as explicit named hypotheses, exactly as permitted by
blueprint `fnote:cap-interface`.
-/

noncomputable section

namespace LiquidDrop

/-- Blueprint `not:L`: `L := q⁻²(V + 10)`, the quantity for which
`2𝓔(B_{V/2}) = (L/5) P_B(V)` by `prop:two-ball`. -/
def twoBallL (V : ℝ) : ℝ := (q ^ 2)⁻¹ * (V + 10)

/-- Positivity of the quantity `L` of blueprint `not:L` at positive volumes. -/
theorem twoBallL_pos {V : ℝ} (hV : 0 < V) : 0 < twoBallL V := by
  have hq : (0 : ℝ) < q := q_pos
  have : (0 : ℝ) < (q ^ 2)⁻¹ := by positivity
  have h10 : (0 : ℝ) < V + 10 := by linarith
  exact mul_pos this h10

/-! ## Blueprint `lem:two-ball-comparison` -/

/-- Blueprint `lem:two-ball-comparison`, inequality `eq:two-ball-lambda`.

`V` is the volume, `P = Per(Ω)`, `E = 𝓔(Ω)`, `PB = P_B(V)`, `R` the radius of
`B_V`, `lam` the multiplier and `z = 1 + δ` as in `not:z-delta`.  The
hypotheses are, in order: `lem:ball-perimeter` (`eq:ball-perimeter`),
`prop:scaling-identity` (`eq:scaling-identity`, second form), the two
identities of `eq:z-identities`, and minimality against two balls of volume
`V/2` combined with `prop:two-ball`. -/
theorem two_ball_lambda_bound {V lam P E PB R z : ℝ} (hV : 0 < V)
    (hR : 0 < R) (hz1 : 1 ≤ z) (hRPB : R * PB = 3 * V)
    (hscaling : 3 * V * lam = 5 * E - 3 * P) (hz : P = PB * z ^ 2)
    (hsqrt : Real.sqrt (P / (4 * Real.pi)) = R * z)
    (hcomp : E ≤ twoBallL V / 5 * PB) :
    lam * Real.sqrt (P / (4 * Real.pi)) ≤ (twoBallL V - 3 * z ^ 2) * z := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have h3V : (0 : ℝ) < 3 * V := by linarith
  have hRz : (0 : ℝ) ≤ R * z := by positivity
  have h5 : 5 * E ≤ twoBallL V * PB := by nlinarith [hcomp]
  have key : 3 * V * lam ≤ PB * (twoBallL V - 3 * z ^ 2) := by
    rw [hscaling, hz]; nlinarith [h5]
  rw [hsqrt]
  refine le_of_mul_le_mul_left ?_ h3V
  calc 3 * V * (lam * (R * z)) = 3 * V * lam * (R * z) := by ring
    _ ≤ PB * (twoBallL V - 3 * z ^ 2) * (R * z) := mul_le_mul_of_nonneg_right key hRz
    _ = R * PB * ((twoBallL V - 3 * z ^ 2) * z) := by ring
    _ = 3 * V * ((twoBallL V - 3 * z ^ 2) * z) := by rw [hRPB]

/-- Blueprint `lem:two-ball-comparison`, inequality `eq:z-small`.

`hPE` is `Per(Ω) ≤ 𝓔(Ω)` (the Coulomb term is nonnegative), `hz` is the first
identity of `eq:z-identities`, and `hcomp` is minimality against two balls of
volume `V/2`.  The bound `L/5 < q⁴` is blueprint `lem:ledger-L5`. -/
theorem z_small {V P E PB z : ℝ} (hPB : 0 < PB) (hV8 : V ≤ 8)
    (hz : P = PB * z ^ 2) (hPE : P ≤ E) (hcomp : E ≤ twoBallL V / 5 * PB) :
    z ^ 2 ≤ twoBallL V / 5 ∧ twoBallL V / 5 < q ^ 4 ∧ z < q ^ 2 ∧
      (q ^ 2)⁻¹ * z < 1 := by
  have hq : (0 : ℝ) < q := q_pos
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  have hzsq : z ^ 2 ≤ twoBallL V / 5 := by
    have hmul : PB * z ^ 2 ≤ twoBallL V / 5 * PB := by linarith
    nlinarith [hmul]
  have hL5 := ledger_L5 V hV8
  have hlt : twoBallL V / 5 < q ^ 4 := by
    have h1 : twoBallL V / 5 ≤ 18 / (5 * q ^ 2) := hL5.1
    exact lt_of_le_of_lt h1 hL5.2
  have hzq : z < q ^ 2 := by
    refine lt_of_pow_lt_pow_left₀ 2 hq2.le ?_
    have : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [this]
    linarith
  refine ⟨hzsq, hlt, hzq, ?_⟩
  have := mul_lt_mul_of_pos_left hzq (inv_pos.2 hq2)
  rwa [inv_mul_cancel₀ (ne_of_gt hq2)] at this

/-! ## Blueprint `eq:nonexistence-identity` -/

/-- Blueprint `eq:nonexistence-identity`, the sharp algebraic identity of
`prop:nonexistence-6`.  Following `fnote:verify-nonexistence-identity` it is
proved as an exact identity, by normalisation against the threshold identity
`eq:Vstar-identity` (`criticalVolume_identity`), and not by a chain of
inequalities.  Its `V = criticalVolume` specialisation is
`lem:ledger-oneball`. -/
theorem nonexistence_identity (V δ : ℝ) :
    V + 2 - (twoBallL V - 3 * (1 + δ) ^ 2) * (1 + δ)
      = δ * (4 - criticalVolume + 9 * δ + 3 * δ ^ 2)
        + (V - criticalVolume) * (1 - (q ^ 2)⁻¹ * (1 + δ)) := by
  rw [twoBallL]
  linear_combination (-(1 + δ)) * criticalVolume_identity

/-! ## Blueprint `prop:nonexistence-6` -/

/-- Blueprint `prop:nonexistence-6`, in the partial form permitted by
`fnote:cap-interface`: the capacitary lower bound `eq:cap-estimate` for
`V ≤ 6` is the hypothesis `hlower`, and the two-ball upper bounds
`eq:two-ball-lambda`, `eq:z-small` are `hupper` and `hzq`.  There is no
minimiser at a volume `criticalVolume < V ≤ 6`. -/
theorem nonexistence_six {V δ z lam P : ℝ} (hVstar : criticalVolume < V)
    (_hV6 : V ≤ 6) (hδ : 0 ≤ δ) (hz : z = 1 + δ) (hzq : (q ^ 2)⁻¹ * z < 1)
    (hupper : lam * Real.sqrt (P / (4 * Real.pi)) ≤ (twoBallL V - 3 * z ^ 2) * z)
    (hlower : V + 2 ≤ lam * Real.sqrt (P / (4 * Real.pi))) : False := by
  subst hz
  have hid := nonexistence_identity V δ
  have hfirst : 0 ≤ δ * (4 - criticalVolume + 9 * δ + 3 * δ ^ 2) := by
    have h4 : criticalVolume < 4 := criticalVolume_lt_four
    have : 0 ≤ 4 - criticalVolume + 9 * δ + 3 * δ ^ 2 := by nlinarith
    exact mul_nonneg hδ this
  have hsecond : 0 < (V - criticalVolume) * (1 - (q ^ 2)⁻¹ * (1 + δ)) :=
    mul_pos (by linarith) (by linarith)
  linarith

/-! ## Blueprint `prop:nonexistence-8` -/

/-- Blueprint `eq:cubic-value`: since `L = q⁻²(V + 10)` and `q³ = 2`, the
cubic majorant `2L^{3/2}/9` of `lem:ledger-cubic` equals `(V+10)^{3/2}/9`. -/
theorem cubic_value {V : ℝ} (hV : 0 ≤ V + 10) :
    2 * twoBallL V ^ ((3 : ℝ) / 2) / 9 = (V + 10) ^ ((3 : ℝ) / 2) / 9 := by
  have hq : (0 : ℝ) < q := q_pos
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  have hL0 : 0 ≤ twoBallL V := by
    have : (0 : ℝ) < (q ^ 2)⁻¹ := by positivity
    exact mul_nonneg this.le hV
  have hsqrtL : Real.sqrt (twoBallL V) = q⁻¹ * Real.sqrt (V + 10) := by
    rw [twoBallL, Real.sqrt_mul (by positivity) _, Real.sqrt_inv, Real.sqrt_sq hq.le]
  rw [rpow_three_halves _ hL0, rpow_three_halves _ hV, hsqrtL, mul_pow, inv_pow, q_cube]
  ring

/-- The strict inequality `(V+10)^{3/2}/9 < 4√(V-2)` on `6 < V ≤ 8` used in
blueprint `prop:nonexistence-8`; it reduces to `(V+10)³/(V-2) < 1296`, which is
`lem:ledger-h`. -/
theorem cubic_lt_cap {V : ℝ} (hV6 : 6 < V) (hV8 : V ≤ 8) :
    (V + 10) ^ ((3 : ℝ) / 2) / 9 < 4 * Real.sqrt (V - 2) := by
  have hV10 : (0 : ℝ) ≤ V + 10 := by linarith
  have hV2 : (0 : ℝ) < V - 2 := by linarith
  have hs : Real.sqrt (V - 2) > 0 := Real.sqrt_pos.2 hV2
  have hlhs0 : 0 ≤ (V + 10) ^ ((3 : ℝ) / 2) / 9 := by
    rw [rpow_three_halves _ hV10]
    positivity
  have hsq : ((V + 10) ^ ((3 : ℝ) / 2)) ^ 2 = (V + 10) ^ 3 := by
    rw [rpow_three_halves _ hV10]
    calc (Real.sqrt (V + 10) ^ 3) ^ 2 = (Real.sqrt (V + 10) ^ 2) ^ 3 := by ring
      _ = (V + 10) ^ 3 := by rw [Real.sq_sqrt hV10]
  have hh := ledger_h V ⟨hV6.le, hV8⟩
  have hcube : (V + 10) ^ 3 < 1296 * (V - 2) := by
    have h1 : (V + 10) ^ 3 / (V - 2) ≤ 1024 := hh.1
    have h2 : (V + 10) ^ 3 ≤ 1024 * (V - 2) := by
      rw [div_le_iff₀ hV2] at h1; linarith
    linarith
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  have hsr : Real.sqrt (V - 2) ^ 2 = V - 2 := Real.sq_sqrt hV2.le
  have hexp : ((V + 10) ^ ((3 : ℝ) / 2) / 9) ^ 2 = (V + 10) ^ 3 / 81 := by
    rw [div_pow, hsq]; norm_num
  rw [hexp, mul_pow, hsr]
  linarith

/-- Blueprint `prop:nonexistence-8`, in the partial form permitted by
`fnote:cap-interface`: the capacitary lower bound `eq:cap-estimate` for
`V ≥ 6` is the hypothesis `hlower` and `eq:two-ball-lambda` is `hupper`.
There is no minimiser at a volume `6 < V ≤ 8`. -/
theorem nonexistence_eight {V z lam P : ℝ} (hV6 : 6 < V) (hV8 : V ≤ 8)
    (hz0 : 0 ≤ z)
    (hupper : lam * Real.sqrt (P / (4 * Real.pi)) ≤ (twoBallL V - 3 * z ^ 2) * z)
    (hlower : 4 * Real.sqrt (V - 2) ≤ lam * Real.sqrt (P / (4 * Real.pi))) :
    False := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hL : 0 < twoBallL V := twoBallL_pos hV0
  have hcubic := ledger_cubic (twoBallL V) z hL hz0
  have hrewrite : (twoBallL V - 3 * z ^ 2) * z = twoBallL V * z - 3 * z ^ 3 := by
    ring
  have hval := cubic_value (V := V) (by linarith)
  have hstrict := cubic_lt_cap hV6 hV8
  rw [hrewrite] at hupper
  linarith

/-! ## Blueprint `cor:nonexistence` -/

/-- Blueprint `cor:nonexistence`, restricted to `V ≤ 8` (the complementary
range is `prop:V-le-8`, which lives in `NoCompromise.Nonexistence.Slicing`).
The hypothesis `hlower` is exactly the two-case conclusion `eq:cap-estimate`
of `prop:cap-estimate`, and `hupper`, `hzq` are `eq:two-ball-lambda` and the
last part of `eq:z-small`.  The `V ≤ 6` / `6 < V` split of
`prop:nonexistence-6` and `prop:nonexistence-8` is performed inside. -/
theorem nonexistence_above_threshold {V δ z lam P : ℝ}
    (hVstar : criticalVolume < V) (hV8 : V ≤ 8) (hδ : 0 ≤ δ) (hz : z = 1 + δ)
    (hzq : (q ^ 2)⁻¹ * z < 1)
    (hupper : lam * Real.sqrt (P / (4 * Real.pi)) ≤ (twoBallL V - 3 * z ^ 2) * z)
    (hlower : (V ≤ 6 → V + 2 ≤ lam * Real.sqrt (P / (4 * Real.pi))) ∧
      (6 ≤ V → 4 * Real.sqrt (V - 2) ≤ lam * Real.sqrt (P / (4 * Real.pi)))) :
    False := by
  rcases le_or_gt V 6 with h6 | h6
  · exact nonexistence_six hVstar h6 hδ hz hzq hupper (hlower.1 h6)
  · exact nonexistence_eight h6 hV8 (by rw [hz]; linarith) hupper (hlower.2 h6.le)

open MeasureTheory in
/-- Blueprint `cor:nonexistence` for every volume `V > V_*`: no fixed-volume minimiser exists.

Here `V = |Ω|`.  The range `V > 8` is excluded by `prop:V-le-8`
(`volume_le_eight_of_slicing_inequality`), whose only external input is the slicing inequality
`eq:slice-coulomb` of `lem:slicing-inequality`, supplied as `hslice`.  On the remaining range
`V_* < V ≤ 8` the argument is `nonexistence_above_threshold`; its inputs from
`lem:two-ball-comparison` (`eq:two-ball-lambda` and the last part of `eq:z-small`), which the
blueprint derives only for `0 < V ≤ 8`, are taken under that hypothesis, and `hlower` is the
two-case conclusion `eq:cap-estimate` of `prop:cap-estimate`. -/
theorem nonexistence_above_threshold_of_slicing (Ω : Set AmbientSpace) (hΩ : MeasurableSet Ω)
    (hfin : MeasureTheory.volume Ω ≠ ⊤) {δ z lam P : ℝ}
    (hVstar : criticalVolume < (MeasureTheory.volume Ω).toReal)
    (hslice : ∀ ν ∈ Metric.sphere (0 : AmbientSpace) 1, ∀ᵐ ℓ : ℝ,
      (∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
          ENNReal.ofReal (‖x - y‖⁻¹)) ≤ 2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}))
    (hδ : 0 ≤ δ) (hz : z = 1 + δ)
    (hzq : (MeasureTheory.volume Ω).toReal ≤ 8 → (q ^ 2)⁻¹ * z < 1)
    (hupper : (MeasureTheory.volume Ω).toReal ≤ 8 →
      lam * Real.sqrt (P / (4 * Real.pi)) ≤
        (twoBallL (MeasureTheory.volume Ω).toReal - 3 * z ^ 2) * z)
    (hlower : ((MeasureTheory.volume Ω).toReal ≤ 6 →
        (MeasureTheory.volume Ω).toReal + 2 ≤ lam * Real.sqrt (P / (4 * Real.pi))) ∧
      (6 ≤ (MeasureTheory.volume Ω).toReal →
        4 * Real.sqrt ((MeasureTheory.volume Ω).toReal - 2) ≤
          lam * Real.sqrt (P / (4 * Real.pi)))) :
    False := by
  have hV8 := volume_le_eight_of_slicing_inequality Ω hΩ hfin hslice
  exact nonexistence_above_threshold hVstar hV8 hδ hz (hzq hV8) (hupper hV8) hlower

end LiquidDrop

#print axioms LiquidDrop.twoBallL_pos
#print axioms LiquidDrop.two_ball_lambda_bound
#print axioms LiquidDrop.z_small
#print axioms LiquidDrop.nonexistence_identity
#print axioms LiquidDrop.nonexistence_six
#print axioms LiquidDrop.cubic_value
#print axioms LiquidDrop.cubic_lt_cap
#print axioms LiquidDrop.nonexistence_eight
#print axioms LiquidDrop.nonexistence_above_threshold
#print axioms LiquidDrop.nonexistence_above_threshold_of_slicing
