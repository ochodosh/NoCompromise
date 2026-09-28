import NoCompromise.Threshold.Ledger
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The capacitary estimate for stationary domains

Blueprint Chapter 33 (`ch:cap-estimate`).

Throughout, the real parameters are the ones of blueprint `not:cap-estimate`:
`lam` is the Lagrange multiplier λ, `V` the volume, `C = Cap(K)`,
`I = ∫_{∂K}|∇u|²` and `P = Per(Ω)`.

The chapter's inputs come from Chapters 28, 30, 31 and 32, which are not yet
formalised.  Every such input therefore appears here as an *explicit named
hypothesis* in its blueprint form; the algebraic content of the chapter is
proved in full.  In particular `eliminate_capacity` and
`cap_estimate_of_stationary` have no external inputs beyond the displayed ones.
-/

noncomputable section

open MeasureTheory

namespace LiquidDrop

/-! ### `lem:integrate-EL` -/

/-- Blueprint `lem:integrate-EL`, equation `eq:integrate-EL`.

The boundary `∂K` is modelled by an abstract measure space `(X, μ)`; `g` plays
the role of `|∇u|`, `H` of the mean curvature and `v` of the Newtonian
potential `v_Ω`.  The external inputs are

* `hEL`  : `cor:EL-pointwise`, i.e. `H + v_Ω = λ` on `∂K`;
* `hflux`: `lem:flux-identity`, equation `eq:flux-boundary`;
* `hgreen`: `thm:green-identity`.

The conclusion is `λ𝖢 - V = (4π)⁻¹ ∫_{∂K} H |∇u|`. -/
theorem integrate_EL_of_EL_pointwise_of_flux_identity_of_green_identity
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (H v g : X → ℝ)
    (lam C V : ℝ)
    (hEL : ∀ x, H x + v x = lam)
    (hflux : ∫ x, g x ∂μ = 4 * Real.pi * C)
    (hgreen : (4 * Real.pi)⁻¹ * ∫ x, v x * g x ∂μ = V)
    (hg : Integrable g μ) (hvg : Integrable (fun x => v x * g x) μ) :
    lam * C - V = (4 * Real.pi)⁻¹ * ∫ x, H x * g x ∂μ := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hvgint : ∫ x, v x * g x ∂μ = 4 * Real.pi * V := by
    rw [← hgreen]
    field_simp
  have hfun : (fun x => H x * g x) = fun x => lam * g x - v x * g x := by
    funext x
    have h : H x = lam - v x := by linarith [hEL x]
    rw [h]; ring
  have hHg : ∫ x, H x * g x ∂μ = lam * (4 * Real.pi * C) - 4 * Real.pi * V := by
    rw [hfun, integral_sub (hg.const_mul lam) hvg, integral_const_mul, hflux, hvgint]
  rw [hHg]
  field_simp

/-- Blueprint `lem:integrate-EL`, equation `eq:integrate-EL-bound`.

The external input `hcap2` is the *second* capacitary inequality of
`thm:capacitary-inequalities` (blueprint Chapter 31) in its exact form
`∫_{∂K} H|∇u| ≥ 4𝖨 - 8π`; `hEL1` is the conclusion `eq:integrate-EL` of
`integrate_EL_of_EL_pointwise_of_flux_identity_of_green_identity`. -/
theorem integrate_EL_bound_of_capacitary_inequalities
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (H g : X → ℝ)
    (lam C V I : ℝ)
    (hEL1 : lam * C - V = (4 * Real.pi)⁻¹ * ∫ x, H x * g x ∂μ)
    (hcap2 : ∫ x, H x * g x ∂μ ≥ 4 * I - 8 * Real.pi) :
    lam * C - V ≥ I / Real.pi - 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * Real.pi := by linarith
  have hmul : (4 * Real.pi)⁻¹ * (4 * I - 8 * Real.pi)
      ≤ (4 * Real.pi)⁻¹ * ∫ x, H x * g x ∂μ :=
    mul_le_mul_of_nonneg_left hcap2 (inv_nonneg.2 h4pi.le)
  have hval : (4 * Real.pi)⁻¹ * (4 * I - 8 * Real.pi) = I / Real.pi - 2 := by
    field_simp
    ring
  rw [hEL1]
  linarith [hmul, hval.le, hval.ge]

/-! ### `lem:two-bounds-I` -/

/-- Blueprint `lem:two-bounds-I`, equation `eq:I-bound-1`.

`hI1` is the first capacitary inequality `𝖨 ≥ 4π` of
`thm:capacitary-inequalities`; `hEL1` is `eq:integrate-EL-bound`. -/
theorem lambdaC_sub_V_ge_two {lam C V I : ℝ} (hI1 : I ≥ 4 * Real.pi)
    (hEL1 : lam * C - V ≥ I / Real.pi - 2) : lam * C - V ≥ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : (4 : ℝ) ≤ I / Real.pi := by
    rw [le_div_iff₀ hpi]
    linarith
  linarith

/-- Blueprint `lem:two-bounds-I`, first half of equation `eq:I-bound-2`.

`hCS` is Cauchy–Schwarz on `∂K` (an external input), `hflux` is
`eq:flux-boundary`, and `hPerK : Per(K) ≤ P` is `eq:hull-perimeter`
(blueprint Chapter 29). -/
theorem I_ge_sq_div {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ)
    {I C PerK P : ℝ}
    (hCS : I ≥ (∫ x, g x ∂μ) ^ 2 / PerK)
    (hflux : ∫ x, g x ∂μ = 4 * Real.pi * C)
    (hPerK : PerK ≤ P) (hPerK0 : 0 < PerK) :
    I ≥ 16 * Real.pi ^ 2 * C ^ 2 / P := by
  rw [hflux, show (4 * Real.pi * C) ^ 2 = 16 * Real.pi ^ 2 * C ^ 2 by ring] at hCS
  have hnum : (0 : ℝ) ≤ 16 * Real.pi ^ 2 * C ^ 2 := by positivity
  have hmono : 16 * Real.pi ^ 2 * C ^ 2 / P ≤ 16 * Real.pi ^ 2 * C ^ 2 / PerK := by
    gcongr
  linarith

/-- Blueprint `lem:two-bounds-I`, second half of equation `eq:I-bound-2`. -/
theorem lambdaC_sub_V_ge_cap {lam C V I P : ℝ} (hP : 0 < P)
    (hI2 : I ≥ 16 * Real.pi ^ 2 * C ^ 2 / P)
    (hEL1 : lam * C - V ≥ I / Real.pi - 2) :
    lam * C - V ≥ 16 * Real.pi * C ^ 2 / P - 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsplit : I / Real.pi - 16 * Real.pi * C ^ 2 / P
      = (I - 16 * Real.pi ^ 2 * C ^ 2 / P) / Real.pi := by
    field_simp
  have hnn : 0 ≤ (I - 16 * Real.pi ^ 2 * C ^ 2 / P) / Real.pi :=
    div_nonneg (by linarith) hpi.le
  linarith [hsplit.le, hsplit.ge]

/-- Blueprint `lem:two-bounds-I`, equation `eq:I-bound-combined`. -/
theorem lambdaC_sub_V_ge_max {lam C V P : ℝ} (h1 : lam * C - V ≥ 2)
    (h2 : lam * C - V ≥ 16 * Real.pi * C ^ 2 / P - 2) :
    lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2) := max_le h1 h2

/-! ### `lem:eliminate-capacity` -/

/-- Blueprint `lem:eliminate-capacity`, the substitution `eq:sy-def`.

With `s := 𝖢√(4π/𝖯)` and `y := λ√(𝖯/(4π))` one has `λ𝖢 = sy` and
`16π𝖢²/𝖯 = 4s²`, so `eq:I-bound-combined` turns into the two bounds
`eq:sy-bounds`. -/
theorem sy_bounds {lam V C P : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hkey : lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2)) :
    ∃ s : ℝ, 0 < s ∧ V + 2 ≤ s * (lam * Real.sqrt (P / (4 * Real.pi))) ∧
      V - 2 + 4 * s ^ 2 ≤ s * (lam * Real.sqrt (P / (4 * Real.pi))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * Real.pi := by linarith
  have hA : (0 : ℝ) < 4 * Real.pi / P := div_pos h4pi hP
  have hprod : Real.sqrt (4 * Real.pi / P) * Real.sqrt (P / (4 * Real.pi)) = 1 := by
    rw [← Real.sqrt_mul hA.le,
      show 4 * Real.pi / P * (P / (4 * Real.pi)) = 1 by field_simp]
    exact Real.sqrt_one
  have hsy : C * Real.sqrt (4 * Real.pi / P) * (lam * Real.sqrt (P / (4 * Real.pi)))
      = lam * C := by
    rw [show C * Real.sqrt (4 * Real.pi / P) * (lam * Real.sqrt (P / (4 * Real.pi)))
        = lam * C * (Real.sqrt (4 * Real.pi / P) * Real.sqrt (P / (4 * Real.pi))) by ring,
      hprod, mul_one]
  have hs2 : (C * Real.sqrt (4 * Real.pi / P)) ^ 2 = 4 * Real.pi * C ^ 2 / P := by
    rw [mul_pow, Real.sq_sqrt hA.le]
    ring
  refine ⟨C * Real.sqrt (4 * Real.pi / P), mul_pos hC (Real.sqrt_pos.2 hA), ?_, ?_⟩
  · rw [hsy]
    linarith [le_trans (le_max_left (2 : ℝ) (16 * Real.pi * C ^ 2 / P - 2)) hkey]
  · rw [hsy, hs2]
    have h16 : 4 * (4 * Real.pi * C ^ 2 / P) = 16 * Real.pi * C ^ 2 / P := by ring
    linarith [le_trans (le_max_right (2 : ℝ) (16 * Real.pi * C ^ 2 / P - 2)) hkey]

/-- Blueprint `lem:eliminate-capacity`, the step `s ≤ 1`: the first bound of
`eq:sy-bounds` already gives `y ≥ V + 2`. -/
theorem add_two_le_of_sy_le_one {s y V : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hV : 0 < V)
    (ha : V + 2 ≤ s * y) : V + 2 ≤ y := by
  have hsy : 0 < s * y := by linarith
  have hy0 : 0 < y := by
    by_contra hcon
    have hcon : y ≤ 0 := not_lt.1 hcon
    nlinarith [mul_nonneg hs0.le (neg_nonneg.2 hcon)]
  linarith [mul_le_of_le_one_left hy0.le hs1]

/-- Blueprint `lem:eliminate-capacity`, the step `s ≥ 1` for `0 < V ≤ 6`:
`V - 2 + 4s² - (V+2)s = (s-1)(4s - (V-2)) ≥ 0`, so the second bound of
`eq:sy-bounds` gives `y ≥ V + 2`. -/
theorem add_two_le_of_sy_one_le {s y V : ℝ} (hs1 : 1 ≤ s) (hV6 : V ≤ 6)
    (hb : V - 2 + 4 * s ^ 2 ≤ s * y) : V + 2 ≤ y := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hfac : 0 ≤ (s - 1) * (4 * s - (V - 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have hmul : s * (V + 2) ≤ s * y := by nlinarith
  exact le_of_mul_le_mul_left hmul hs0

/-- Blueprint `lem:eliminate-capacity`, the uniform AM–GM step for `V ≥ 2`:
`4s² - 4√(V-2)·s + (V-2) = (2s - √(V-2))² ≥ 0`, so the second bound of
`eq:sy-bounds` gives `y ≥ 4√(V-2)` for every `s > 0`. -/
theorem four_sqrt_le_of_sy {s y V : ℝ} (hs0 : 0 < s) (hV : 2 ≤ V)
    (hb : V - 2 + 4 * s ^ 2 ≤ s * y) : 4 * Real.sqrt (V - 2) ≤ y := by
  have ht2 : Real.sqrt (V - 2) ^ 2 = V - 2 := Real.sq_sqrt (by linarith)
  have hmul : s * (4 * Real.sqrt (V - 2)) ≤ s * y := by
    nlinarith [sq_nonneg (2 * s - Real.sqrt (V - 2))]
  exact le_of_mul_le_mul_left hmul hs0

/-- Blueprint `lem:eliminate-capacity`, the elementary comparison used in the
`s ≤ 1`, `V ≥ 6` case: `(V+2)² - 16(V-2) = (V-6)² ≥ 0` (`lem:ledger-six`), hence
`4√(V-2) ≤ V + 2`. -/
theorem four_sqrt_sub_two_le_add_two (V : ℝ) (hV6 : 6 ≤ V) :
    4 * Real.sqrt (V - 2) ≤ V + 2 := by
  have h1 : (0 : ℝ) ≤ V - 2 := by linarith
  have h16 : Real.sqrt (16 * (V - 2)) = 4 * Real.sqrt (V - 2) := by
    rw [show (16 : ℝ) * (V - 2) = 4 ^ 2 * (V - 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [← h16]
  have hle : 16 * (V - 2) ≤ (V + 2) ^ 2 := by
    have := ledger_six V
    nlinarith [sq_nonneg (V - 6)]
  calc Real.sqrt (16 * (V - 2)) ≤ Real.sqrt ((V + 2) ^ 2) := Real.sqrt_le_sqrt hle
    _ = V + 2 := Real.sqrt_sq (by linarith)

/-- Blueprint `lem:eliminate-capacity`, equation `eq:y-lower`, case `0 < V ≤ 6`. -/
theorem cap_estimate_le_six {lam V C P : ℝ} (hV : 0 < V) (hP : 0 < P) (hC : 0 < C)
    (hV6 : V ≤ 6)
    (hkey : lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2)) :
    V + 2 ≤ lam * Real.sqrt (P / (4 * Real.pi)) := by
  obtain ⟨s, hs0, ha, hb⟩ := sy_bounds hP hC hkey
  rcases le_total s 1 with h | h
  · exact add_two_le_of_sy_le_one hs0 h hV ha
  · exact add_two_le_of_sy_one_le h hV6 hb

/-- Blueprint `lem:eliminate-capacity`, equation `eq:y-lower`, case `V ≥ 6`. -/
theorem cap_estimate_ge_six {lam V C P : ℝ} (hP : 0 < P) (hC : 0 < C) (hV6 : 6 ≤ V)
    (hkey : lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2)) :
    4 * Real.sqrt (V - 2) ≤ lam * Real.sqrt (P / (4 * Real.pi)) := by
  obtain ⟨s, hs0, _, hb⟩ := sy_bounds hP hC hkey
  exact four_sqrt_le_of_sy hs0 (by linarith) hb

/-- Blueprint `lem:eliminate-capacity`, equation `eq:y-lower`, both cases at
once. -/
theorem eliminate_capacity {lam V C P : ℝ} (hV : 0 < V) (hP : 0 < P) (hC : 0 < C)
    (hkey : lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2)) :
    (if V ≤ 6 then V + 2 else 4 * Real.sqrt (V - 2))
      ≤ lam * Real.sqrt (P / (4 * Real.pi)) := by
  split_ifs with h
  · exact cap_estimate_le_six hV hP hC h hkey
  · exact cap_estimate_ge_six hP hC (by linarith [not_le.1 h]) hkey

/-! ### `prop:cap-estimate` -/

/-- Blueprint `prop:cap-estimate`, equation `eq:cap-estimate`, in the partial
form announced in `fnote:cap-interface`: the hypothesis `hkey` is exactly the
conclusion `eq:I-bound-combined` of `lem:two-bounds-I`, which is what a
stationary domain supplies.  Both branches of `eq:cap-estimate` are given. -/
theorem cap_estimate_of_stationary {lam V C P : ℝ} (hV : 0 < V) (hP : 0 < P)
    (hC : 0 < C)
    (hkey : lam * C - V ≥ max 2 (16 * Real.pi * C ^ 2 / P - 2)) :
    (V ≤ 6 → V + 2 ≤ lam * Real.sqrt (P / (4 * Real.pi))) ∧
      (6 ≤ V → 4 * Real.sqrt (V - 2) ≤ lam * Real.sqrt (P / (4 * Real.pi))) :=
  ⟨fun h => cap_estimate_le_six hV hP hC h hkey,
    fun h => cap_estimate_ge_six hP hC h hkey⟩

end LiquidDrop

#print axioms LiquidDrop.integrate_EL_of_EL_pointwise_of_flux_identity_of_green_identity
#print axioms LiquidDrop.integrate_EL_bound_of_capacitary_inequalities
#print axioms LiquidDrop.lambdaC_sub_V_ge_two
#print axioms LiquidDrop.I_ge_sq_div
#print axioms LiquidDrop.lambdaC_sub_V_ge_cap
#print axioms LiquidDrop.lambdaC_sub_V_ge_max
#print axioms LiquidDrop.sy_bounds
#print axioms LiquidDrop.add_two_le_of_sy_le_one
#print axioms LiquidDrop.add_two_le_of_sy_one_le
#print axioms LiquidDrop.four_sqrt_le_of_sy
#print axioms LiquidDrop.four_sqrt_sub_two_le_add_two
#print axioms LiquidDrop.cap_estimate_le_six
#print axioms LiquidDrop.cap_estimate_ge_six
#print axioms LiquidDrop.eliminate_capacity
#print axioms LiquidDrop.cap_estimate_of_stationary
