import NoCompromise.Threshold.Algebra
import NoCompromise.Threshold.Ledger
import NoCompromise.Value.Defs

namespace LiquidDrop

open MeasureTheory
open scoped ENNReal

noncomputable def splittingN (s : ℝ) : ℝ :=
  s ^ ((2 : ℝ) / 3) + (1 - s) ^ ((2 : ℝ) / 3) - 1

noncomputable def splittingD (s : ℝ) : ℝ :=
  1 - s ^ ((5 : ℝ) / 3) - (1 - s) ^ ((5 : ℝ) / 3)

noncomputable def splittingF (s : ℝ) : ℝ := splittingN s / splittingD s

theorem splitting_substitution {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let x := s ^ ((1 : ℝ) / 3)
    let y := (1 - s) ^ ((1 : ℝ) / 3)
    let p := x + y
    let r := x * y
    0 < x ∧ 0 < y ∧ x ^ 3 + y ^ 3 = 1 ∧
    1 < p ∧ p ≤ q ^ 2 ∧ (p = q ^ 2 ↔ s = 1 / 2) ∧
    r = (p ^ 3 - 1) / (3 * p) ∧
    splittingN s = p ^ 2 - 2 * r - 1 ∧
    splittingN s = (p - 1) ^ 2 * (p + 2) / (3 * p) ∧
    splittingD s = 1 - p ^ 2 + 2 * r + r ^ 2 * p ∧
    splittingD s = (p - 1) ^ 3 * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5) / (9 * p) := by
  dsimp only
  let x : ℝ := s ^ ((1 : ℝ) / 3)
  let y : ℝ := (1 - s) ^ ((1 : ℝ) / 3)
  let p : ℝ := x + y
  let r : ℝ := x * y
  have ht : 0 < 1 - s := by linarith
  have hx : 0 < x := by dsimp [x]; exact Real.rpow_pos_of_pos hs0 _
  have hy : 0 < y := by dsimp [y]; exact Real.rpow_pos_of_pos ht _
  have hx3 : x ^ 3 = s := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
    norm_num
  have hy3 : y ^ 3 = 1 - s := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht)]
    norm_num
  have hcube : x ^ 3 + y ^ 3 = 1 := by rw [hx3, hy3]; ring
  have hp : 0 < p := by dsimp [p]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hp3 : p ^ 3 = 1 + 3 * r * p := by
    dsimp [p, r]
    nlinarith [hcube]
  have hp1 : 1 < p := by
    have hid : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by ring
    nlinarith [hp3, hp, hr]
  have hp3le : p ^ 3 ≤ 4 := by
    have hid : 4 * (x ^ 3 + y ^ 3) - p ^ 3 = 3 * p * (x - y) ^ 2 := by
      dsimp [p]
      ring
    nlinarith [hid, hcube]
  have hq6 : (q ^ 2) ^ 3 = 4 := by
    calc
      (q ^ 2) ^ 3 = (q ^ 3) ^ 2 := by ring
      _ = 4 := by rw [q_cube]; norm_num
  have hp_le : p ≤ q ^ 2 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (sq_nonneg q)
    nlinarith [hp3le, hq6]
  have hr_eq : r = (p ^ 3 - 1) / (3 * p) := by
    have hden : 3 * p ≠ 0 := by positivity
    field_simp
    nlinarith [hp3]
  have hx2 : s ^ ((2 : ℝ) / 3) = x ^ 2 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
    norm_num
  have hy2 : (1 - s) ^ ((2 : ℝ) / 3) = y ^ 2 := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht)]
    norm_num
  have hx5 : s ^ ((5 : ℝ) / 3) = x ^ 5 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
    norm_num
  have hy5 : (1 - s) ^ ((5 : ℝ) / 3) = y ^ 5 := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht)]
    norm_num
  have hN : splittingN s = p ^ 2 - 2 * r - 1 := by
    rw [splittingN, hx2, hy2]
    dsimp [p, r]
    ring
  have hNclosed : splittingN s = (p - 1) ^ 2 * (p + 2) / (3 * p) := by
    rw [hN, hr_eq]
    have hden : 3 * p ≠ 0 := by positivity
    field_simp
    ring
  have hD : splittingD s = 1 - p ^ 2 + 2 * r + r ^ 2 * p := by
    rw [splittingD, hx5, hy5]
    dsimp [p, r]
    -- x^5 + y^5 = (x²+y²)(x³+y³) - x²y²(x+y) is a ring identity; combine it
    -- linearly with `hcube : x^3 + y^3 = 1` instead of a costly `nlinarith`
    -- search (this single call previously took ~12s / most of the heartbeat
    -- budget).
    linear_combination (-(x ^ 2 + y ^ 2)) * hcube
  have hDclosed : splittingD s = (p - 1) ^ 3 * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5) / (9 * p) := by
    rw [hD, hr_eq]
    have hden : 3 * p ≠ 0 := by positivity
    field_simp
    ring
  have heq : p = q ^ 2 ↔ s = 1 / 2 := by
    constructor
    · intro h
      have hp3eq : p ^ 3 = 4 := by rw [h, hq6]
      have hxy : x = y := by
        have hid : 4 * (x ^ 3 + y ^ 3) - p ^ 3 = 3 * p * (x - y) ^ 2 := by
          dsimp [p]
          ring
        rw [hcube, hp3eq] at hid
        norm_num at hid
        rcases hid with hzero | hxy
        · linarith
        · exact sub_eq_zero.mp hxy
      have hcubeXY : x ^ 3 = y ^ 3 := congrArg (fun z : ℝ => z ^ 3) hxy
      rw [hx3, hy3] at hcubeXY
      linarith
    · intro hs
      have hxy : x = y := by
        have hbase : 1 - s = s := by linarith
        dsimp [x, y]
        congr 1
        linarith [hbase]
      have hp3eq : p ^ 3 = 4 := by
        have hx3half : x ^ 3 = 1 / 2 := by
          rw [← hxy] at hcube
          -- `hcube` is now `x^3 + x^3 = 1`, which is linear in the atom
          -- `x^3`; a bare `nlinarith` here searched the whole (large)
          -- ambient context and took ~5s, so restrict to just this fact.
          linarith only [hcube]
        have hpval : p = 2 * x := by dsimp [p]; rw [hxy]; ring
        rw [hpval]
        rw [show (2 * x) ^ 3 = 8 * x ^ 3 by ring, hx3half]
        norm_num
      have hpowinj : Function.Injective (fun z : ℝ => z ^ 3) :=
        (show Odd 3 from ⟨1, by norm_num⟩).pow_injective
      apply hpowinj
      change p ^ 3 = (q ^ 2) ^ 3
      rw [hp3eq, hq6]
  exact ⟨hx, hy, hcube, hp1, hp_le, heq, hr_eq, hN, hNclosed, hD, hDclosed⟩

/-- Blueprint `lem:ND-positive`. -/
theorem splittingN_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < splittingN s := by
  obtain ⟨_, _, _, hp, _, _, _, _, hN, _, _⟩ := splitting_substitution hs0 hs1
  rw [hN]
  have hp0 : 0 < s ^ ((1 : ℝ) / 3) + (1 - s) ^ ((1 : ℝ) / 3) := by
    linarith
  positivity

/-- Blueprint `lem:ND-positive`. -/
theorem splittingD_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < splittingD s := by
  obtain ⟨_, _, _, hp, _, _, _, _, _, _, hD⟩ := splitting_substitution hs0 hs1
  rw [hD]
  have hp0 : 0 < s ^ ((1 : ℝ) / 3) + (1 - s) ^ ((1 : ℝ) / 3) := by
    linarith
  have hsub : 0 < s ^ ((1 : ℝ) / 3) + (1 - s) ^ ((1 : ℝ) / 3) - 1 := by
    linarith
  positivity

/-- The rational function `F` of blueprint `eq:splitting-F`. -/
noncomputable def splittingFofP (p : ℝ) : ℝ :=
  3 * (p + 2) / ((p - 1) * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5))

/-- Blueprint `lem:splitting-F`. -/
theorem splittingF_eq_splittingFofP {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    splittingF s =
      splittingFofP (s ^ ((1 : ℝ) / 3) + (1 - s) ^ ((1 : ℝ) / 3)) := by
  have halg (p : ℝ) (hp : 1 < p) :
      ((p - 1) ^ 2 * (p + 2) / (3 * p)) /
          ((p - 1) ^ 3 * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5) / (9 * p)) =
        3 * (p + 2) / ((p - 1) * (p ^ 3 + 3 * p ^ 2 + 6 * p + 5)) := by
    have hp0 : p ≠ 0 := by linarith
    have hsub : p - 1 ≠ 0 := by linarith
    have hpoly : p ^ 3 + 3 * p ^ 2 + 6 * p + 5 ≠ 0 := by
      have : 0 < p := by linarith
      positivity
    field_simp
    ring
  obtain ⟨_, _, _, hp, _, _, _, _, hN, _, hD⟩ := splitting_substitution hs0 hs1
  rw [splittingF, hN, hD, splittingFofP]
  exact halg _ hp

/-- `F` is strictly decreasing on `(1, ∞)`. -/
theorem splittingFofP_strictAntiOn : StrictAntiOn splittingFofP (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro p hp
    exact ((ledger_F_hasDerivAt p hp).continuousAt).continuousWithinAt
  · intro p hp
    exact ledger_F_deriv_neg p (by simpa using hp)

/-- The endpoint value. -/
theorem splittingFofP_q_sq : splittingFofP (q ^ 2) = q ^ 2 / (q + 1) := by
  have hq4 : q ^ 4 = 2 * q := by
    calc
      q ^ 4 = q * q ^ 3 := by ring
      _ = 2 * q := by rw [q_cube]; ring
  have hq6 : q ^ 6 = 4 := by
    calc
      q ^ 6 = (q ^ 3) ^ 2 := by ring
      _ = 4 := by rw [q_cube]; norm_num
  have hpoly : (q ^ 2) ^ 3 + 3 * (q ^ 2) ^ 2 + 6 * (q ^ 2) + 5 =
      6 * q ^ 2 + 6 * q + 9 := by
    calc
      _ = q ^ 6 + 3 * q ^ 4 + 6 * q ^ 2 + 5 := by ring
      _ = 6 * q ^ 2 + 6 * q + 9 := by rw [hq6, hq4]; ring
  have hden : (q ^ 2 - 1) * (6 * q ^ 2 + 6 * q + 9) = 3 * (q + 1) ^ 2 := by
    linear_combination 6 * hq4 + 6 * q_cube
  have hq1 : q + 1 ≠ 0 := by linarith [q_pos]
  rw [splittingFofP, hpoly, hden]
  field_simp
  linear_combination -q_cube

/-- Blueprint `thm:splitting`, value at the midpoint. -/
theorem splittingF_half : splittingF (1 / 2) = criticalVolume / 5 := by
  have hhalf0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨_, _, _, _, _, hp, _, _, _, _, _⟩ :=
    splitting_substitution hhalf0 hhalf1
  have hp_eq : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) +
      (1 - 1 / 2 : ℝ) ^ ((1 : ℝ) / 3) = q ^ 2 := hp.mpr rfl
  rw [splittingF_eq_splittingFofP hhalf0 hhalf1, hp_eq, splittingFofP_q_sq]
  rw [criticalVolume_eq]
  ring

/-- Blueprint `thm:splitting`. -/
theorem splittingF_ge {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    criticalVolume / 5 ≤ splittingF s := by
  let p : ℝ := s ^ ((1 : ℝ) / 3) + (1 - s) ^ ((1 : ℝ) / 3)
  obtain ⟨_, _, _, hp, hp_le, _, _, _, _, _, _⟩ := splitting_substitution hs0 hs1
  have hq : 1 < q ^ 2 := by nlinarith [one_lt_q]
  have hmon : splittingFofP (q ^ 2) ≤ splittingFofP p := by
    rcases eq_or_lt_of_le hp_le with heq | hlt
    · rw [← heq]
    · exact le_of_lt (splittingFofP_strictAntiOn hp hq hlt)
  rw [splittingF_eq_splittingFofP hs0 hs1]
  change criticalVolume / 5 ≤ splittingFofP p
  calc
    criticalVolume / 5 = splittingFofP (q ^ 2) := by
      rw [criticalVolume_eq, splittingFofP_q_sq]
      ring
    _ ≤ splittingFofP p := hmon

private lemma scaling_pow_three {s : ℝ} (hs : 0 < s) :
    (s ^ (-(1 : ℝ) / 3)) ^ 3 * s = 1 := by
  calc
    _ = s ^ (-(1 : ℝ)) * s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      norm_num
    _ = s⁻¹ * s := by rw [Real.rpow_neg hs.le, Real.rpow_one]
    _ = 1 := inv_mul_cancel₀ hs.ne'

private lemma scaling_pow_two {s : ℝ} (hs : 0 < s) :
    s ^ ((5 : ℝ) / 3) * (s ^ (-(1 : ℝ) / 3)) ^ 2 = s := by
  calc
    _ = s ^ ((5 : ℝ) / 3 + (-(1 : ℝ) / 3) * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
      norm_num
    _ = s ^ (1 : ℝ) := by congr 1; ring
    _ = s := Real.rpow_one s

private lemma scaling_pow_five {s : ℝ} (hs : 0 < s) :
    s ^ ((5 : ℝ) / 3) * (s ^ (-(1 : ℝ) / 3)) ^ 5 = 1 := by
  calc
    _ = s ^ ((5 : ℝ) / 3 + (-(1 : ℝ) / 3) * 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
      norm_num
    _ = s ^ (0 : ℝ) := by congr 1; ring
    _ = 1 := Real.rpow_zero s

private lemma ballPerimeter_scale {V s : ℝ} (hV : 0 < V) (hs : 0 < s) :
    ballPerimeter (s * V) = ENNReal.ofReal (s ^ ((2 : ℝ) / 3)) * ballPerimeter V := by
  rw [ballPerimeter_eq_rpow (mul_pos hs hV), ballPerimeter_eq_rpow hV]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ s ^ ((2 : ℝ) / 3))]
  rw [Real.mul_rpow hs.le hV.le]
  congr 1
  ring

/-- Blueprint `lem:scaling-lower` (ENNReal form), modulo `thm:sharp-isoperimetric`. -/
theorem scaling_lower (hiso : SharpIsoperimetric) {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ENNReal.ofReal (s ^ ((5 : ℝ) / 3)) * valueFunction V +
        ENNReal.ofReal ((1 - s) * s ^ ((2 : ℝ) / 3)) * ballPerimeter V ≤
      valueFunction (s * V) := by
  refine le_iInf fun E => le_iInf fun hE => le_iInf fun hvol => ?_
  let r : ℝ := s ^ (-(1 : ℝ) / 3)
  have hr : 0 < r := Real.rpow_pos_of_pos hs0 _
  have hm : NullMeasurableSet ((fun x : AmbientSpace => r • x) '' E) volume := by
    apply nullMeasurableSet_image_of_differentiable
      (by fun_prop : Differentiable ℝ (fun x : AmbientSpace => r • x))
      (smul_right_injective _ hr.ne') hE
  have hvolF : volume ((fun x : AmbientSpace => r • x) '' E) =
      ENNReal.ofReal V := by
    rw [volume_image_smul E hr, hvol, ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    congr 1
    dsimp [r]
    calc
      _ = ((s ^ (-(1 : ℝ) / 3)) ^ 3 * s) * V := by ring
      _ = V := by rw [scaling_pow_three hs0]; ring
  have hvf := valueFunction_le hm hvolF
  have hscale : ENNReal.ofReal (s ^ ((5 : ℝ) / 3)) * valueFunction V ≤
      ENNReal.ofReal s * perimeter E + coulombEnergy E := by
    calc
      _ ≤ ENNReal.ofReal (s ^ ((5 : ℝ) / 3)) *
          energy ((fun x : AmbientSpace => r • x) '' E) :=
        mul_le_mul_of_nonneg_left hvf (by positivity)
      _ = _ := by
        rw [energy_smul hE hr, mul_add, ← mul_assoc, ← mul_assoc]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ s ^ ((5 : ℝ) / 3)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ s ^ ((5 : ℝ) / 3))]
        rw [show r = s ^ (-(1 : ℝ) / 3) from rfl,
          scaling_pow_two hs0, scaling_pow_five hs0]
        simp
  have hfin : volume E < ∞ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hpos : 0 < volume E := by
    rw [hvol]
    exact ENNReal.ofReal_pos.mpr (mul_pos hs0 hV)
  have hisoE := hiso.ballPerimeter_le hE hfin hpos
  have hreal : (volume E).toReal = s * V := by
    rw [hvol, ENNReal.toReal_ofReal (mul_pos hs0 hV).le]
  rw [hreal, ballPerimeter_scale hV hs0] at hisoE
  have hsecond : ENNReal.ofReal ((1 - s) * s ^ ((2 : ℝ) / 3)) *
      ballPerimeter V ≤ ENNReal.ofReal (1 - s) * perimeter E := by
    rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - s)]
    calc
      _ = ENNReal.ofReal (1 - s) *
          (ENNReal.ofReal (s ^ ((2 : ℝ) / 3)) * ballPerimeter V) := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hisoE (by positivity)
  calc
    _ ≤ (ENNReal.ofReal s * perimeter E + coulombEnergy E) +
        ENNReal.ofReal (1 - s) * perimeter E := add_le_add hscale hsecond
    _ = energy E := by
      rw [energy, add_right_comm, ← add_mul,
        ← ENNReal.ofReal_add hs0.le (by linarith : 0 ≤ 1 - s)]
      norm_num

/-- Blueprint `lem:scaling-lower`, real form. -/
theorem scaling_lower_toReal (hiso : SharpIsoperimetric) {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    s ^ ((5 : ℝ) / 3) * (valueFunction V).toReal +
        (1 - s) * s ^ ((2 : ℝ) / 3) * (ballPerimeter V).toReal ≤
      (valueFunction (s * V)).toReal := by
  have ha : ENNReal.ofReal (s ^ ((5 : ℝ) / 3)) * valueFunction V < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (valueFunction_lt_top hV)
  have hb : ENNReal.ofReal ((1 - s) * s ^ ((2 : ℝ) / 3)) *
      ballPerimeter V < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hV)
  have h := ENNReal.toReal_mono (valueFunction_lt_top (mul_pos hs0 hV)).ne
    (scaling_lower hiso hV hs0 hs1)
  rw [ENNReal.toReal_add ha.ne hb.ne, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ s ^ ((5 : ℝ) / 3)),
    ENNReal.toReal_ofReal
      (mul_nonneg (by linarith : 0 ≤ 1 - s)
        (by positivity : 0 ≤ s ^ ((2 : ℝ) / 3)))] at h
  exact h

private lemma splitting_power_identity {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - s) * s ^ ((2 : ℝ) / 3) + s * (1 - s) ^ ((2 : ℝ) / 3) =
      splittingN s + splittingD s := by
  have ht : 0 < 1 - s := by linarith
  have hs : s * s ^ ((2 : ℝ) / 3) = s ^ ((5 : ℝ) / 3) := by
    calc
      _ = s ^ (1 : ℝ) * s ^ ((2 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = s ^ ((5 : ℝ) / 3) := by
        rw [← Real.rpow_add hs0]
        congr 1
        ring
  have ht' : (1 - s) * (1 - s) ^ ((2 : ℝ) / 3) =
      (1 - s) ^ ((5 : ℝ) / 3) := by
    calc
      _ = (1 - s) ^ (1 : ℝ) * (1 - s) ^ ((2 : ℝ) / 3) := by
        rw [Real.rpow_one]
      _ = (1 - s) ^ ((5 : ℝ) / 3) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
  unfold splittingN splittingD
  nlinarith [hs, ht']

/-- Blueprint `lem:two-piece`, modulo `thm:sharp-isoperimetric`. -/
theorem two_piece (hiso : SharpIsoperimetric) {V s : ℝ} (hV : 0 < V)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (ballPerimeter V).toReal * splittingD s * (splittingF s - V / 5) ≤
      (valueFunction (s * V)).toReal + (valueFunction ((1 - s) * V)).toReal -
        (valueFunction V).toReal := by
  have ht0 : 0 < 1 - s := by linarith
  have ht1 : 1 - s < 1 := by linarith
  have h1 := scaling_lower_toReal hiso hV hs0 hs1
  have h2 := scaling_lower_toReal hiso hV ht0 ht1
  have h2' : (1 - s) ^ ((5 : ℝ) / 3) * (valueFunction V).toReal +
      s * (1 - s) ^ ((2 : ℝ) / 3) * (ballPerimeter V).toReal ≤
      (valueFunction ((1 - s) * V)).toReal := by
    convert h2 using 1; ring_nf
  have hballfin : energy (ballByVolume V) < ∞ := by
    rw [energy_ballByVolume hV]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballPerimeter_lt_top hV)
  have hm : (valueFunction V).toReal ≤
      (V + 5) / 5 * (ballPerimeter V).toReal := by
    rw [← energy_ballByVolume_toReal hV]
    exact ENNReal.toReal_mono hballfin.ne (valueFunction_le_ball hV)
  have hdpos := splittingD_pos hs0 hs1
  have hneg : -(splittingD s) * ((V + 5) / 5 * (ballPerimeter V).toReal) ≤
      -(splittingD s) * (valueFunction V).toReal :=
    mul_le_mul_of_nonpos_left hm (by linarith)
  have hdn : splittingD s * splittingF s = splittingN s := by
    unfold splittingF
    field_simp [ne_of_gt hdpos]
  have hid := splitting_power_identity hs0 hs1
  have hsum := add_le_add h1 h2'
  have hdsum : s ^ ((5 : ℝ) / 3) + (1 - s) ^ ((5 : ℝ) / 3) =
      1 - splittingD s := by unfold splittingD; ring
  calc
    (ballPerimeter V).toReal * splittingD s * (splittingF s - V / 5) =
        -(splittingD s) * ((V + 5) / 5 * (ballPerimeter V).toReal) +
          ((1 - s) * s ^ ((2 : ℝ) / 3) +
            s * (1 - s) ^ ((2 : ℝ) / 3)) * (ballPerimeter V).toReal := by
      rw [hid]
      calc
        _ = (ballPerimeter V).toReal * (splittingD s * splittingF s) -
            (ballPerimeter V).toReal * splittingD s * V / 5 := by ring
        _ = (ballPerimeter V).toReal * splittingN s -
            (ballPerimeter V).toReal * splittingD s * V / 5 := by rw [hdn]
        _ = _ := by ring
    _ ≤ -(splittingD s) * (valueFunction V).toReal +
          ((1 - s) * s ^ ((2 : ℝ) / 3) +
            s * (1 - s) ^ ((2 : ℝ) / 3)) * (ballPerimeter V).toReal := by
      linarith [hneg]
    _ ≤ (valueFunction (s * V)).toReal +
          (valueFunction ((1 - s) * V)).toReal - (valueFunction V).toReal := by
      nlinarith [congrArg (fun x : ℝ => x * (valueFunction V).toReal) hdsum]

end LiquidDrop
