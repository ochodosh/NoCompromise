module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# Scalar perturbation estimate for the far-field Bochner expansion

Normalize the square root as `sqrt S = (C / r²) * a`. The relation
`a² = 1 + 6u + g` makes the normalized remainder a polynomial divisible by
`(a - 1)²`, up to the three input errors. This exact factorization avoids
Taylor estimates and supplies explicit radius and remainder constants.
-/

namespace LiquidDrop.CapacitaryK

/-- Exact cancellation leaves a quadratic square-root error and linear input errors. -/
private theorem scalar_algebra {a u e f g : ℝ}
    (ha : (1 : ℝ) / 2 ≤ a) (ha' : a ≤ 2) (hs : a ^ 2 = 1 + 6 * u + g) :
    |(6 + 72 * u + e) / a - (4 + 72 * u + f) / a ^ 3 - 2 - 18 * u| ≤
      8 * (88 * (a - 1) ^ 2 + 84 * |g| + 4 * |e| + |f|) := by
  have ha0 : 0 < a := by linarith
  have ha2 : a ^ 2 ≤ 4 := by nlinarith
  have ha3 : a ^ 3 ≤ 8 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - a by linarith)
      (show 0 ≤ a ^ 2 + 2 * a + 4 by positivity)]
  have ha3low : (1 : ℝ) / 8 ≤ a ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ a - 1 / 2 by linarith)
      (show 0 ≤ a ^ 2 + a / 2 + 1 / 4 by positivity)]
  have hq : |-3 * a ^ 3 + 6 * a ^ 2 + 16 * a + 8| ≤ 88 := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg ha0.le 3, sq_nonneg a]
  have hg : |3 * a ^ 3 - 12 * a ^ 2 + 12| ≤ 84 := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg ha0.le 3, sq_nonneg a]
  have hid : (6 + 72 * u + e) / a - (4 + 72 * u + f) / a ^ 3 - 2 - 18 * u =
      ((a - 1) ^ 2 * (-3 * a ^ 3 + 6 * a ^ 2 + 16 * a + 8) +
        g * (3 * a ^ 3 - 12 * a ^ 2 + 12) + e * a ^ 2 - f) / a ^ 3 := by
    field_simp [ha0.ne']
    nlinarith [congrArg (fun x : ℝ => (a ^ 2 * 12 - a ^ 3 * 3 - 12) * x) hs]
  rw [hid, abs_div, abs_of_pos (pow_pos ha0 3)]
  apply (div_le_iff₀ (pow_pos ha0 3)).mpr
  have hb : |(a - 1) ^ 2 * (-3 * a ^ 3 + 6 * a ^ 2 + 16 * a + 8) +
      g * (3 * a ^ 3 - 12 * a ^ 2 + 12) + e * a ^ 2 - f| ≤
      88 * (a - 1) ^ 2 + 84 * |g| + 4 * |e| + |f| := by
    calc
      _ ≤ |(a - 1) ^ 2 * (-3 * a ^ 3 + 6 * a ^ 2 + 16 * a + 8)| +
          |g * (3 * a ^ 3 - 12 * a ^ 2 + 12)| + |e * a ^ 2| + |f| := by
        apply (abs_sub _ _).trans
        apply add_le_add
        · apply (abs_add_le _ _).trans
          exact add_le_add (abs_add_le _ _) le_rfl
        · exact le_rfl
      _ = (a - 1) ^ 2 * |-3 * a ^ 3 + 6 * a ^ 2 + 16 * a + 8| +
          |g| * |3 * a ^ 3 - 12 * a ^ 2 + 12| + |e| * a ^ 2 + |f| := by
        simp only [abs_mul, abs_pow, sq_abs]
      _ ≤ (a - 1) ^ 2 * 88 + |g| * 84 + |e| * 4 + |f| := by gcongr
      _ = _ := by ring
  have hb0 : 0 ≤ 88 * (a - 1) ^ 2 + 84 * |g| + 4 * |e| + |f| := by positivity
  nlinarith [mul_nonneg hb0 (show 0 ≤ 8 * a ^ 3 - 1 by linarith)]

private theorem scalar_scale_error {x L r c : ℝ} {m n : ℕ}
    (hr : 0 < r) (hc : 0 < c) (hx : |x| ≤ L / r ^ (m + n)) :
    |x * r ^ m / c| ≤ (L / c) / r ^ n := by
  rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos (pow_pos hr m)]
  calc
    _ ≤ (L / r ^ (m + n)) * r ^ m / c := by gcongr
    _ = _ := by rw [pow_add]; field_simp

/-- The scalar remainder estimate in the far-field Bochner expansion. -/
theorem bochner_scalar_perturbation {C B K : ℝ} (hC : 0 < C) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ R' K' : ℝ, 0 < R' ∧ ∀ (r h N P S : ℝ), R' ≤ r → |h| ≤ B / r ^ 3 →
      |N - (6 * C ^ 2 / r ^ 6 + 72 * C * h / r ^ 5)| ≤ K / r ^ 9 →
      |P - (4 * C ^ 4 / r ^ 10 + 72 * C ^ 3 * h / r ^ 9)| ≤ K / r ^ 13 →
      |S - (C ^ 2 / r ^ 4 + 6 * C * h / r ^ 3)| ≤ K / r ^ 7 →
      0 < S ∧
      |N / Real.sqrt S - P / Real.sqrt S ^ 3 - 2 * C / r ^ 4 - 18 * h / r ^ 3| ≤ K' / r ^ 7 := by
  let D := 6 * (B / C) + K / C ^ 2
  let E := K / C ^ 2
  let F := K / C ^ 4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨2 * D + 1, 8 * C * (88 * D ^ 2 + 88 * E + F), by positivity, ?_⟩
  intro r h N P S hr hh hN hP hS
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hrne := hr0.ne'
  have hCne := hC.ne'
  let u := h * r / C
  let e := (N - (6 * C ^ 2 / r ^ 6 + 72 * C * h / r ^ 5)) * r ^ 6 / C ^ 2
  let f := (P - (4 * C ^ 4 / r ^ 10 + 72 * C ^ 3 * h / r ^ 9)) * r ^ 10 / C ^ 4
  let g := (S - (C ^ 2 / r ^ 4 + 6 * C * h / r ^ 3)) * r ^ 4 / C ^ 2
  have hu : |u| ≤ (B / C) / r ^ 2 := by
    simpa [u] using scalar_scale_error (m := 1) (n := 2) hr0 hC hh
  have he : |e| ≤ E / r ^ 3 := scalar_scale_error (m := 6) (n := 3) hr0 (pow_pos hC 2) hN
  have hf : |f| ≤ F / r ^ 3 := scalar_scale_error (m := 10) (n := 3) hr0 (pow_pos hC 4) hP
  have hg : |g| ≤ E / r ^ 3 := scalar_scale_error (m := 4) (n := 3) hr0 (pow_pos hC 2) hS
  have hr23 : r ^ 2 ≤ r ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr1)]
  have hd : |6 * u + g| ≤ D / r ^ 2 := by
    calc
      _ ≤ 6 * |u| + |g| := by
        simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using
          abs_add_le (6 * u) g
      _ ≤ 6 * ((B / C) / r ^ 2) + E / r ^ 3 := by gcongr
      _ ≤ 6 * ((B / C) / r ^ 2) + E / r ^ 2 := by
        gcongr
      _ = _ := by dsimp [D, E]; ring
  have hdhalf : |6 * u + g| ≤ 1 / 2 := by
    apply hd.trans
    apply (div_le_iff₀ (pow_pos hr0 2)).mpr
    nlinarith only [hr, hr1, sq_nonneg (r - 1)]
  have hbase : 0 < 1 + 6 * u + g := by linarith only [(abs_le.mp hdhalf).1]
  let a := Real.sqrt (1 + 6 * u + g)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 1 + 6 * u + g := Real.sq_sqrt hbase.le
  have ha : (1 : ℝ) / 2 ≤ a := by nlinarith only [ha0, ha2, (abs_le.mp hdhalf).1]
  have ha' : a ≤ 2 := by nlinarith only [ha0, ha2, (abs_le.mp hdhalf).2]
  have ha_pos : 0 < a := by linarith
  have hSeq : S = C ^ 2 / r ^ 4 * (1 + 6 * u + g) := by
    dsimp [u, g]
    field_simp
    ring
  have hSpos : 0 < S := by rw [hSeq]; positivity
  refine ⟨hSpos, ?_⟩
  have hsqrt : Real.sqrt S = C / r ^ 2 * a := by
    apply (Real.sqrt_eq_iff_eq_sq hSpos.le (by positivity)).mpr
    rw [mul_pow, div_pow, ha2, hSeq]
    ring
  have had : |a - 1| ≤ D / r ^ 2 := by
    have hab : |a ^ 2 - 1| = |a - 1| * (a + 1) := by
      rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ a + 1)]
    have had' : |a ^ 2 - 1| ≤ D / r ^ 2 := by
      rw [ha2]
      convert hd using 1
      congr 1
      ring
    nlinarith only [hab, had', ha0, abs_nonneg (a - 1)]
  have had2 : (a - 1) ^ 2 ≤ D ^ 2 / r ^ 3 := by
    have hab := sq_abs (a - 1)
    have hsq : (a - 1) ^ 2 ≤ (D / r ^ 2) ^ 2 := by
      nlinarith only [hab, mul_nonneg (sub_nonneg.mpr had)
        (show 0 ≤ D / r ^ 2 + |a - 1| by positivity)]
    calc
      _ ≤ (D / r ^ 2) ^ 2 := hsq
      _ = D ^ 2 / r ^ 4 := by ring
      _ ≤ D ^ 2 / r ^ 3 := by
        apply div_le_div_of_nonneg_left (sq_nonneg D) (pow_pos hr0 3)
        nlinarith only [mul_nonneg (pow_nonneg hr0.le 3) (sub_nonneg.mpr hr1)]
  have hnorm := scalar_algebra ha ha' ha2 (e := e) (f := f)
  have hid : N / Real.sqrt S - P / Real.sqrt S ^ 3 - 2 * C / r ^ 4 - 18 * h / r ^ 3 =
      C / r ^ 4 * ((6 + 72 * u + e) / a - (4 + 72 * u + f) / a ^ 3 - 2 - 18 * u) := by
    rw [hsqrt]
    dsimp [u, e, f]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos (by positivity : 0 < C / r ^ 4)]
  calc
    _ ≤ C / r ^ 4 * (8 * (88 * (a - 1) ^ 2 + 84 * |g| + 4 * |e| + |f|)) := by
      gcongr
    _ ≤ C / r ^ 4 * (8 * (88 * (D ^ 2 / r ^ 3) + 84 * (E / r ^ 3) +
        4 * (E / r ^ 3) + F / r ^ 3)) := by gcongr
    _ = _ := by ring

end LiquidDrop.CapacitaryK
