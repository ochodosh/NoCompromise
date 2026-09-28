import NoCompromise.Threshold.Defs
import Mathlib.Tactic

/-! # Exact threshold algebra

Blueprint `lem:Vstar-form`, `lem:Vstar-identity`, and `lem:Vstar-bounds`.
Natural-number powers such as `q ^ 3` are polynomial powers; the explicit real
exponents in `Defs` denote `Real.rpow`.
-/

namespace LiquidDrop

theorem q_pos : 0 < q := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem one_lt_q : 1 < q := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

theorem q_cube : q ^ 3 = 2 := by
  rw [q, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Bridge between the cube-root notation and the real power in the showcase. -/
theorem q_sq_eq_two_rpow : q ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [q, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem q_lt_four_thirds : q < 4 / 3 := by
  apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 4 / 3)
  rw [q_cube]
  norm_num

/-- Blueprint `lem:Vstar-form`, expressed using the original showcase constant. -/
theorem criticalVolume_eq : criticalVolume = 5 * q ^ 2 / (q + 1) := by
  have hden : q ^ 2 - 1 ≠ 0 := by nlinarith [one_lt_q]
  have hplus : q + 1 ≠ 0 := by linarith [q_pos]
  rw [criticalVolume, ← q_sq_eq_two_rpow]
  field_simp
  nlinarith [q_cube, congrArg (fun x : ℝ => x * q) q_cube]

/-- Blueprint `lem:Vstar-identity`. -/
theorem criticalVolume_identity : (q ^ 2)⁻¹ * (criticalVolume + 10) =
    criticalVolume + 5 := by
  have hq : q ≠ 0 := ne_of_gt q_pos
  have hplus : q + 1 ≠ 0 := by linarith [q_pos]
  rw [criticalVolume_eq]
  field_simp
  nlinarith [q_cube, congrArg (fun x : ℝ => x * q) q_cube]

theorem five_halves_lt_criticalVolume : 5 / 2 < criticalVolume := by
  rw [criticalVolume_eq]
  apply (lt_div_iff₀ (by linarith [q_pos] : 0 < q + 1)).2
  nlinarith [one_lt_q]

theorem criticalVolume_lt_four : criticalVolume < 4 := by
  rw [criticalVolume_eq]
  apply (div_lt_iff₀ (by linarith [q_pos] : 0 < q + 1)).2
  nlinarith [one_lt_q, q_lt_four_thirds,
    mul_nonneg (sub_nonneg.mpr (le_of_lt q_lt_four_thirds))
      (show 0 ≤ 5 * q + 8 / 3 by linarith [q_pos])]

theorem criticalVolume_pos : 0 < criticalVolume := by
  linarith [five_halves_lt_criticalVolume]

/-- Blueprint `lem:Vstar-bounds`. -/
theorem criticalVolume_bounds : 0 < criticalVolume ∧
    5 / 2 < criticalVolume ∧ criticalVolume < 4 ∧ (4 : ℝ) < 6 := by
  exact ⟨criticalVolume_pos, five_halves_lt_criticalVolume, criticalVolume_lt_four, by norm_num⟩

end LiquidDrop
