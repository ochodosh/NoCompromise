module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

namespace LiquidDrop

theorem rpow_two_thirds_strict_superadditive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) ^ ((2 : ℝ) / 3) < a ^ ((2 : ℝ) / 3) + b ^ ((2 : ℝ) / 3) := by
  let c := a + b
  let u := a / c
  let v := b / c
  have hc : 0 < c := by dsimp [c]; linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hu1 : u < 1 := by
    dsimp [u, c]
    rw [div_lt_one (by positivity)]
    linarith
  have hv1 : v < 1 := by
    dsimp [v, c]
    rw [div_lt_one (by positivity)]
    linarith
  have hpowu : u < u ^ ((2 : ℝ) / 3) := by
    have := Real.rpow_lt_rpow_of_exponent_gt hu hu1 (by norm_num : (2 : ℝ) / 3 < 1)
    simpa using this
  have hpowv : v < v ^ ((2 : ℝ) / 3) := by
    have := Real.rpow_lt_rpow_of_exponent_gt hv hv1 (by norm_num : (2 : ℝ) / 3 < 1)
    simpa using this
  have hau : a = c * u := by dsimp [c, u]; field_simp
  have hbv : b = c * v := by dsimp [c, v]; field_simp
  have hsum : u + v = 1 := by dsimp [u, v, c]; field_simp
  have hcu : c * u + c * v = c := by
    rw [← mul_add, hsum, mul_one]
  rw [hau, hbv, Real.mul_rpow (le_of_lt hc) (le_of_lt hu),
    Real.mul_rpow (le_of_lt hc) (le_of_lt hv)]
  rw [hcu]
  calc
    c ^ ((2 : ℝ) / 3) = c ^ ((2 : ℝ) / 3) * 1 := by ring
    _ = c ^ ((2 : ℝ) / 3) * (u + v) := by rw [hsum]
    _ < c ^ ((2 : ℝ) / 3) * (u ^ ((2 : ℝ) / 3) + v ^ ((2 : ℝ) / 3)) := by
      apply mul_lt_mul_of_pos_left _ (Real.rpow_pos_of_pos hc _)
      linarith
    _ = c ^ ((2 : ℝ) / 3) * u ^ ((2 : ℝ) / 3) +
        c ^ ((2 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) := by ring

end LiquidDrop
