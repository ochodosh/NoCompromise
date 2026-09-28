import NoCompromise.Elliptic.HolderInterpolationSplit

/-! Explicit polynomial scales for same-ball Hölder interpolation. A single
natural exponent is chosen from α before the radius and small parameter. -/

noncomputable section
open Metric Set
namespace LiquidDrop

lemma schauder_quantitative_interpolation_scales {a ε R : ℝ} {k : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hk : 1 ≤ (k : ℝ) * (1 - a))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : (1 / 2 : ℝ) ≤ R) :
    ∃ s t : ℝ, 0 < s ∧ s < R ∧ 0 < t ∧
      2 * s * (1 + 2 / t ^ a) + t ^ (1 - a) ≤ ε ∧
      (4 / s) * (1 + 2 / t ^ a) ≤
        (288 * (4 : ℝ) ^ (2 * k)) * (ε⁻¹) ^ (2 * k + 1) := by
  let t : ℝ := (ε / 4) ^ k
  let s : ℝ := ε * t / 24
  have hbase : 0 < ε / 4 := by positivity
  have hbase1 : ε / 4 ≤ 1 := by linarith
  have ht : 0 < t := pow_pos hbase k
  have ht1 : t ≤ 1 := pow_le_one₀ hbase.le hbase1
  have hs : 0 < s := by dsimp [s]; positivity
  have hsR : s < R := by
    have htt : ε * t ≤ 1 := (mul_le_mul hε1 ht1 ht.le zero_le_one).trans_eq (one_mul _)
    dsimp [s]
    linarith
  have htp : t ^ (1 - a) ≤ ε / 4 := by
    calc
      t ^ (1 - a) = (ε / 4) ^ ((k : ℝ) * (1 - a)) := by
        dsimp only [t]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
      _ ≤ (ε / 4) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hk
      _ = ε / 4 := Real.rpow_one _
  have hta : t ≤ t ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 ha1.le
  have htaPos : 0 < t ^ a := Real.rpow_pos_of_pos ht a
  let L : ℝ := 1 + 2 / t ^ a
  have hL : 0 < L := by dsimp [L]; positivity
  have htL : t * L ≤ 3 := by
    have hh : t / t ^ a ≤ 1 := (div_le_one htaPos).mpr hta
    calc
      t * L = t + 2 * (t / t ^ a) := by dsimp [L]; ring
      _ ≤ 1 + 2 * 1 := add_le_add ht1 (mul_le_mul_of_nonneg_left hh (by norm_num))
      _ = 3 := by norm_num
  have hsmall : 2 * s * L + t ^ (1 - a) ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left htL hε.le
    dsimp [s]
    nlinarith only [hm, htp, hε]
  have hLb : L ≤ 3 / t := (le_div_iff₀ ht).mpr (by nlinarith only [htL])
  refine ⟨s, t, hs, hsR, ht, hsmall, ?_⟩
  change (4 / s) * L ≤ _
  calc
    _ ≤ (4 / s) * (3 / t) := mul_le_mul_of_nonneg_left hLb (by positivity)
    _ = 288 * ε⁻¹ * (t⁻¹) ^ 2 := by
      dsimp [s]
      field_simp
      ring
    _ = (288 * (4 : ℝ) ^ (2 * k)) * (ε⁻¹) ^ (2 * k + 1) := by
      dsimp [t]
      simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, ← pow_mul]
      rw [Nat.mul_comm k 2, pow_succ]
      ring

end LiquidDrop
