import NoCompromise.Ball.Perimeter
import NoCompromise.Energy.Scaling
import NoCompromise.Threshold.Algebra
import Mathlib.Analysis.Normed.MulAction

/-!
# Half-volume balls and the exact comparison coefficients

The half-volume ball is the genuine dilation by the inverse cube root of two.
Its actual perimeter and Coulomb energy obey the corresponding scaling laws.
The affine comparison coefficients meet at the original critical volume.
-/

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal
namespace LiquidDrop

lemma ballRadius_half {V : ℝ} (hV : 0 < V) : ballRadius (V / 2) = ballRadius V / q := by
  apply (pow_left_inj₀ (ballRadius_pos (by positivity)).le
    (div_nonneg (ballRadius_pos hV).le q_pos.le) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [ballRadius_cube (by positivity), div_pow, ballRadius_cube hV, q_cube]
  ring

lemma ballByVolume_half {V : ℝ} (hV : 0 < V) :
    ballByVolume (V / 2) = (fun x : AmbientSpace => q⁻¹ • x) '' ballByVolume V := by
  rw [ballByVolume, ballByVolume, Metric.smul_image_ball (inv_ne_zero q_pos.ne'),
    smul_zero, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr q_pos), ballRadius_half hV,
    div_eq_mul_inv, mul_comm]

lemma ballPerimeter_half {V : ℝ} (hV : 0 < V) :
    ballPerimeter (V / 2) = ENNReal.ofReal (q⁻¹ ^ 2) * ballPerimeter V := by
  change perimeter (ballByVolume (V / 2)) = _
  rw [ballByVolume_half hV]
  exact perimeter_image_smul
    (show NullMeasurableSet (ballByVolume V) volume from
      isOpen_ball.measurableSet.nullMeasurableSet)
    (inv_pos.mpr q_pos)

lemma coulombEnergy_ball_half {V : ℝ} (hV : 0 < V) :
    coulombEnergy (ballByVolume (V / 2)) =
      ENNReal.ofReal (q⁻¹ ^ 5) * coulombEnergy (ballByVolume V) := by
  rw [ballByVolume_half hV, coulombEnergy_smul _ (inv_pos.mpr q_pos)]

lemma two_mul_inv_q_sq : (2 : ℝ) * q⁻¹ ^ 2 = q := by
  have hq := q_pos.ne'
  field_simp
  nlinarith [q_cube]

lemma two_mul_inv_q_fifth : (2 : ℝ) * q⁻¹ ^ 5 = q⁻¹ ^ 2 := by
  have hq := q_pos.ne'
  field_simp
  nlinarith [q_cube]

lemma two_ball_perimeter {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * ballPerimeter (V / 2) = ENNReal.ofReal q * ballPerimeter V := by
  rw [ballPerimeter_half hV, ← mul_assoc,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    two_mul_inv_q_sq]

/-- The actual energy of two half-volume balls expressed in terms of one ball's
perimeter and Coulomb energy, before using the explicit potential formula. -/
theorem two_ball_energy_scaling {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) =
      ENNReal.ofReal q * ballPerimeter V +
        ENNReal.ofReal (q⁻¹ ^ 2) * coulombEnergy (ballByVolume V) := by
  change (2 : ℝ≥0∞) * (ballPerimeter (V / 2) + coulombEnergy (ballByVolume (V / 2))) = _
  rw [mul_add, two_ball_perimeter hV, coulombEnergy_ball_half hV, ← mul_assoc,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    two_mul_inv_q_fifth]

lemma two_ball_coefficient_eq (V : ℝ) :
    q + V / (5 * q ^ 2) = (q ^ 2)⁻¹ * (V + 10) / 5 := by
  have hq := q_pos.ne'
  field_simp
  nlinarith [q_cube]

lemma one_sub_inv_q_sq_pos : 0 < 1 - (q ^ 2)⁻¹ := by
  have hsq : (1 : ℝ) < q ^ 2 := by nlinarith [one_lt_q]
  have hpos : 0 < q ^ 2 := by positivity
  have hi : (q ^ 2)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr hsq
  linarith

/-- The exact affine difference vanishes at the unchanged critical volume. -/
lemma ball_coefficient_difference (V : ℝ) :
    (V + 5) / 5 - (q + V / (5 * q ^ 2)) =
      (1 - (q ^ 2)⁻¹) / 5 * (V - criticalVolume) := by
  rw [two_ball_coefficient_eq]
  nlinarith [criticalVolume_identity]

lemma ball_coefficient_eq_iff (V : ℝ) :
    (V + 5) / 5 = q + V / (5 * q ^ 2) ↔ V = criticalVolume := by
  rw [← sub_eq_zero, ball_coefficient_difference]
  have hc : (1 - (q ^ 2)⁻¹) / 5 ≠ 0 := ne_of_gt (by
    exact div_pos one_sub_inv_q_sq_pos (by norm_num))
  simp only [mul_eq_zero, hc, false_or, sub_eq_zero]

lemma ball_coefficient_lt_iff (V : ℝ) :
    (V + 5) / 5 < q + V / (5 * q ^ 2) ↔ V < criticalVolume := by
  rw [← sub_neg, ball_coefficient_difference]
  have hc : 0 < (1 - (q ^ 2)⁻¹) / 5 := div_pos one_sub_inv_q_sq_pos (by norm_num)
  constructor <;> intro hh <;> nlinarith

lemma ball_coefficient_gt_iff (V : ℝ) :
    q + V / (5 * q ^ 2) < (V + 5) / 5 ↔ criticalVolume < V := by
  rw [← sub_pos, ball_coefficient_difference]
  have hc : 0 < (1 - (q ^ 2)⁻¹) / 5 := div_pos one_sub_inv_q_sq_pos (by norm_num)
  exact (mul_pos_iff_of_pos_left hc).trans sub_pos

end LiquidDrop
