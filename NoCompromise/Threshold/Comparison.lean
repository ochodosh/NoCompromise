import NoCompromise.Threshold.BallSplitting
import NoCompromise.Ball.Potential

/-!
# One ball versus two equal balls

The comparison concerns the original liquid-drop energy of genuine
prescribed-volume balls. The exact Coulomb potential calculation supplies the
missing coefficient in the already proved scaling identities.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LiquidDrop

/-- Exact energy of two half-volume balls, expressed through the full ball's perimeter. -/
theorem two_ball_energy {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) =
      ENNReal.ofReal (q + V / (5 * q ^ 2)) * ballPerimeter V := by
  rw [two_ball_energy_scaling hV, coulombEnergy_ballByVolume hV, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg q⁻¹), ← add_mul,
    ← ENNReal.ofReal_add q_pos.le (by positivity)]
  congr 2
  have hq := q_pos.ne'
  field_simp

/-- The equivalent L/5 coefficient in the blueprint. -/
theorem two_ball_energy_eq_L {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) =
      ENNReal.ofReal ((q ^ 2)⁻¹ * (V + 10) / 5) * ballPerimeter V := by
  rw [two_ball_energy hV, two_ball_coefficient_eq]

/-- The exact energy tie occurs at the unchanged critical volume. -/
theorem ball_energy_eq_two_ball_iff {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) = (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) ↔
      V = criticalVolume := by
  have hq := q_pos
  rw [energy_ballByVolume hV, two_ball_energy hV,
    ENNReal.mul_left_inj (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity), ball_coefficient_eq_iff]

/-- One ball has smaller energy precisely below the critical volume. -/
theorem ball_energy_lt_two_ball_iff {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) < (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) ↔
      V < criticalVolume := by
  have hq := q_pos
  rw [energy_ballByVolume hV, two_ball_energy hV,
    ENNReal.mul_lt_mul_iff_left (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne,
    ENNReal.ofReal_lt_ofReal_iff (by positivity), ball_coefficient_lt_iff]

/-- Two equal balls have smaller energy precisely above the critical volume. -/
theorem two_ball_energy_lt_ball_iff {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) < energy (ballByVolume V) ↔
      criticalVolume < V := by
  rw [energy_ballByVolume hV, two_ball_energy hV,
    ENNReal.mul_lt_mul_iff_left (ballPerimeter_pos hV).ne' (ballPerimeter_lt_top hV).ne,
    ENNReal.ofReal_lt_ofReal_iff (by positivity), ball_coefficient_gt_iff]

/-- The complete one-ball versus two-equal-balls proposition, with actual energies. -/
theorem two_ball_comparison {V : ℝ} (hV : 0 < V) :
    (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) =
        ENNReal.ofReal ((q ^ 2)⁻¹ * (V + 10) / 5) * ballPerimeter V ∧
      (energy (ballByVolume V) = (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) ↔
        V = criticalVolume) ∧
      (energy (ballByVolume V) < (2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) ↔
        V < criticalVolume) ∧
      ((2 : ℝ≥0∞) * energy (ballByVolume (V / 2)) < energy (ballByVolume V) ↔
        criticalVolume < V) :=
  ⟨two_ball_energy_eq_L hV, ball_energy_eq_two_ball_iff hV,
    ball_energy_lt_two_ball_iff hV, two_ball_energy_lt_ball_iff hV⟩

end LiquidDrop
