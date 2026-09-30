module

public import NoCompromise.Ball.Defs
public import NoCompromise.Area.Sphere
public import NoCompromise.Sobolev.AnnulusDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Exact volume and perimeter of a ball

The perimeter is the original variational definition. Its equality with sphere
area follows from the proved C¹-domain theorem and the normalized Hausdorff
sphere formula. The remaining radius/volume identities are exact real algebra.
-/

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal
namespace LiquidDrop

lemma ballRadius_pos {V : ℝ} (hV : 0 < V) : 0 < ballRadius V := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma ballRadius_cube {V : ℝ} (hV : 0 < V) :
    ballRadius V ^ 3 = 3 * V / (4 * Real.pi) := by
  rw [ballRadius, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 * V / (4 * Real.pi))]
  norm_num

lemma volume_ball_eq_ofReal (c : AmbientSpace) {R : ℝ} (hR : 0 ≤ R) :
    volume (ball c R) = ENNReal.ofReal (4 * Real.pi * R ^ 3 / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_mul (pow_nonneg hR 3)]
  congr 1
  ring

/-- The variational perimeter of a positive-radius ball equals its actual sphere area. -/
theorem perimeter_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    perimeter (ball c R) = ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  rw [(hasC1Boundary_ball c hR).perimeter_eq_boundaryArea isOpen_ball,
    hausdorffMeasure2_frontier_ball c hR]

lemma hasFinitePerimeter_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    HasFinitePerimeter (ball c R) :=
  (hasC1Boundary_ball c hR).hasFinitePerimeter isOpen_ball isBounded_ball

lemma volume_ballByVolume {V : ℝ} (hV : 0 < V) :
    volume (ballByVolume V) = ENNReal.ofReal V := by
  rw [ballByVolume, volume_ball_eq_ofReal _ (ballRadius_pos hV).le, ballRadius_cube hV]
  congr 1
  field_simp

lemma ballPerimeter_eq_radius {V : ℝ} (hV : 0 < V) :
    ballPerimeter V = ENNReal.ofReal (4 * Real.pi * ballRadius V ^ 2) :=
  perimeter_ball 0 (ballRadius_pos hV)

lemma ballPerimeter_toReal_eq_radius {V : ℝ} (hV : 0 < V) :
    (ballPerimeter V).toReal = 4 * Real.pi * ballRadius V ^ 2 := by
  rw [ballPerimeter_eq_radius hV, ENNReal.toReal_ofReal (by positivity)]

lemma ballPerimeter_pos {V : ℝ} (hV : 0 < V) : 0 < ballPerimeter V := by
  rw [ballPerimeter_eq_radius hV]
  exact ENNReal.ofReal_pos.mpr (by have := ballRadius_pos hV; positivity)

lemma ballPerimeter_lt_top {V : ℝ} (hV : 0 < V) : ballPerimeter V < ∞ := by
  rw [ballPerimeter_eq_radius hV]
  exact ENNReal.ofReal_lt_top

lemma radius_mul_ballPerimeter {V : ℝ} (hV : 0 < V) :
    ballRadius V * (ballPerimeter V).toReal = 3 * V := by
  rw [ballPerimeter_toReal_eq_radius hV]
  calc
    _ = 4 * Real.pi * ballRadius V ^ 3 := by ring
    _ = _ := by rw [ballRadius_cube hV]; field_simp

lemma ballPerimeter_radius_eq_rpow {V : ℝ} (hV : 0 < V) :
    4 * Real.pi * ballRadius V ^ 2 = (36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ)) := by
  have hc : ((36 * Real.pi) ^ (1 / (3 : ℝ))) ^ 3 = 36 * Real.pi := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 36 * Real.pi)]
    norm_num
  have hv : (V ^ (2 / (3 : ℝ))) ^ 3 = V ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]
    norm_num
  have hp : (4 * Real.pi * ballRadius V ^ 2) ^ 3 =
      ((36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ))) ^ 3 := by
    conv_rhs => rw [mul_pow, hc, hv]
    calc
      _ = (4 * Real.pi) ^ 3 * (ballRadius V ^ 3) ^ 2 := by ring
      _ = _ := by rw [ballRadius_cube hV]; field_simp; ring
  exact (pow_left_inj₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hp

lemma ballPerimeter_eq_rpow {V : ℝ} (hV : 0 < V) :
    ballPerimeter V = ENNReal.ofReal
      ((36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ))) := by
  rw [ballPerimeter_eq_radius hV, ballPerimeter_radius_eq_rpow hV]

lemma ballPerimeter_toReal_eq_rpow {V : ℝ} (hV : 0 < V) :
    (ballPerimeter V).toReal = (36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ)) := by
  rw [ballPerimeter_toReal_eq_radius hV, ballPerimeter_radius_eq_rpow hV]

/-- All volume, perimeter and radius identities for the prescribed-volume ball. -/
theorem ball_volume_perimeter {V : ℝ} (hV : 0 < V) :
    volume (ballByVolume V) = ENNReal.ofReal V ∧
      ballPerimeter V = ENNReal.ofReal (4 * Real.pi * ballRadius V ^ 2) ∧
      ballPerimeter V = ENNReal.ofReal
        ((36 * Real.pi) ^ (1 / (3 : ℝ)) * V ^ (2 / (3 : ℝ))) ∧
      ballRadius V * (ballPerimeter V).toReal = 3 * V :=
  ⟨volume_ballByVolume hV, ballPerimeter_eq_radius hV, ballPerimeter_eq_rpow hV,
    radius_mul_ballPerimeter hV⟩

end LiquidDrop
