module

public import NoCompromise.Regularity.TiltGeometry

@[expose] public section

/-! # Distance to the affine plane associated with a graph slope -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma inner_graphNormalVector_eq (p : EuclideanSpace ℝ (Fin 2)) (y : AmbientSpace) :
    inner ℝ (graphNormalVector p) y = y 2 - inner ℝ p (graphProjectionN 2 y) := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, graphProjectionN_apply]
  ring

lemma graphUnitNormal_affine_height_eq (p : EuclideanSpace ℝ (Fin 2))
    (y : AmbientSpace) (b : ℝ) :
    inner ℝ (graphUnitNormal p) y - b / Real.sqrt (1 + ‖p‖ ^ 2) =
      (y 2 - b - inner ℝ p (graphProjectionN 2 y)) / Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [graphUnitNormal, real_inner_smul_left, inner_graphNormalVector_eq]
  ring

lemma graphUnitNormal_affine_height_le (p : EuclideanSpace ℝ (Fin 2))
    (y : AmbientSpace) (b : ℝ) :
    |inner ℝ (graphUnitNormal p) y - b / Real.sqrt (1 + ‖p‖ ^ 2)| ≤
      |y 2| + |b| + ‖p‖ * ‖graphProjectionN 2 y‖ := by
  have hs : 1 ≤ Real.sqrt (1 + ‖p‖ ^ 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖p‖])
  rw [graphUnitNormal_affine_height_eq, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_self (abs_nonneg _) hs).trans
  have h1 : |y 2 - b - inner ℝ p (graphProjectionN 2 y)| ≤
      |y 2 - b| + |inner ℝ p (graphProjectionN 2 y)| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (y 2 - b) 0 (inner ℝ p (graphProjectionN 2 y))
  have h2 : |y 2 - b| ≤ |y 2| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (y 2) 0 b
  exact h1.trans (add_le_add h2 (abs_real_inner_le_norm _ _))

lemma graphUnitNormal_affine_offset_le (p : EuclideanSpace ℝ (Fin 2)) (b : ℝ) :
    |b / Real.sqrt (1 + ‖p‖ ^ 2)| ≤ |b| := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_self (abs_nonneg _)
  exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖p‖])

end LiquidDrop
