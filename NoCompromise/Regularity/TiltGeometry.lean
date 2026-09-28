import NoCompromise.Regularity.GraphApproxHeight
import NoCompromise.Regularity.ApproxHarmonicAlgebra

/-! # Quantitative geometry of the new affine plane -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma graphUnitNormal_sub_vertical_le (p : EuclideanSpace ℝ (Fin 2)) :
    ‖graphUnitNormal p - EuclideanSpace.single 2 1‖ ≤ 2 * ‖p‖ := by
  let J := Real.sqrt (1 + ‖p‖ ^ 2)
  have hJ : 0 < J := Real.sqrt_pos.mpr (by positivity)
  have hJ1 : 1 ≤ J := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖p‖])
  have hJsq : J ^ 2 = 1 + ‖p‖ ^ 2 := Real.sq_sqrt (by positivity)
  have he : ‖graphUnitNormal p - EuclideanSpace.single 2 1‖ ^ 2 = 2 - 2 / J := by
    rw [norm_sub_sq_real, norm_graphUnitNormal]
    simp [EuclideanSpace.inner_single_right, approxHarmonic_graphUnitNormal_vertical,
      J, div_eq_mul_inv]
    ring
  have hb : 2 - 2 / J ≤ 4 * ‖p‖ ^ 2 := by
    have hcancel : (2 / J) * J = 2 := div_mul_cancel₀ _ hJ.ne'
    have hm := mul_nonneg (sq_nonneg ‖p‖) (sub_nonneg.mpr hJ1)
    nlinarith
  nlinarith [norm_nonneg (graphUnitNormal p - EuclideanSpace.single 2 1), norm_nonneg p]

lemma rotated_cylinder_two_subset_standard_three {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {θ : ℝ} (hθ : 0 < θ) : cylinder 0 (2 * θ) ν ⊆ standardCylinder (3 * θ) := by
  rw [standardCylinder_eq_cylinder]
  apply (cylinder_subset_ball 0 (by positivity) hν).trans
  apply (ball_subset_ball (show Real.sqrt 2 * (2 * θ) ≤ 3 * θ from ?_)).trans
    (ball_subset_cylinder 0 (3 * θ) (ν := EuclideanSpace.single 2 1) (by simp))
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb : 2 * Real.sqrt 2 ≤ 3 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  nlinarith

/-- Small change of axis leaves the two tilted caps on the correct sides of
the original horizontal slab. -/
lemma tilted_cap_heights {ν y : AmbientSpace} {r : ℝ} (hr : 0 < r)
    (hclose : ‖ν - EuclideanSpace.single 2 1‖ ≤ 1 / 8)
    (hy : inner ℝ ν y = 0) (hyr : ‖y‖ < r) :
    r / 2 < (r • ν + y) 2 ∧ ((-r) • ν + y) 2 < -(r / 2) := by
  have hν : |ν 2 - 1| ≤ 1 / 8 := by
    have hh := (PiLp.norm_apply_le (ν - EuclideanSpace.single 2 1) 2).trans hclose
    simpa using hh
  have hi : inner ℝ (EuclideanSpace.single 2 1 - ν) y = y 2 := by
    rw [inner_sub_left, EuclideanSpace.inner_single_left, hy]
    simp
  have hyabs : |y 2| ≤ (1 / 8 : ℝ) * ‖y‖ := by
    rw [← hi]
    apply (abs_real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
    simpa only [norm_sub_rev] using hclose
  have hlow := (abs_le.mp hν).1
  have hya := abs_le.mp hyabs
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> nlinarith

lemma tilted_cap_norm_sq {ν y : AmbientSpace} (hν : ‖ν‖ = 1)
    (hy : inner ℝ ν y = 0) (r : ℝ) : ‖r • ν + y‖ ^ 2 = r ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, hν, mul_one, sq_abs,
    inner_smul_left, hy]
  ring

end LiquidDrop
