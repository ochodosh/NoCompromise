import NoCompromise.Regularity.SlabCap
import NoCompromise.DeGiorgi.BlowupPolar

/-! # Exact cylinder covariance under positive translation and dilation -/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- Cylinder membership commutes exactly with positive affine scaling, for any axis. -/
lemma mem_cylinder_translate_pos_smul (x y z ν : AmbientSpace) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    x + r • z ∈ cylinder (x + r • y) (r * R) ν ↔ z ∈ cylinder y R ν := by
  have he : x + r • z - (x + r • y) = r • (z - y) := by module
  simp only [cylinder, mem_ofPred_eq, he, map_smul, norm_smul,
    Real.norm_of_nonneg hr.le, inner_smul_right, abs_mul, abs_of_pos hr,
    mul_lt_mul_iff_right₀ hr]

/-- Every intrinsic cylinder has the exact affine-scaled image. -/
theorem image_cylinder_translate_pos_smul (x y ν : AmbientSpace) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (fun z => x + r • z) '' cylinder y R ν = cylinder (x + r • y) (r * R) ν := by
  apply ((blowupHomeomorph x hr).toEquiv.eq_preimage_iff_image_eq _ _).mp
  ext z
  exact (mem_cylinder_translate_pos_smul x y z ν hr R).symm

/-- The standard cylinder is sent to the corresponding cylinder with translated center. -/
theorem image_standardCylinder_translate_pos_smul (x : AmbientSpace) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (fun z => x + r • z) '' standardCylinder R =
      cylinder x (r * R) (EuclideanSpace.single 2 1) := by
  rw [standardCylinder_eq_cylinder, image_cylinder_translate_pos_smul x 0 _ hr R]
  simp only [smul_zero, add_zero]

/-- At the origin, the affine image formula becomes exact standard-cylinder scaling. -/
theorem image_standardCylinder_pos_smul {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun z : AmbientSpace => r • z) '' standardCylinder R = standardCylinder (r * R) := by
  simpa only [zero_add, ← standardCylinder_eq_cylinder] using
    image_standardCylinder_translate_pos_smul (0 : AmbientSpace) hr R

end LiquidDrop
