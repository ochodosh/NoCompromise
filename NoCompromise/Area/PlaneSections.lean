module

public import NoCompromise.BV.Slicing
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Normalized Hausdorff measure of central planar sections

The previously proved planar parametrization identifies a central disk with
its Euclidean two-dimensional parameter disk. Its boundary circle is null for
the same normalized Hausdorff measure.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma coordinatePlaneParam_zero_zero :
    coordinatePlaneParam 0 (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by
  ext i
  fin_cases i <;> rfl

lemma norm_coordinatePlaneParam_zero (p : EuclideanSpace ℝ (Fin 2)) :
    ‖coordinatePlaneParam 0 p‖ = ‖p‖ := by
  simpa only [coordinatePlaneParam_zero_zero, dist_zero_right] using
    (isometry_coordinatePlaneParam 0).dist_eq p 0

lemma preimage_ball_coordinatePlaneParam_zero (R : ℝ) :
    coordinatePlaneParam 0 ⁻¹' ball (0 : AmbientSpace) R =
      ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
  ext p
  simp only [mem_preimage, mem_ball, dist_zero_right, norm_coordinatePlaneParam_zero]

lemma preimage_sphere_coordinatePlaneParam_zero (R : ℝ) :
    coordinatePlaneParam 0 ⁻¹' sphere (0 : AmbientSpace) R =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) R := by
  ext p
  simp only [mem_preimage, mem_sphere, dist_zero_right, norm_coordinatePlaneParam_zero]

/-- The normalized Hausdorff area of any central disk is exactly `π R²`. -/
theorem hausdorffMeasure2_central_plane_ball {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    hausdorffMeasure2 3 (ball (0 : AmbientSpace) R ∩ {x | inner ℝ x ν = 0}) =
      ENNReal.ofReal (Real.pi * R ^ 2) := by
  obtain ⟨e, he⟩ := exists_slicing_isometry hν
  have hpre : e ⁻¹' ball (0 : AmbientSpace) R = ball 0 R := by
    ext x
    simp only [mem_preimage, mem_ball, dist_zero_right, e.norm_map]
  rw [hausdorffMeasure2_plane_slice_isometry e he, hpre,
    hausdorffMeasure2_coordinate_slice, preimage_ball_coordinatePlaneParam_zero,
    EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_mul (sq_nonneg R)]
  congr 1
  ring

/-- The boundary circle of a central planar disk has zero two-dimensional area. -/
theorem hausdorffMeasure2_central_plane_sphere {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (R : ℝ) :
    hausdorffMeasure2 3 (sphere (0 : AmbientSpace) R ∩ {x | inner ℝ x ν = 0}) = 0 := by
  obtain ⟨e, he⟩ := exists_slicing_isometry hν
  have hpre : e ⁻¹' sphere (0 : AmbientSpace) R = sphere 0 R := by
    ext x
    simp only [mem_preimage, mem_sphere, dist_zero_right, e.norm_map]
  rw [hausdorffMeasure2_plane_slice_isometry e he, hpre,
    hausdorffMeasure2_coordinate_slice, preimage_sphere_coordinatePlaneParam_zero,
    Measure.addHaar_sphere]

end LiquidDrop
