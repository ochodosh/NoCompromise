import NoCompromise.Elliptic.BoundaryHolderHalfScaling
import NoCompromise.Elliptic.CampanatoHolderAverages

/-! Positive half-ball volume and quantitative comparison of actual half-ball
averages. No pointwise representative or boundary Lebesgue-point premise is used. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundaryHalfBall_volume_pos {r : ℝ} (hr : 0 < r) :
    0 < volume (boundaryHalfBall r) := by
  apply (isOpen_boundaryHalfBall r).measure_pos volume
  refine ⟨EuclideanSpace.single (Fin.last 2) (r / 2), ?_, ?_⟩
  · change dist (EuclideanSpace.single (Fin.last 2) (r / 2)) 0 < r
    rw [dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  · change 0 < EuclideanSpace.single (Fin.last 2) (r / 2) (Fin.last 2)
    simp only [PiLp.single_apply, ite_true]
    positivity

lemma boundaryHalfBall_real_volume_scaling {r : ℝ} (hr : 0 < r) (s : ℝ) :
    volume.real (boundaryHalfBall (r * s)) = r ^ 3 * volume.real (boundaryHalfBall s) := by
  have h := boundary_integral_halfBall_comp_scaling (fun _ => (1 : ℝ)) hr s
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ] at h
  change volume.real (boundaryHalfBall s) =
    (r ^ 3)⁻¹ * volume.real (boundaryHalfBall (r * s)) at h
  rw [h]
  field_simp [hr.ne']

lemma boundaryHalfBall_real_volume {r : ℝ} (hr : 0 < r) :
    volume.real (boundaryHalfBall r) = r ^ 3 * volume.real (boundaryHalfBall 1) := by
  simpa only [mul_one] using boundaryHalfBall_real_volume_scaling hr 1

lemma boundaryHalfBall_volume_double {r : ℝ} (_hr : 0 < r) :
    volume.real (boundaryHalfBall r) = 8 * volume.real (boundaryHalfBall (r / 2)) := by
  have h := boundaryHalfBall_real_volume_scaling (by norm_num : (0 : ℝ) < 2) (r / 2)
  simpa only [show (2 : ℝ) * (r / 2) = r by ring, show (2 : ℝ) ^ 3 = 8 by norm_num] using h

/-- A concentric half-ball of at least half the radius has a controlled average,
using only the normal excess on the larger half-ball. -/
theorem boundary_average_comparable_radius_bound
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {r s B γ : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hhalf : r / 2 ≤ s) (hsr : s ≤ r)
    (hf : MemLp f 2 (volume.restrict (boundaryHalfBall r)))
    (hosc : boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) f
        (volume.restrict (boundaryHalfBall r)) ≤
      (B * r ^ γ) ^ 2 * volume.real (boundaryHalfBall r)) :
    ‖(⨍ y in boundaryHalfBall s, f y) - ⨍ y in boundaryHalfBall r, f y‖ ≤
      Real.sqrt 8 * B * r ^ γ := by
  have hs : 0 < s := (div_pos hr (by norm_num : (0 : ℝ) < 2)).trans_le hhalf
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall r)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top r⟩
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall s)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top s⟩
  have hm : volume (boundaryHalfBall s) ≠ 0 := (boundaryHalfBall_volume_pos hs).ne'
  have hmreal : 0 < volume.real (boundaryHalfBall s) :=
    ENNReal.toReal_pos hm (boundaryHalfBall_volume_lt_top s).ne
  have hvol : volume.real (boundaryHalfBall r) ≤ 8 * volume.real (boundaryHalfBall s) := by
    rw [boundaryHalfBall_volume_double hr]
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono (boundaryHalfBall_mono hhalf) (boundaryHalfBall_volume_lt_top s).ne)
      (by norm_num)
  have hj := campanato_average_sub_average_sq_le
    (by simpa using hm) (Measure.restrict_mono (boundaryHalfBall_mono hsr) le_rfl) hf
  simp only [Measure.real, Measure.restrict_apply_univ] at hj
  have hvar := (boundary_variance_le_normal_excess hf
    (EuclideanSpace.single (Fin.last 2) 1)).trans hosc
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (volume.real (boundaryHalfBall s))⁻¹ *
        (∫ y in boundaryHalfBall r, ‖f y - ⨍ w in boundaryHalfBall r, f w‖ ^ 2) := hj
    _ ≤ (volume.real (boundaryHalfBall s))⁻¹ *
        ((B * r ^ γ) ^ 2 * volume.real (boundaryHalfBall r)) :=
      mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hmreal.le)
    _ ≤ (volume.real (boundaryHalfBall s))⁻¹ *
        ((B * r ^ γ) ^ 2 * (8 * volume.real (boundaryHalfBall s))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol (sq_nonneg _))
        (inv_nonneg.mpr hmreal.le)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
      field_simp [hmreal.ne']

end LiquidDrop
