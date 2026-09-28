import NoCompromise.Regularity.TangentRepresentative
import NoCompromise.Regularity.SlabCap

/-! # Exact boundary and cylinder covariance for the height bound -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace LiquidDrop

lemma height_blowup_zero_eq_image (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r) :
    blowupSet E 0 r = (fun x => r⁻¹ • x) '' E := by
  ext y
  change (0 + r • y ∈ E) ↔ ∃ x ∈ E, r⁻¹ • x = y
  rw [zero_add]
  constructor
  · intro hy
    exact ⟨r • y, hy, by simp [smul_smul, hr.ne']⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hx

lemma height_frontier_blowup_zero (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r) :
    frontier (densityOne (blowupSet E 0 r)) =
      (fun x => r⁻¹ • x) '' frontier (densityOne E) := by
  rw [height_blowup_zero_eq_image E hr, tangent_densityOne_pos_smul E (inv_pos.mpr hr)]
  exact (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).image_frontier _ |>.symm

lemma height_mem_frontier_blowup_zero (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r)
    (x : AmbientSpace) :
    r⁻¹ • x ∈ frontier (densityOne (blowupSet E 0 r)) ↔ x ∈ frontier (densityOne E) := by
  rw [height_frontier_blowup_zero E hr]
  exact (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).injective.mem_set_image

lemma height_mem_standardCylinder_pos_smul (x : AmbientSpace) {s : ℝ} (hs : 0 < s)
    (r : ℝ) : s • x ∈ standardCylinder (s * r) ↔ x ∈ standardCylinder r := by
  change (‖graphProjectionN 2 (s • x)‖ < s * r ∧ |(s • x) 2| < s * r) ↔ _
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hs, PiLp.smul_apply, smul_eq_mul,
    abs_mul, abs_of_pos hs]
  exact and_congr (mul_lt_mul_iff_right₀ hs) (mul_lt_mul_iff_right₀ hs)

end LiquidDrop
