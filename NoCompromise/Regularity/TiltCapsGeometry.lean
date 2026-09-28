import NoCompromise.Regularity.TiltGeometry
import NoCompromise.Regularity.IsometryCylinders

/-! # Heights and sizes of actual rotated cap points -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma norm_graphAppendN_le (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ‖graphAppendN p t‖ ≤ ‖p‖ + |t| := by
  have h := norm_graphAppendN_sq p t
  nlinarith [norm_nonneg p, norm_nonneg (graphAppendN p t), abs_nonneg t, sq_abs t]

lemma norm_graphAppendN_zero (p : EuclideanSpace ℝ (Fin 2)) :
    ‖graphAppendN p 0‖ = ‖p‖ := by
  have h := norm_graphAppendN_sq p 0
  nlinarith [norm_nonneg p, norm_nonneg (graphAppendN p 0)]

lemma linearIsometry_graphAppend_decomposition (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    Q (graphAppendN p t) = t • Q (EuclideanSpace.single 2 1) + Q (graphAppendN p 0) := by
  change Q (graphBaseN 2 p + t • EuclideanSpace.single 2 1) =
    t • Q (EuclideanSpace.single 2 1) + Q (graphBaseN 2 p + 0 • EuclideanSpace.single 2 1)
  simp only [map_add, map_smul, zero_smul, zero_add, add_comm]

lemma linearIsometry_cap_heights (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    {p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hp : p ∈ ball 0 r)
    (hclose : ‖Q (EuclideanSpace.single 2 1) - EuclideanSpace.single 2 1‖ ≤ 1 / 8) :
    r / 2 < Q (graphAppendN p r) 2 ∧ Q (graphAppendN p (-r)) 2 < -(r / 2) := by
  have hy : inner ℝ (Q (EuclideanSpace.single 2 1)) (Q (graphAppendN p 0)) = 0 := by
    rw [Q.inner_map_map]
    simp [EuclideanSpace.inner_single_left, graphAppendN_height_three]
  have hyr : ‖Q (graphAppendN p 0)‖ < r := by
    rw [Q.norm_map, norm_graphAppendN_zero]
    exact mem_ball_zero_iff.mp hp
  have hh := tilted_cap_heights hr hclose hy hyr
  constructor
  · rw [linearIsometry_graphAppend_decomposition Q p r]
    exact hh.1
  · rw [linearIsometry_graphAppend_decomposition Q p (-r)]
    exact hh.2

lemma linearIsometry_cap_norm_lt (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    {p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hp : p ∈ ball 0 r) :
    ‖Q (graphAppendN p r)‖ < 2 * r ∧ ‖Q (graphAppendN p (-r))‖ < 2 * r := by
  have hp' := mem_ball_zero_iff.mp hp
  rw [Q.norm_map, Q.norm_map]
  have hu := norm_graphAppendN_le p r
  have hl := norm_graphAppendN_le p (-r)
  rw [abs_of_pos hr] at hu
  rw [abs_neg, abs_of_pos hr] at hl
  constructor <;> linarith

end LiquidDrop
