import NoCompromise.Elliptic.BoundaryHolderTangentialGrowth

/-! Elementary ball geometry for the transition from flat-boundary estimates
to interior estimates. No boundary regularity is used in these comparisons. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_flat_projection_norm_le (x : EuclideanSpace ℝ (Fin 3)) :
    ‖graphAppendN (graphProjectionN 2 x) 0‖ ≤ ‖x‖ := by
  have h := norm_sq_graphProjectionN x
  have hp := norm_sq_graphProjectionN (graphAppendN (graphProjectionN 2 x) 0)
  simp only [graphProjectionN_append, graphAppendN_last, zero_pow (by decide : 2 ≠ 0),
    add_zero] at hp
  nlinarith [norm_nonneg x, norm_nonneg (graphAppendN (graphProjectionN 2 x) 0),
    sq_nonneg (x (Fin.last 2))]

lemma boundary_dist_flat_projection (x : EuclideanSpace ℝ (Fin 3)) :
    dist x (graphAppendN (graphProjectionN 2 x) 0) = |x (Fin.last 2)| := by
  have he : x - graphAppendN (graphProjectionN 2 x) 0 =
      x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) 1 := by
    nth_rw 1 [← graphAppendN_projection x]
    simp only [graphAppendN, zero_smul, add_zero, add_sub_cancel_left]
  rw [dist_eq_norm, he, norm_smul]
  simp only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]

lemma boundary_ball_subset_upper {x : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hr : r ≤ x (Fin.last 2)) : ball x r ⊆ {y | 0 < y (Fin.last 2)} := by
  intro y hy
  have hh := (PiLp.norm_apply_le (y - x) (Fin.last 2)).trans_lt (show ‖y - x‖ < r from hy)
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at hh
  have hh' := (abs_lt.mp hh).1
  change 0 < y (Fin.last 2)
  linarith

lemma boundary_interior_ball_subset_unit {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ < 5 / 8) {r : ℝ} (hr : r ≤ 1 / 8) (hheight : r ≤ x (Fin.last 2)) :
    ball x r ⊆ boundaryHalfBall 1 := by
  intro y hy
  refine ⟨?_, boundary_ball_subset_upper hheight hy⟩
  have hh := dist_triangle y x 0
  change dist y 0 < 1
  rw [dist_zero_right x] at hh
  have hd : dist y x < r := hy
  linarith

lemma boundary_interior_ball_subset_tangential {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 < x (Fin.last 2)) {r : ℝ} (hr : r ≤ x (Fin.last 2)) :
    ball x r ⊆ ball (graphAppendN (graphProjectionN 2 x) 0) (2 * x (Fin.last 2)) ∩
      {y | 0 < y (Fin.last 2)} := by
  intro y hy
  refine ⟨?_, boundary_ball_subset_upper hr hy⟩
  have hh := dist_triangle y x (graphAppendN (graphProjectionN 2 x) 0)
  rw [boundary_dist_flat_projection, abs_of_pos hx] at hh
  change dist y (graphAppendN (graphProjectionN 2 x) 0) < 2 * x (Fin.last 2)
  have hd : dist y x < r := hy
  linarith

lemma boundary_variance_le_excess_of_subset {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {U V : Set X} (hUV : U ⊆ V) (hfin : μ V < ∞) {F : X → E}
    (hF : MemLp F 2 (μ.restrict V)) (n : E) (hn : ‖n‖ = 1) :
    (∫ x in U, ‖F x - ⨍ y in U, F y ∂μ‖ ^ 2 ∂μ) ≤
      boundaryNormalExcess n F (μ.restrict V) := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by
    simpa using (measure_mono hUV).trans_lt hfin⟩
  exact (boundary_variance_le_normal_excess
    (hF.mono_measure (Measure.restrict_mono hUV le_rfl)) n).trans
      (boundary_normal_excess_mono hUV hfin hF n hn)

lemma boundary_tangential_ball_subset_unit {z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖graphAppendN z 0‖ < 3 / 4) {r : ℝ} (hr : r ≤ 1 / 8) :
    ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)} ⊆ boundaryHalfBall 1 := by
  intro x hx
  have hx' : x - graphAppendN z 0 ∈ boundaryHalfBall r :=
    (boundary_halfBall_translate_mem z _ r).mp (by simpa only [sub_add_cancel] using hx)
  simpa only [sub_add_cancel] using boundary_small_translate_halfBall_subset hz hr hx'

end LiquidDrop
