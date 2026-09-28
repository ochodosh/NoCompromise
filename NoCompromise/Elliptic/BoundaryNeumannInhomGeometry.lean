import NoCompromise.Elliptic.BoundaryNeumann
import NoCompromise.DeGiorgi.SmoothGraph

/-! Vertical slices of the half-ball, including their curved endpoints. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_append_mem_halfBall (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    graphAppendN y t ∈ boundaryHalfBall 1 ↔
      y ∈ ball 0 1 ∧ t ∈ Ioo 0 (Real.sqrt (1 - ‖y‖ ^ 2)) := by
  have he := norm_sq_graphProjectionN (graphAppendN y t)
  simp only [graphProjectionN_append, graphAppendN_last] at he
  simp only [boundaryHalfBall, mem_inter_iff, mem_ball, dist_zero_right,
    mem_ofPred_eq, graphAppendN_last, mem_Ioo]
  constructor
  · rintro ⟨hn, ht⟩
    have hy : ‖y‖ < 1 := by nlinarith [norm_nonneg (graphAppendN y t), norm_nonneg y, sq_nonneg t]
    have hs := Real.sq_sqrt (show 0 ≤ 1 - ‖y‖ ^ 2 by nlinarith [norm_nonneg y])
    refine ⟨hy, ht, ?_⟩
    nlinarith [Real.sqrt_nonneg (1 - ‖y‖ ^ 2), norm_nonneg (graphAppendN y t)]
  · rintro ⟨hy, ht, htop⟩
    have hs := Real.sq_sqrt (show 0 ≤ 1 - ‖y‖ ^ 2 by nlinarith [norm_nonneg y])
    refine ⟨?_, ht⟩
    nlinarith [norm_nonneg (graphAppendN y t), Real.sqrt_nonneg (1 - ‖y‖ ^ 2)]

lemma boundary_neumann_slice_height_pos {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ ball 0 1) : 0 < Real.sqrt (1 - ‖y‖ ^ 2) := by
  have hn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg y]

lemma boundary_neumann_closed_slice {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ ball 0 1) {t : ℝ} (ht : t ∈ Icc 0 (Real.sqrt (1 - ‖y‖ ^ 2))) :
    graphAppendN y t ∈ closure (boundaryHalfBall 1) := by
  have hm : MapsTo (fun s => graphAppendN y s)
      (Ioo 0 (Real.sqrt (1 - ‖y‖ ^ 2))) (boundaryHalfBall 1) := by
    intro s hs
    exact (boundary_neumann_append_mem_halfBall y s).mpr ⟨hy, hs⟩
  have hc : Continuous (fun s : ℝ => graphAppendN y s) :=
    continuous_const.add (continuous_id.smul continuous_const)
  apply hm.closure hc
  rwa [closure_Ioo (boundary_neumann_slice_height_pos hy).ne]

lemma boundary_neumann_test_zero_at_slice_top
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hsφ : tsupport φ ⊆ ball 0 1)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ ball 0 1) :
    φ (graphAppendN y (Real.sqrt (1 - ‖y‖ ^ 2))) = 0 := by
  have hn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
  have he := norm_sq_graphProjectionN (graphAppendN y (Real.sqrt (1 - ‖y‖ ^ 2)))
  simp only [graphProjectionN_append, graphAppendN_last,
    Real.sq_sqrt (show 0 ≤ 1 - ‖y‖ ^ 2 by nlinarith [norm_nonneg y])] at he
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hb := hsφ ht
  simp only [mem_ball, dist_zero_right] at hb
  nlinarith [norm_nonneg (graphAppendN y (Real.sqrt (1 - ‖y‖ ^ 2)))]

/-- Fubini with the exact vertical segments of the upper unit half-ball. -/
theorem boundary_neumann_integral_halfBall_slices
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : IntegrableOn g (boundaryHalfBall 1)) :
    (∫ x in boundaryHalfBall 1, g x) =
      ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ∫ t in Ioo 0 (Real.sqrt (1 - ‖y‖ ^ 2)), g (graphAppendN y t) := by
  let e := smoothGraphCoordinates (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
    continuous_const
  have hp := smoothGraphCoordinates_measurePreserving
    (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) continuous_const
  have hi : Integrable ((boundaryHalfBall 1).indicator g) :=
    (integrable_indicator_iff (isOpen_boundaryHalfBall 1).measurableSet).mpr hg
  have hic := hp.integrable_comp_of_integrable hi
  rw [← integral_indicator (isOpen_boundaryHalfBall 1).measurableSet,
    ← hp.integral_comp e.measurableEmbedding]
  change (∫ p, ((boundaryHalfBall 1).indicator g) (e p) ∂volume.prod volume) = _
  change Integrable (fun p => ((boundaryHalfBall 1).indicator g) (e p))
    (volume.prod volume) at hic
  rw [integral_prod _ hic]
  have he (y : EuclideanSpace ℝ (Fin 2)) :
      (∫ t : ℝ, ((boundaryHalfBall 1).indicator g) (e (y, t))) =
        (ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator
          (fun y => ∫ t in Ioo 0 (Real.sqrt (1 - ‖y‖ ^ 2)), g (graphAppendN y t)) y := by
    by_cases hy : y ∈ ball 0 1
    · rw [indicator_of_mem hy, ← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      change ((boundaryHalfBall 1).indicator g) (graphAppendN y (t + 0)) = _
      rw [add_zero]
      by_cases ht : t ∈ Ioo 0 (Real.sqrt (1 - ‖y‖ ^ 2))
      · rw [indicator_of_mem ((boundary_neumann_append_mem_halfBall y t).mpr ⟨hy, ht⟩),
          indicator_of_mem ht]
      · rw [indicator_of_notMem (fun hx => ht ((boundary_neumann_append_mem_halfBall y t).mp hx).2),
          indicator_of_notMem ht]
    · rw [indicator_of_notMem hy]
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro t
      change ((boundaryHalfBall 1).indicator g) (graphAppendN y (t + 0)) = 0
      rw [add_zero, indicator_of_notMem
        (fun hx => hy ((boundary_neumann_append_mem_halfBall y t).mp hx).1)]
  change (∫ y, ∫ t, ((boundaryHalfBall 1).indicator g) (e (y, t))) = _
  simp_rw [he]
  exact integral_indicator measurableSet_ball

end LiquidDrop
