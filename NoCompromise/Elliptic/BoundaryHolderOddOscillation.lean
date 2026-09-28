import NoCompromise.Elliptic.BoundaryHolderOddExcess
import NoCompromise.Elliptic.BoundaryHolderNearInterior

/-! Uniform full-ball Campanato estimates for the reflected weak gradient.
Balls meeting the flat face use normal excess; balls on one side use genuine
interior comparison. Both estimates have the full coefficient exponent. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_variance_mono {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {U V : Set X} (hUV : U ⊆ V) (hfin : μ V < ∞) {F : X → E}
    (hF : MemLp F 2 (μ.restrict V)) :
    (∫ x in U, ‖F x - ⨍ y in U, F y ∂μ‖ ^ 2 ∂μ) ≤
      ∫ x in V, ‖F x - ⨍ y in V, F y ∂μ‖ ^ 2 ∂μ := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by
    simpa using (measure_mono hUV).trans_lt hfin⟩
  let : IsFiniteMeasure (μ.restrict V) := ⟨by simpa using hfin⟩
  apply (frozen_integral_norm_sub_average_le
    (hF.mono_measure (Measure.restrict_mono hUV le_rfl)) (⨍ y in V, F y ∂μ)).trans
  exact setIntegral_mono_set ((hF.sub (memLp_const _)).norm.integrable_sq)
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hUV)

/-- The actual reflected gradient has a uniform sharp oscillation bound on all
small balls around every point of a full neighborhood of the flat origin. -/
theorem boundary_holder_odd_oscillation {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ J : ℝ, 0 ≤ J ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 256 : ℝ),
          ∀ r ∈ Ioc 0 (1 / 512 : ℝ),
            (∫ y in ball x r,
              ‖boundaryOddField F y - ⨍ z in ball x r, boundaryOddField F z‖ ^ 2) ≤
                J * r ^ (3 + 2 * a) := by
  obtain ⟨K, P, hK, hP, hb⟩ := boundary_holder_tangential_growth
    ha ha1 hlam hcap hHA hHG hM
  obtain ⟨L, _, hL, _, hi⟩ := boundary_near_interior_growth
    ha ha1 hlam hcap hHA hHG hK hP (M := M)
  let J := max L (4 * K * (5 : ℝ) ^ (3 + 2 * a))
  have hJ : 0 ≤ J := hL.trans (le_max_left _ _)
  refine ⟨J, hJ, ?_⟩
  intro u F G A h x hx r hr
  have hxnorm : ‖x‖ < 1 / 256 := by simpa only [mem_ball, dist_zero_right] using hx
  have hF := boundaryOddField_memLp h.h1.memLp_gradient
  have hboundary := hb u F G A h
  have hinterior := hi u F G A h hboundary
  have hpos (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ < 1 / 256)
      (hd : 0 < y (Fin.last 2)) (hrr : r ≤ y (Fin.last 2) / 4) :
      (∫ z in ball y r,
        ‖boundaryOddField F z - ⨍ w in ball y r, boundaryOddField F w‖ ^ 2) ≤
          L * r ^ (3 + 2 * a) := by
    have hheight : |y (Fin.last 2)| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y (Fin.last 2)
    have hdsmall : y (Fin.last 2) < 1 / 64 :=
      (le_abs_self _).trans_lt (hheight.trans_lt (hy.trans (by norm_num)))
    have hsub : ball y r ⊆ boundaryHalfBall 1 := boundary_interior_ball_subset_unit
      (hy.trans (by norm_num)) (hr.2.trans (by norm_num)) (by linarith)
    rw [boundaryOddField_variance_upper hsub]
    exact (hinterior y (hy.trans (by norm_num)) hd hdsmall r ⟨hr.1, hrr⟩).1
  by_cases hclose : |x (Fin.last 2)| ≤ 4 * r
  · let q := graphAppendN (graphProjectionN 2 x) 0
    have hq : ‖q‖ < 3 / 4 := (boundary_flat_projection_norm_le x).trans_lt
      (hxnorm.trans (by norm_num))
    have hqsmall : ‖q‖ < 1 / 256 := (boundary_flat_projection_norm_le x).trans_lt hxnorm
    have h5 : 5 * r ∈ Ioc 0 (1 / 8 : ℝ) := ⟨by nlinarith [hr.1], by linarith [hr.2]⟩
    have hsub : ball x r ⊆ ball q (5 * r) := by
      intro y hy
      have hh := dist_triangle y x q
      have hdx : dist x q = |x (Fin.last 2)| := boundary_dist_flat_projection x
      rw [hdx] at hh
      change dist y q < 5 * r
      have hd : dist y x < r := hy
      linarith
    have hunit : ball q (5 * r) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro y hy
      have hh := dist_triangle y q 0
      rw [dist_zero_right q] at hh
      change dist y 0 < 1
      have hd : dist y q < 5 * r := hy
      linarith [hr.2]
    calc
      _ ≤ ∫ y in ball q (5 * r),
          ‖boundaryOddField F y - ⨍ z in ball q (5 * r), boundaryOddField F z‖ ^ 2 :=
        boundary_variance_mono hsub (isBounded_ball (x := q) (r := 5 * r)).measure_lt_top
          (hF.restrict _)
      _ ≤ 4 * boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
          (volume.restrict (ball q (5 * r) ∩ {y | 0 < y (Fin.last 2)})) :=
        boundaryOddField_variance_flat_ball h.h1.memLp_gradient (graphProjectionN 2 x) _ hunit
      _ ≤ 4 * (K * (5 * r) ^ (3 + 2 * a)) :=
        mul_le_mul_of_nonneg_left (hboundary (graphProjectionN 2 x) hq (5 * r) h5).1 (by norm_num)
      _ = (4 * K * (5 : ℝ) ^ (3 + 2 * a)) * r ^ (3 + 2 * a) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hr.1.le]
        ring
      _ ≤ J * r ^ (3 + 2 * a) := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hr.1.le _)
  · have hfar : 4 * r < |x (Fin.last 2)| := lt_of_not_ge hclose
    have hxne : x (Fin.last 2) ≠ 0 := by
      intro he
      rw [he, abs_zero] at hfar
      linarith [hr.1]
    have hbound : (∫ y in ball x r,
        ‖boundaryOddField F y - ⨍ z in ball x r, boundaryOddField F z‖ ^ 2) ≤
          L * r ^ (3 + 2 * a) := by
      rcases lt_or_gt_of_ne hxne with hn | hp
      · let R := coordinateReflection (Fin.last 2)
        have hRn : ‖R x‖ < 1 / 256 := by simpa only [R.norm_map] using hxnorm
        have hRd : 0 < R x (Fin.last 2) := by
          change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2)
          rw [boundary_reflection_last]
          linarith
        have hRr : r ≤ R x (Fin.last 2) / 4 := by
          change r ≤ coordinateReflection (Fin.last 2) x (Fin.last 2) / 4
          rw [boundary_reflection_last]
          rw [abs_of_neg hn] at hfar
          linarith
        have hh := hpos (R x) hRn hRd hRr
        rw [boundaryOddField_variance_reflect] at hh
        exact hh
      · exact hpos x hxnorm hp (by rw [abs_of_pos hp] at hfar; linarith)
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hr.1.le _))

end LiquidDrop
