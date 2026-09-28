import NoCompromise.Sard.Flat
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Null vector images of the rank-zero C² stratum

A quadratic bound on a subset of `ℝⁿ` makes its image in `ℝᵐ` null when
`n < 2m`. This is the elementary Hausdorff covering estimate for exponent two.
Locally Lipschitz first derivatives supply that bound on the rank-zero stratum
of a C² map. No Sard or nonlinear area theorem is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric Function
open scoped ENNReal NNReal Topology
namespace LiquidDrop

/-- A quadratic pairwise bound gives a null image when twice the target dimension
exceeds the source dimension. -/
lemma measure_image_eq_zero_of_quadratic_bound {n m : ℕ} (hdim : n < 2 * m)
    {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (C : ℝ≥0)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ C * dist x y ^ 2) :
    volume (f '' S) = 0 := by
  have hh : HolderOnWith C 2 f S := by
    intro x hx y hy
    have hb := ENNReal.ofReal_le_ofReal (h x hx y hy)
    simpa only [edist_dist, NNReal.coe_ofNat, ENNReal.rpow_two,
      ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_pow dist_nonneg,
      ENNReal.ofReal_coe_nnreal] using hb
  have hz : (Measure.hausdorffMeasure (2 * (m : ℝ)) :
      Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
    apply Real.hausdorffMeasure_of_finrank_lt
    simpa only [finrank_euclideanSpace_fin] using (show (n : ℝ) < 2 * m by exact_mod_cast hdim)
  have hnull : Measure.hausdorffMeasure (m : ℝ) (f '' S) = 0 := by
    have hb := hh.hausdorffMeasure_image_le (by norm_num) (d := (m : ℝ)) (by positivity)
    simpa only [NNReal.coe_ofNat, hz, Measure.coe_zero, Pi.zero_apply, mul_zero,
      nonpos_iff_eq_zero] using hb
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hnull, smul_zero]

/-- A countable open cover assembles null vector images without requiring
measurability of the covered source set. -/
lemma measure_vector_image_eq_zero_of_local_null {n m : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hloc : ∀ x ∈ S, ∃ V, IsOpen V ∧ x ∈ V ∧ volume (f '' (S ∩ V)) = 0) :
    volume (f '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose V hVo hVx hnull using fun x : S => hloc x x.property
    have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
    obtain ⟨c, hc⟩ := hL.indexed_countable_subcover V hVo
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
    apply measure_mono_null (t := ⋃ j, f '' (S ∩ V (c j))) _
      (measure_iUnion_null fun j => hnull (c j))
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨j, x, ⟨hx, hj⟩, rfl⟩
  · simp only [not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

/-- The rank-zero stratum of a C² map `ℝⁿ → ℝᵐ` has null image if `n < 2m`. -/
theorem measure_image_fderiv_zero_of_contDiffOn {n m : ℕ} (hdim : n < 2 * m)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : ContDiffOn ℝ 2 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  apply measure_vector_image_eq_zero_of_local_null
  intro x hx
  let C : ℝ≥0 := ‖fderiv ℝ (fderiv ℝ f) x‖₊ + 1
  have hdc := hdf.contDiffAt (hU.mem_nhds hx.1)
  obtain ⟨V, hV, hLip⟩ := hdc.exists_lipschitzOnWith_of_nnnorm_lt C
    (by dsimp [C]; simp)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hx.1))
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr, ?_⟩
  apply measure_image_eq_zero_of_quadratic_bound hdim C
  intro y hy z hz
  have hseg : segment ℝ z y ⊆ ball x r := (convex_ball x r).segment_subset hz.2 hy.2
  have hder (w) (hw : w ∈ segment ℝ z y) : ‖fderiv ℝ f w‖ ≤ C * dist y z := by
    have hb := hLip.dist_le_mul w (hrV (hseg hw)).1 z (hrV hz.2).1
    rw [hz.1.2, dist_zero_right] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
    simpa only [mem_closedBall, dist_comm z y] using
      segment_subset_closedBall_left z y hw
  have hb := (convex_segment z y).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hf.differentiableOn (by norm_num) w (hrV (hseg hw)).2).differentiableAt
      (hU.mem_nhds (hrV (hseg hw)).2)) hder
    (left_mem_segment ℝ z y) (right_mem_segment ℝ z y)
  simpa only [dist_eq_norm, pow_two, mul_assoc] using hb

end LiquidDrop
