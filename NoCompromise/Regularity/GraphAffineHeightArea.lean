import NoCompromise.Regularity.ApproxHarmonicEstimateArea
import NoCompromise.Regularity.TiltPlane
import NoCompromise.Sobolev.Extension

/-! # Genuine area bounds for affine height on a Lipschitz graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma graphAffineHeight_projection (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : graphProjectionN 2 (graphMap f x) = x := by
  ext i
  fin_cases i <;> simp [graphProjectionN_apply]

lemma graphAffineHeight_jacobian_le_two
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) (x : EuclideanSpace ℝ (Fin 2)) :
    Real.sqrt (1 + ‖gradient f x‖ ^ 2) ≤ 2 := by
  have hh := (norm_gradient_le_of_lipschitz hf x).trans hK
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num, by nlinarith [norm_nonneg (gradient f x)]⟩

/-- Orthogonal distance to an affine graph plane is bounded by vertical discrepancy. -/
lemma graphAffineHeight_sq_le (p : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (z : AmbientSpace) :
    (inner ℝ (graphUnitNormal p) z - b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2 ≤
      (z 2 - b - inner ℝ p (graphProjectionN 2 z)) ^ 2 := by
  have hs : 1 ≤ Real.sqrt (1 + ‖p‖ ^ 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖p‖])
  rw [graphUnitNormal_affine_height_eq]
  have hh : |(z 2 - b - inner ℝ p (graphProjectionN 2 z)) /
      Real.sqrt (1 + ‖p‖ ^ 2)| ≤ |z 2 - b - inner ℝ p (graphProjectionN 2 z)| := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self (abs_nonneg _) hs
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

/-- Continuous affine graph errors are integrable on every bounded base set. -/
lemma integrableOn_graphAffineHeight_base
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (p : EuclideanSpace ℝ (Fin 2)) (b : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A) :
    IntegrableOn (fun x => (f x - b - inner ℝ p x) ^ 2) A volume := by
  have hc : Continuous (fun x => (f x - b - inner ℝ p x) ^ 2) :=
    ((hf.continuous.sub continuous_const).sub (continuous_const.inner continuous_id)).pow 2
  exact (hc.continuousOn.integrableOn_compact hA.isCompact_closure).mono_set subset_closure

/-- Genuine signed area transport bounds the full affine-height integral on an
actual Lipschitz graph; no surface integral estimate is a premise. -/
theorem graphAffineHeight_integral_graph_le
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) (p : EuclideanSpace ℝ (Fin 2)) (b : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hbA : Bornology.IsBounded A) :
    IntegrableOn (fun z => (inner ℝ (graphUnitNormal p) z -
        b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2) (graphMap f '' A) (hausdorffMeasure2 3) ∧
    (∫ z in graphMap f '' A, (inner ℝ (graphUnitNormal p) z -
        b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2 ∂hausdorffMeasure2 3) ≤
      2 * ∫ x in A, (f x - b - inner ℝ p x) ^ 2 := by
  let q := fun z : AmbientSpace => (inner ℝ (graphUnitNormal p) z -
    b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2
  have hi := integrableOn_graphAffineHeight_base hf p b hbA
  have hq : Continuous q := by dsimp only [q]; fun_prop
  have hm : Measurable (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2) * q (graphMap f x)) :=
    (measurable_const.add ((measurable_gradient f).norm.pow_const 2)).sqrt.mul
      (hq.measurable.comp (lipschitzWith_graphMap hf).continuous.measurable)
  have hbound (x : EuclideanSpace ℝ (Fin 2)) :
      Real.sqrt (1 + ‖gradient f x‖ ^ 2) * q (graphMap f x) ≤
        2 * (f x - b - inner ℝ p x) ^ 2 := by
    have hh := graphAffineHeight_sq_le p b (graphMap f x)
    simp only [graphMap_apply_two, graphAffineHeight_projection] at hh
    exact (mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (graphAffineHeight_jacobian_le_two hf hK x) (sq_nonneg _))
  have hiq : IntegrableOn
      (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2) * q (graphMap f x)) A volume := by
    apply (hi.const_mul 2).mono' hm.aestronglyMeasurable.restrict
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))]
    exact hbound x
  refine ⟨(integrableOn_graphMap_image_iff hf hA q).mpr hiq, ?_⟩
  rw [integral_graphMap_image hf hA, ← integral_const_mul]
  exact integral_mono_ae hiq (hi.const_mul 2) (ae_of_all _ hbound)

end LiquidDrop
