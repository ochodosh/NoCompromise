module

public import NoCompromise.Elliptic.NeumannChartC3Localize
public import NoCompromise.Elliptic.NeumannChartC1Geometry

@[expose] public section

/-!
# Face geometry for C² chart heights
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

theorem neumannLocalizeCoefficient_eq_c2
    (c : C1BoundaryChart) (hψ : ContDiff ℝ 2 c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).IsInvertible) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y =
      ρ • boundaryNormalCoefficient c.height (graphAppendN a 0 + ρ • y) := by
  simp only [neumannLocalizeCoefficient, fderiv_neumannLocalizeMap_c2 c hψ,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  exact neumannLocalize_scaled_isometry_coefficient c.placement.linearIsometryEquiv _ hy hρ

theorem neumannLocalizeCoefficient_eq_of_regular_c2
    (c : C1BoundaryChart) (hψ : ContDiff ℝ 2 c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y =
      ρ • boundaryNormalCoefficient c.height (graphAppendN a 0 + ρ • y) := by
  apply neumannLocalizeCoefficient_eq_c2 c hψ a hρ
  let L := fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)
  have hinj : Function.Injective L := by
    intro v w hvw
    have heq : (fderiv ℝ (neumannLocalizeMap c a ρ) y) (ρ⁻¹ • v) =
        (fderiv ℝ (neumannLocalizeMap c a ρ) y) (ρ⁻¹ • w) := by
      simp only [fderiv_neumannLocalizeMap_c2 c hψ, ContinuousLinearMap.comp_apply,
        smul_apply, ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      exact congrArg c.placement.linearIsometryEquiv hvw
    exact (smul_right_injective _ (inv_ne_zero hρ.ne')) (hy.injective heq)
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv, rfl⟩

theorem neumannLocalizeCoefficient_cross_face_c2
    (c : C1BoundaryChart) (hψ : ContDiff ℝ 2 c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    {y : AmbientSpace} (hy : y (Fin.last 2) = 0) {i : Fin 3} (hi : i ≠ Fin.last 2) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y
        (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
      neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y
        (EuclideanSpace.single (Fin.last 2) 1) i = 0 := by
  have hface : (graphAppendN a 0 + ρ • y) (Fin.last 2) = 0 := by
    simp only [PiLp.add_apply, graphAppendN_last, PiLp.smul_apply, hy, smul_zero, add_zero]
  have hreg : (fderiv ℝ (boundaryNormalChart c.height)
      (graphAppendN a 0 + ρ • y)).IsInvertible := by
    have heq : graphAppendN a 0 + ρ • y =
        graphAppendN (graphProjectionN 2 (graphAppendN a 0 + ρ • y)) 0 := by
      simpa only [hface] using (graphAppendN_projection (graphAppendN a 0 + ρ • y)).symm
    rw [heq, fderiv_boundaryNormalChart_face_equiv (hψ.of_le (by simp))]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [neumannLocalizeCoefficient_eq_c2 c hψ a hρ hreg]
  obtain ⟨h₁, h₂⟩ := boundaryNormalCoefficient_cross_face (hψ.of_le (by simp)) hface hi
  simpa only [smul_apply, PiLp.smul_apply, h₁, h₂, smul_zero] using
    (show (0 : ℝ) = 0 ∧ (0 : ℝ) = 0 from ⟨rfl, rfl⟩)

theorem neumannChartC1_abs_det_face_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a t : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) :
    |(fderiv ℝ (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)).det| =
      ρ ^ 3 * (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) := by
  rw [fderiv_neumannLocalizeMap_c2 c hψ, neumannChartC1_scaled_face,
    fderiv_boundaryNormalChart_face (hψ.of_le (by simp))]
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_smul, LinearMap.det_comp,
    finrank_euclideanSpace, Fintype.card_fin, abs_mul, abs_pow, abs_of_pos hρ]
  change ρ ^ 3 *
    (|(c.placement.linearIsometryEquiv : AmbientSpace →L[ℝ] AmbientSpace).det| *
      |(boundaryNormalLinear (gradient c.height (a + ρ • t))).det|) = _
  rw [neumannLocalize_abs_det_isometry, one_mul, neumannChartC1_det_normalLinear,
    abs_neg, abs_of_pos (by positivity)]

theorem neumannChartC1_coefficient_face_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a t : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) (v : AmbientSpace) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t) v
      (Fin.last 2) = ρ * v (Fin.last 2) := by
  have hreg : (fderiv ℝ (boundaryNormalChart c.height)
      (graphAppendN a 0 + ρ • graphBaseEmbedding t)).IsInvertible := by
    rw [neumannChartC1_scaled_face,
      fderiv_boundaryNormalChart_face_equiv (hψ.of_le (by simp))]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [neumannLocalizeCoefficient_eq_c2 c hψ a hρ hreg, neumannChartC1_scaled_face]
  have he : boundaryNormalCoefficient c.height (graphAppendN (a + ρ • t) 0)
      (EuclideanSpace.single (Fin.last 2) 1) = EuclideanSpace.single (Fin.last 2) 1 := by
    rw [boundaryNormalCoefficient, fderiv_boundaryNormalChart_face (hψ.of_le (by simp))]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      boundaryNormalLinear_inverse_gram_last, neumannChartC1_det_normalLinear,
      abs_neg, abs_of_pos (show 0 < (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2 : ℝ)
        by positivity), smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt (by positivity)), one_smul]
  have hs := boundaryNormalCoefficient_symmetric c.height (graphAppendN (a + ρ • t) 0)
    v (EuclideanSpace.single (Fin.last 2) 1)
  rw [he] at hs
  have hl : boundaryNormalCoefficient c.height (graphAppendN (a + ρ • t) 0) v
      (Fin.last 2) = v (Fin.last 2) := by
    simpa [EuclideanSpace.inner_single_right] using hs
  simpa only [smul_apply, PiLp.smul_apply, smul_eq_mul] using
    congrArg (fun r : ℝ => ρ * r) hl

theorem neumannChartC1_normal_derivative_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a t : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    fderiv ℝ (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
        (EuclideanSpace.single (Fin.last 2) 1) =
      -(ρ * Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) •
        c.outwardNormal (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) := by
  have hp : graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) 1) = 0 := by
    ext i
    simp only [graphProjectionN_apply, PiLp.single_apply, Fin.castSucc_ne_last,
      ite_false, PiLp.zero_apply]
  have he (p : EuclideanSpace ℝ (Fin 2)) :
      boundaryNormalLinear p (EuclideanSpace.single (Fin.last 2) 1) =
        -graphAppendN (-p) 1 := by
    simp only [boundaryNormalLinear, sub_apply, ContinuousLinearMap.comp_apply,
      hp, map_zero, ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj,
      PiLp.single_apply, ite_true, one_smul, zero_sub]
  have hn : c.outwardNormal (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) =
      c.placement.linearIsometryEquiv (smoothGraphUnitNormal (gradient c.height (a + ρ • t))) := by
    rw [neumannChartC1_map_face, C1BoundaryChart.outwardNormal,
      c.placement.symm_apply_apply, smoothSubgraphNormal]
    rw [show graphProjectionN 2 (graphMapN c.height (a + ρ • t)) = a + ρ • t from
      graphProjectionN_append _ _]
  rw [fderiv_neumannLocalizeMap_c2 c hψ, neumannChartC1_scaled_face,
    fderiv_boundaryNormalChart_face (hψ.of_le (by simp)), hn]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, he, map_neg, smoothGraphUnitNormal, smul_smul]
  have hs : Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [neg_mul, mul_assoc, mul_inv_cancel₀ hs, mul_one, neg_smul, smul_neg]
  rfl

/-- The face normal coefficient is constant on the whole base plane. -/
theorem neumannChartC3_normal_coefficient (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) :
    boundaryNeumannNormalCoefficient
      (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ)) = fun _ => ρ := by
  funext t
  simp only [boundaryNeumannNormalCoefficient, EuclideanSpace.inner_single_right,
    neumannChartC1_coefficient_face_c2 c hψ a t hρ, PiLp.single_apply, ite_true, mul_one,
    RCLike.conj_to_real, one_mul]

end LiquidDrop
