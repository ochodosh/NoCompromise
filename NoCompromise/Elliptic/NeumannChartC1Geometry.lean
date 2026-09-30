module

public import NoCompromise.Elliptic.NeumannChartC1Smooth
public import NoCompromise.Elliptic.ClassicalNormal
public import NoCompromise.Elliptic.BoundaryNeumannInhomLift

@[expose] public section

/-!
# Face geometry of the placed normal chart
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- The unnormalized inward normal column gives a negative determinant. -/
theorem neumannChartC1_det_normalLinear (p : EuclideanSpace ℝ (Fin 2)) :
    (boundaryNormalLinear p).det = -(1 + ‖p‖ ^ 2) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : (boundaryNormalLinear p).det = Matrix.det
      (Matrix.of (fun i j : Fin 3 => boundaryNormalLinear p (EuclideanSpace.single j 1) i)) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
  rw [he, Matrix.det_fin_three, PiLp.norm_sq_eq_of_L2]
  simp [Matrix.of_apply, boundaryNormalLinear, graphTangentN, graphProjectionN,
    graphAppendN, graphBaseN, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, pow_two]
  ring

lemma neumannChartC1_scaled_face (a t : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    graphAppendN a 0 + ρ • graphBaseEmbedding t = graphAppendN (a + ρ • t) 0 := by
  rw [boundary_neumann_graphBase_eq_append]
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, graphAppendN_last,
      graphAppendN_castSucc, smul_zero, add_zero]

lemma neumannChartC1_map_face (c : C1BoundaryChart)
    (a t : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    neumannLocalizeMap c a ρ (graphBaseEmbedding t) =
      c.placement (graphMapN c.height (a + ρ • t)) := by
  rw [neumannLocalizeMap, neumannChartC1_scaled_face, boundaryNormalChart_face]

/-- The volume Jacobian on the face has three factors of the positive scale. -/
theorem neumannChartC1_abs_det_face (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a t : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) :
    |(fderiv ℝ (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)).det| =
      ρ ^ 3 * (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) := by
  rw [fderiv_neumannLocalizeMap c hψ, neumannChartC1_scaled_face,
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

/-- With the unnormalized normal coordinate, the normal coefficient on the
face is exactly the scale. This gives the conormal for an arbitrary vector. -/
theorem neumannChartC1_coefficient_face (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a t : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) (v : AmbientSpace) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t) v
      (Fin.last 2) = ρ * v (Fin.last 2) := by
  have hreg : (fderiv ℝ (boundaryNormalChart c.height)
      (graphAppendN a 0 + ρ • graphBaseEmbedding t)).IsInvertible := by
    rw [neumannChartC1_scaled_face,
      fderiv_boundaryNormalChart_face_equiv (hψ.of_le (by simp))]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [neumannLocalizeCoefficient_eq c hψ a hρ hreg, neumannChartC1_scaled_face]
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

/-- Positive chart normal is the negative outward unit normal, multiplied by
the scale and the graph area density. -/
theorem neumannChartC1_normal_derivative (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a t : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
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
  rw [fderiv_neumannLocalizeMap c hψ, neumannChartC1_scaled_face,
    fderiv_boundaryNormalChart_face (hψ.of_le (by simp)), hn]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, he, map_neg, smoothGraphUnitNormal, smul_smul]
  have hs : Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [neg_mul, mul_assoc, mul_inv_cancel₀ hs, mul_one, neg_smul, smul_neg]
  rfl

end LiquidDrop
