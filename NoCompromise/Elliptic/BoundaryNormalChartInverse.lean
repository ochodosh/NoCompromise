import NoCompromise.Elliptic.BoundaryNormalChart

/-!
# Invertibility of normal graph coordinates

The tangent plane is orthogonal to the upward normal. In particular the face
derivative is injective, and normal coordinates give a local smooth inverse.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

/-- Every graph tangent vector is orthogonal to the unnormalized normal. -/
lemma boundaryNormal_tangent_orthogonal (p v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (graphTangentN p v) (graphAppendN (-p) 1) = 0 := by
  have hp : graphProjectionN 2 (graphTangentN p v) = v := by ext i; simp
  rw [inner_graphAppendN, hp, graphTangentN_last, inner_neg_right, mul_one,
    real_inner_comm v p]
  exact neg_add_cancel _

/-- The exact squared norm of the face derivative. -/
lemma norm_boundaryNormalLinear_sq (p : EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 3)) :
    ‖boundaryNormalLinear p v‖ ^ 2 = ‖v‖ ^ 2 +
      (inner ℝ p (graphProjectionN 2 v)) ^ 2 + (v (Fin.last 2)) ^ 2 * ‖p‖ ^ 2 := by
  rw [boundaryNormalLinear_apply, norm_sq_graphProjectionN,
    graphProjectionN_append, graphAppendN_last, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    real_inner_comm (graphProjectionN 2 v) p, norm_sq_graphProjectionN v]
  ring

lemma norm_le_boundaryNormalLinear (p : EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖ ≤ ‖boundaryNormalLinear p v‖ := by
  have h := norm_boundaryNormalLinear_sq p v
  nlinarith [sq_nonneg (inner ℝ p (graphProjectionN 2 v)),
    mul_nonneg (sq_nonneg (v (Fin.last 2))) (sq_nonneg ‖p‖), norm_nonneg v,
    norm_nonneg (boundaryNormalLinear p v)]

lemma boundaryNormalLinear_injective (p : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (boundaryNormalLinear p) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := norm_le_boundaryNormalLinear p (v - w)
  rw [map_sub, hvw, sub_self, norm_zero] at h
  exact le_antisymm h (norm_nonneg _)

/-- The face derivative, packaged as a continuous linear equivalence. -/
def boundaryNormalLinearEquiv (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (LinearEquiv.ofInjectiveEndo (boundaryNormalLinear p).toLinearMap
    (boundaryNormalLinear_injective p)).toContinuousLinearEquiv

@[simp] lemma boundaryNormalLinearEquiv_coe (p : EuclideanSpace ℝ (Fin 2)) :
    (boundaryNormalLinearEquiv p : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) = boundaryNormalLinear p := rfl

/-- Every face point has an invertible derivative, with no slope bound. -/
theorem fderiv_boundaryNormalChart_face_equiv
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (boundaryNormalChart ψ) (graphAppendN x 0) =
      (boundaryNormalLinearEquiv (gradient ψ x) : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) :=
  fderiv_boundaryNormalChart_face hψ x

/-- Smooth normal coordinates are a local diffeomorphism at each face point. -/
theorem boundaryNormalChart_local_diffeomorphism
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) = boundaryNormalChart ψ ∧
      graphAppendN x 0 ∈ e.source ∧
      ContDiffAt ℝ (⊤ : ℕ∞) e.symm (graphMapN ψ x) := by
  have hc := (smooth_boundaryNormalChart hψ).contDiffAt (x := graphAppendN x 0)
  have hd : HasFDerivAt (boundaryNormalChart ψ)
      (boundaryNormalLinearEquiv (gradient ψ x) : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) (graphAppendN x 0) :=
    hasFDerivAt_boundaryNormalChart_face (hψ.of_le (by simp)) x
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.toOpenPartialHomeomorph _ hd hn, rfl,
    hc.mem_toOpenPartialHomeomorph_source hd hn, ?_⟩
  simpa only [ContDiffAt.localInverse, HasStrictFDerivAt.localInverse_def,
    ContDiffAt.toOpenPartialHomeomorph, boundaryNormalChart_face] using hc.to_localInverse hd hn

end LiquidDrop
