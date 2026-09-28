import NoCompromise.Area.Linear
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Cofactors and the Jacobian on a normal plane

The cofactor convention is the transpose of the adjugate of the matrix in standard
orthonormal coordinates. The cross-product transformation formula and the Gram
Jacobian formula imply the normal-plane identity for every isometric parametrization
of that plane. Such parametrizations exist for every unit normal, and their orientation
does not affect the result. No area formula or image-measure result is used.
-/

noncomputable section

open Module Matrix
open scoped RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The ordinary oriented cross product in standard Euclidean coordinates. -/
abbrev cross3 (u v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

/-- The squared norm of a cross product is the two-vector Gram determinant. -/
lemma norm_cross3_sq (u v : EuclideanSpace ℝ (Fin 3)) :
    ‖cross3 u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 := by
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, RCLike.re_to_real, cross_dot_cross,
    dotProduct_comm (WithLp.ofLp v) (WithLp.ofLp u), sq]

/-- The Gram determinant of a linear map with planar source. -/
lemma gram_det_eq_norms {m : ℕ}
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (A.adjoint.comp A).det =
      ‖A (EuclideanSpace.single 0 (1 : ℝ))‖ ^ 2 *
        ‖A (EuclideanSpace.single 1 (1 : ℝ))‖ ^ 2 -
      inner ℝ (A (EuclideanSpace.single 0 (1 : ℝ)))
        (A (EuclideanSpace.single 1 (1 : ℝ))) ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hentry (i j : Fin 2) :
      LinearMap.toMatrix b.toBasis b.toBasis (A.adjoint.comp A).toLinearMap i j =
      inner ℝ (A (EuclideanSpace.single i (1 : ℝ)))
        (A (EuclideanSpace.single j (1 : ℝ))) := by
    rw [LinearMap.toMatrix_apply]
    change (A.adjoint (A (b j))) i = _
    calc
      _ = inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (A.adjoint (A (EuclideanSpace.single j (1 : ℝ)))) := by
        simp [EuclideanSpace.inner_single_left, b, EuclideanSpace.basisFun_apply]
      _ = _ := ContinuousLinearMap.adjoint_inner_right A _ _
  change LinearMap.det (A.adjoint.comp A).toLinearMap = _
  rw [← LinearMap.det_toMatrix b.toBasis, Matrix.det_fin_two]
  simp only [hentry, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (A (EuclideanSpace.single 1 (1 : ℝ)))
    (A (EuclideanSpace.single 0 (1 : ℝ)))]
  ring

/-- The planar Jacobian in three-dimensional Euclidean space is a cross-product norm. -/
lemma jacobian2Linear_eq_norm_cross3
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    jacobian2Linear A = ‖cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
      (A (EuclideanSpace.single 1 (1 : ℝ)))‖ := by
  rw [jacobian2Linear, gram_det_eq_norms, ← norm_cross3_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The matrix of a three-dimensional linear map in the standard orthonormal basis. -/
def standardMatrix3
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.toEuclideanLin.symm L.toLinearMap

/-- The cofactor map: transpose of the adjugate in standard orthonormal coordinates. -/
def cofactor3
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (Matrix.toEuclideanLin (standardMatrix3 L).adjugate.transpose).toContinuousLinearMap

/-- The cofactor convention is exact, including for singular linear maps. -/
lemma standardMatrix3_cofactor3
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 (cofactor3 L) = (standardMatrix3 L).adjugate.transpose := by
  exact Matrix.toEuclideanLin.symm_apply_apply _

/-- The polynomial cofactor identity for arbitrary three-by-three real matrices. -/
lemma crossProduct_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    crossProduct (M *ᵥ u) (M *ᵥ v) = M.adjugate.transpose *ᵥ crossProduct u v := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- Cross products transform by the cofactor map, without invertibility assumptions. -/
lemma cross3_map
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (u v : EuclideanSpace ℝ (Fin 3)) :
    cross3 (L u) (L v) = cofactor3 L (cross3 u v) := by
  have hL (w : EuclideanSpace ℝ (Fin 3)) :
      L w = WithLp.toLp 2 (standardMatrix3 L *ᵥ WithLp.ofLp w) := by
    change L.toLinearMap w = Matrix.toEuclideanLin (standardMatrix3 L) w
    rw [standardMatrix3, LinearEquiv.apply_symm_apply]
  rw [hL u, hL v]
  change WithLp.toLp 2 (crossProduct (standardMatrix3 L *ᵥ WithLp.ofLp u)
    (standardMatrix3 L *ᵥ WithLp.ofLp v)) =
    WithLp.toLp 2 ((standardMatrix3 L).adjugate.transpose *ᵥ
      crossProduct (WithLp.ofLp u) (WithLp.ofLp v))
  rw [crossProduct_mulVec]

/-- The Jacobian of a composite is the cofactor norm of the original area vector. -/
lemma jacobian2Linear_comp_eq_cofactor_cross3
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    jacobian2Linear (L.comp A) =
      ‖cofactor3 L (cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
        (A (EuclideanSpace.single 1 (1 : ℝ))))‖ := by
  rw [jacobian2Linear_eq_norm_cross3]
  exact congrArg norm (cross3_map L _ _)

lemma inner_left_cross3 (u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ u (cross3 u v) = 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    dotProduct_comm] using (dot_self_cross (WithLp.ofLp u) (WithLp.ofLp v))

lemma inner_right_cross3 (u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (cross3 u v) = 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    dotProduct_comm] using (dot_cross_self (WithLp.ofLp u) (WithLp.ofLp v))

lemma cross3_mem_orthogonal_range
    (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
      (A (EuclideanSpace.single 1 (1 : ℝ))) ∈ A.rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨x, rfl⟩
  have hx : x = x 0 • EuclideanSpace.single 0 (1 : ℝ) +
      x 1 • EuclideanSpace.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hx]
  simp [map_add, map_smul, inner_add_left, real_inner_smul_left,
    inner_left_cross3, inner_right_cross3]

lemma norm_cross3_of_isometry
    (A : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ‖cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
      (A (EuclideanSpace.single 1 (1 : ℝ)))‖ = 1 := by
  have h := norm_cross3_sq (A (EuclideanSpace.single 0 (1 : ℝ)))
    (A (EuclideanSpace.single 1 (1 : ℝ)))
  rw [A.inner_map_map] at h
  norm_num [A.norm_map, PiLp.norm_single, EuclideanSpace.inner_single_left,
    PiLp.single_apply] at h
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
    (A (EuclideanSpace.single 1 (1 : ℝ))))]

/-- The ambient isometric inclusion associated with coordinates on the normal plane. -/
def normalPlaneInclusion (ν : EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((ℝ ∙ ν)ᗮ).subtypeₗᵢ.comp e.toLinearIsometry

/-- The parametrization covers precisely the plane orthogonal to the given normal. -/
lemma normalPlaneInclusion_range (ν : EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    (normalPlaneInclusion ν e).toLinearMap.range = (ℝ ∙ ν)ᗮ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e y).property
  · intro hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- Every unit normal admits isometric planar coordinates on its orthogonal complement. -/
lemma exists_normalPlaneIsometry {ν : EuclideanSpace ℝ (Fin 3)} (hν : ‖ν‖ = 1) :
    Nonempty (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) := by
  have hνne : ν ≠ 0 := by intro h; simp [h] at hν
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact ⟨(OrthonormalBasis.fromOrthogonalSpanSingleton 2 hνne).repr.symm⟩

/-- Blueprint `lem:cofactor`: the Jacobian of the restriction to the normal plane is
the norm of the cofactor applied to the unit normal. This holds in any isometric
coordinates on the plane, regardless of orientation. -/
lemma jacobian2Linear_normalPlane
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    {ν : EuclideanSpace ℝ (Fin 3)} (hν : ‖ν‖ = 1)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    jacobian2Linear (L.comp (normalPlaneInclusion ν e).toContinuousLinearMap) =
      ‖cofactor3 L ν‖ := by
  let A := normalPlaneInclusion ν e
  have hc := cross3_mem_orthogonal_range A.toLinearMap
  rw [normalPlaneInclusion_range, Submodule.orthogonal_orthogonal] at hc
  obtain ⟨c, heq⟩ := Submodule.mem_span_singleton.mp hc
  change c • ν = cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
    (A (EuclideanSpace.single 1 (1 : ℝ))) at heq
  have hcnorm : ‖c‖ = 1 := by
    have h := congrArg norm heq
    rw [norm_smul, hν, mul_one, norm_cross3_of_isometry] at h
    exact h
  rw [jacobian2Linear_comp_eq_cofactor_cross3]
  change ‖cofactor3 L (cross3 (A (EuclideanSpace.single 0 (1 : ℝ)))
    (A (EuclideanSpace.single 1 (1 : ℝ))))‖ = _
  rw [← heq, map_smul, norm_smul, hcnorm, one_mul]

end LiquidDrop
