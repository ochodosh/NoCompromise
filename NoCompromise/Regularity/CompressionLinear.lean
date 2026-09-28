import NoCompromise.Area.Cofactor
import NoCompromise.BV.CoareaCoordinates

/-! # The exact derivative and cofactor of a vertical compression -/

noncomputable section
open Set InnerProductSpace Matrix
open scoped Gradient
namespace LiquidDrop

def compressionLinear (β t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (Matrix.toEuclideanLin !![1, 0, 0; 0, 1, 0; t * p 0, t * p 1, β]).toContinuousLinearMap

lemma compressionLinear_apply (β t : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 3)) :
    compressionLinear β t p v = graphAppendN (graphProjectionN 2 v)
      (β * v 2 + t * inner ℝ p (graphProjectionN 2 v)) := by
  ext i
  fin_cases i <;>
    simp [compressionLinear, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two, graphAppendN, graphBaseN,
      graphProjectionN, PiLp.inner_apply]
  ring

lemma standardMatrix3_compressionLinear (β t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    standardMatrix3 (compressionLinear β t p) =
      !![1, 0, 0; 0, 1, 0; t * p 0, t * p 1, β] := by
  exact Matrix.toEuclideanLin.symm_apply_apply _

lemma cofactor3_compressionLinear (β t : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (ν : EuclideanSpace ℝ (Fin 3)) :
    cofactor3 (compressionLinear β t p) ν =
      graphAppendN (β • graphProjectionN 2 ν - (t * ν 2) • p) (ν 2) := by
  rw [cofactor3, standardMatrix3_compressionLinear]
  ext i
  fin_cases i <;>
    simp [Matrix.adjugate_fin_three, Matrix.transpose_apply, Matrix.toEuclideanLin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      graphAppendN, graphBaseN, graphProjectionN] <;> ring

lemma norm_graphAppendN_sq {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    ‖graphAppendN p s‖ ^ 2 = ‖p‖ ^ 2 + s ^ 2 := by
  rw [norm_sq_graphProjectionN]
  simp only [graphProjectionN_append, graphAppendN_last]

/-- The squared area Jacobian on every normal plane is exactly the squared
norm of the compression cofactor; the planar coordinates need no orientation. -/
theorem compression_jacobian_sq (β t : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    {ν : EuclideanSpace ℝ (Fin 3)} (hν : ‖ν‖ = 1)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    jacobian2Linear ((compressionLinear β t p).comp
      (normalPlaneInclusion ν e).toContinuousLinearMap) ^ 2 =
      ‖β • graphProjectionN 2 ν - (t * ν 2) • p‖ ^ 2 + (ν 2) ^ 2 := by
  rw [jacobian2Linear_normalPlane _ hν e, cofactor3_compressionLinear, norm_graphAppendN_sq]

end LiquidDrop
