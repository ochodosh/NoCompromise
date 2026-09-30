module

public import NoCompromise.Elliptic.SobolevChain
public import NoCompromise.Isoperimetric.ABPContact

@[expose] public section

/-!
# The two classical Laplacians and the Neumann quadratic correction

Only C² regularity at the point is needed to identify the coordinate Laplacian
with the Hessian trace used by the ABP argument. In dimension three the
quadratic correction `c * ‖x‖ ^ 2 / 6` has Laplacian `c`.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient Laplacian

namespace LiquidDrop

lemma poissonCoordinateDerivative_second_of_contDiffAt {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := hD.hasFDerivAt.clm_apply
    (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  change fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x _ = _
  rw [h.fderiv]
  simp

/-- The Hessian trace and coordinate Laplacian agree under local C² regularity. -/
theorem laplacianTrace_eq_laplacianN {u : AmbientSpace → ℝ} {x : AmbientSpace}
    (hu : ContDiffAt ℝ 2 u x) : laplacianTrace u x = laplacianN u x := by
  unfold laplacianTrace laplacianN hessianForm
  apply Finset.sum_congr rfl
  intro i _
  exact (poissonCoordinateDerivative_second_of_contDiffAt hu i i).symm

lemma laplacian_eq_laplacianN_of_contDiffAt {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ 2 u x) : Δ u x = laplacianN u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  change (∑ i, _) = ∑ i, _
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, poissonCoordinateDerivative_second_of_contDiffAt hu]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma laplacianN_add_of_contDiffAt {n : ℕ}
    {u v : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    laplacianN (fun y => u y + v y) x = laplacianN u x + laplacianN v x := by
  rw [← laplacian_eq_laplacianN_of_contDiffAt (hu.add hv)]
  change Δ (u + v) x = _
  rw [hu.laplacian_add hv, laplacian_eq_laplacianN_of_contDiffAt hu,
    laplacian_eq_laplacianN_of_contDiffAt hv]

lemma laplacianN_norm_sq (x : AmbientSpace) :
    laplacianN (fun y : AmbientSpace => ‖y‖ ^ 2) x = 6 := by
  rw [← laplacianTrace_eq_laplacianN (contDiff_norm_sq ℝ).contDiffAt]
  have hd := (((innerSL ℝ (E := AmbientSpace)).hasFDerivAt (x := x)).const_smul
    (2 : ℕ)).fderiv
  simp only [laplacianTrace, hessianForm, fderiv_norm_sq, hd]
  have hi (i : Fin 3) :
      innerSL ℝ (E := AmbientSpace) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1) = 1 := by
    change inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) = 1
    simp [EuclideanSpace.single]
  simp only [smul_apply, nsmul_eq_mul]
  simp_rw [hi]
  norm_num

lemma contDiff_neumannQuadratic (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : AmbientSpace => c * ‖x‖ ^ 2 / 6) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 6

lemma laplacianN_neumannQuadratic (c : ℝ) (x : AmbientSpace) :
    laplacianN (fun y : AmbientSpace => c * ‖y‖ ^ 2 / 6) x = c := by
  have hq : (fun y : AmbientSpace => c * ‖y‖ ^ 2 / 6) =
      (c / 6) • (fun y : AmbientSpace => ‖y‖ ^ 2) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [← laplacian_eq_laplacianN_of_contDiffAt
    ((contDiff_neumannQuadratic c).of_le (by simp)).contDiffAt,
    hq, laplacian_smul _ (contDiff_norm_sq ℝ).contDiffAt,
    laplacian_eq_laplacianN_of_contDiffAt (contDiff_norm_sq ℝ).contDiffAt,
    laplacianN_norm_sq, smul_eq_mul]
  ring

end LiquidDrop
