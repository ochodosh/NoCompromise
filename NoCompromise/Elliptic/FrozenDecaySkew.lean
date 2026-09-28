import NoCompromise.Elliptic.InteriorH2Hessian
import NoCompromise.Elliptic.CampanatoComparisonTests

/-! The constant skew part cancels against scalar weak gradients. This is
proved from the symmetry of smooth test Hessians and the distributional
first-derivative pairing, with no extra regularity on the weak function. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_fderiv_gradient_component {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    fderiv ℝ (gradient φ) x (EuclideanSpace.single i 1) j =
      poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x := by
  have hG : ContDiff ℝ 1 (gradient φ) := contDiff_gradient_of_contDiff_succ hφ
  have he : poissonCoordinateDerivative j φ = fun y => gradient φ y j :=
    funext (poissonCoordinateDerivative_eq_gradient j φ)
  rw [he]
  change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient φ) x _
  rw [((EuclideanSpace.proj j).hasFDerivAt.comp x
    ((hG.differentiable one_ne_zero x).hasFDerivAt)).fderiv]
  rfl

lemma frozen_linear_component_eq_sum {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    A v i = ∑ j, v j * A (EuclideanSpace.single j 1) i := by
  have he := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at he
  nth_rw 1 [← he]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]

lemma frozen_adjoint_component {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    A.adjoint (EuclideanSpace.single j 1) i = A (EuclideanSpace.single i 1) j := by
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] using
    A.adjoint_inner_right (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

lemma frozen_divergence_linear_gradient {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => A (gradient φ y)) x =
      ∑ i, ∑ j, poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x *
        A (EuclideanSpace.single j 1) i := by
  have hG := (contDiff_gradient_of_contDiff_succ hφ).differentiable one_ne_zero x
  have hd : fderiv ℝ (fun y => A (gradient φ y)) x = A.comp (fderiv ℝ (gradient φ) x) :=
    (A.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  simp only [divergenceN, hd, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [frozen_linear_component_eq_sum]
  simp only [frozen_fderiv_gradient_component hφ]

lemma frozen_divergence_adjoint_gradient {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => A.adjoint (gradient φ y)) x =
      divergenceN (fun y => A (gradient φ y)) x := by
  rw [frozen_divergence_linear_gradient _ hφ, frozen_divergence_linear_gradient _ hφ,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [frozen_adjoint_component, poissonCoordinateDerivative_comm hφ]

lemma frozen_tsupport_linear_gradient {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (fun y => A (gradient φ y)) ⊆ tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  change A (gradient φ x) = 0
  rw [gradient_eq_zero_of_notMem_tsupport h, map_zero]

/-- Transposing a constant coefficient does not change its scalar weak equation. -/
theorem HasWeakGradientOn.integral_adjoint_gradient {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasWeakGradientOn u G U)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x in U, inner ℝ (A.adjoint (G x)) (gradient φ x)) =
      ∫ x in U, inner ℝ (A (G x)) (gradient φ x) := by
  have hGφ : ContDiff ℝ 1 (gradient φ) := contDiff_gradient_of_contDiff_succ hφ
  have htest (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      -(∫ x in U, u x * divergenceN (fun y => B (gradient φ y)) x) =
        ∫ x in U, inner ℝ (B (gradient φ x)) (G x) :=
    hu.integral_divergence_eq (B.contDiff.comp hGφ)
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (frozen_tsupport_linear_gradient B φ))
      ((frozen_tsupport_linear_gradient B φ).trans hsφ)
  have h₁ := htest A
  have h₂ := htest A.adjoint
  simp_rw [frozen_divergence_adjoint_gradient A hφ] at h₂
  have he := h₁.symm.trans h₂
  convert he using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x
  · rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  · rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

end LiquidDrop
