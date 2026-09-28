import NoCompromise.Area.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Graph Jacobians in arbitrary dimension

The graph map appends the height as the last coordinate. Its norm determinant is
computed from the Gram matrix `I + p pᵀ`, using the matrix determinant lemma.
No nonlinear area formula is used.
-/

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Horizontal inclusion, with the final coordinate zero. -/
def graphBaseN (k : ℕ) : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  ∑ i : Fin k, (EuclideanSpace.proj i).smulRight (EuclideanSpace.single i.castSucc 1)

@[simp] lemma graphBaseN_castSucc {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    graphBaseN k x i.castSucc = x i := by
  simp [graphBaseN, Pi.single_apply, Fin.castSucc_inj]

@[simp] lemma graphBaseN_last {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    graphBaseN k x (Fin.last k) = 0 := by
  simp [graphBaseN]

/-- The standard graph map `x ↦ (x,f x)` in dimension `k`. -/
def graphMapN {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  graphBaseN k x + f x • EuclideanSpace.single (Fin.last k) 1

@[simp] lemma graphMapN_castSucc {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) : graphMapN f x i.castSucc = x i := by
  simp [graphMapN]

@[simp] lemma graphMapN_last {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : graphMapN f x (Fin.last k) = f x := by
  simp [graphMapN]

lemma graphMapN_injective {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Function.Injective (graphMapN f) := by
  intro x y h
  apply PiLp.ext
  intro i
  simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z i.castSucc) h

lemma norm_graphMapN_sub_sq {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x y : EuclideanSpace ℝ (Fin k)) :
    ‖graphMapN f x - graphMapN f y‖ ^ 2 = ‖x - y‖ ^ 2 + ‖f x - f y‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc, Real.norm_eq_abs, sq_abs]

lemma antilipschitzWith_graphMapN {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    AntilipschitzWith 1 (graphMapN f) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have heq := norm_graphMapN_sub_sq f x y
  nlinarith [sq_nonneg ‖f x - f y‖, norm_nonneg (x - y),
    norm_nonneg (graphMapN f x - graphMapN f y)]

lemma continuousOn_graphMapN {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin k))} (hf : ContinuousOn f U) :
    ContinuousOn (graphMapN f) U :=
  (graphBaseN k).continuous.continuousOn.add (hf.smul continuousOn_const)

lemma contDiffOn_graphMapN {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin k))} {r : WithTop ℕ∞}
    (hf : ContDiffOn ℝ r f U) : ContDiffOn ℝ r (graphMapN f) U :=
  (graphBaseN k).contDiff.contDiffOn.add (hf.smul contDiffOn_const)

/-- Linear graph parametrization with slope `p`. -/
def graphTangentN {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  graphBaseN k + (innerSL ℝ p).smulRight (EuclideanSpace.single (Fin.last k) 1)

@[simp] lemma graphTangentN_castSucc {k : ℕ} (p v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    graphTangentN p v i.castSucc = v i := by
  simp [graphTangentN]

@[simp] lemma graphTangentN_last {k : ℕ} (p v : EuclideanSpace ℝ (Fin k)) :
    graphTangentN p v (Fin.last k) = inner ℝ p v := by simp [graphTangentN]

lemma graphTangentN_injective {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    Function.Injective (graphTangentN p) := by
  intro x y h
  apply PiLp.ext
  intro i
  simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z i.castSucc) h

lemma norm_graphTangentN_sq {k : ℕ} (p v : EuclideanSpace ℝ (Fin k)) :
    ‖graphTangentN p v‖ ^ 2 = ‖v‖ ^ 2 + (inner ℝ p v) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]

lemma norm_le_graphTangentN {k : ℕ} (p v : EuclideanSpace ℝ (Fin k)) :
    ‖v‖ ≤ ‖graphTangentN p v‖ := by
  have h := norm_graphTangentN_sq p v
  nlinarith [sq_nonneg (inner ℝ p v), norm_nonneg v, norm_nonneg (graphTangentN p v)]

lemma inner_graphTangentN {k : ℕ} (p v w : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (graphTangentN p v) (graphTangentN p w) =
      inner ℝ v w + inner ℝ p v * inner ℝ p w := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc, RCLike.inner_apply, mul_comm]

lemma det_gram_graphTangentN {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    ((graphTangentN p).adjoint.comp (graphTangentN p)).det = 1 + ‖p‖ ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hm : LinearMap.toMatrix b b
      ((graphTangentN p).adjoint.comp (graphTangentN p)).toLinearMap =
      1 + Matrix.replicateCol Unit (fun i => p i) *
        Matrix.replicateRow Unit (fun i => p i) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change ((graphTangentN p).adjoint (graphTangentN p (b j))) i = _
    calc
      _ = inner ℝ (EuclideanSpace.single i 1)
          ((graphTangentN p).adjoint (graphTangentN p (b j))) := by
        simp [EuclideanSpace.inner_single_left]
      _ = inner ℝ (graphTangentN p (EuclideanSpace.single i 1))
          (graphTangentN p (b j)) := ContinuousLinearMap.adjoint_inner_right _ _ _
      _ = _ := by
        rw [inner_graphTangentN]
        simp [b, EuclideanSpace.basisFun_apply,
          EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.one_apply,
          PiLp.single_apply, eq_comm, mul_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hm,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

lemma normDet_graphTangentN {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    (graphTangentN p).normDet = Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [← det_gram_graphTangentN p, ← ContinuousLinearMap.normDet_sq]
  exact (Real.sqrt_sq (graphTangentN p).normDet_nonneg).symm

lemma hasFDerivAt_graphMapN {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (graphMapN f) (graphTangentN (gradient f x)) x := by
  have heq : fderiv ℝ f x = innerSL ℝ (gradient f x) := by
    ext v
    exact inner_gradient_left.symm
  have hdf := hf.hasFDerivAt
  rw [heq] at hdf
  exact (graphBaseN k).hasFDerivAt.add
    (hdf.smul_const (EuclideanSpace.single (Fin.last k) 1))

lemma fderiv_graphMapN {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (graphMapN f) x = graphTangentN (gradient f x) :=
  (hasFDerivAt_graphMapN hf).fderiv

lemma normDet_fderiv_graphMapN {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (graphMapN f) x).normDet = Real.sqrt (1 + ‖gradient f x‖ ^ 2) := by
  rw [fderiv_graphMapN hf, normDet_graphTangentN]

/-- The algebraic norm determinant is continuous in every fixed Euclidean dimension. -/
lemma continuous_normDet_euclidean {k m : ℕ} : Continuous
    (fun L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) => L.normDet) := by
  have heq (L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
      L.normDet = Real.sqrt (L.adjoint.comp L).det := by
    rw [← L.normDet_sq]
    exact (Real.sqrt_sq L.normDet_nonneg).symm
  simp_rw [heq]
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id))

end LiquidDrop
