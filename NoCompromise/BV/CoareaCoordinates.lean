module

public import NoCompromise.Area.C1GraphAlgebra
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Coordinates for scalar coarea

The horizontal coordinates precede the final scalar coordinate. These elementary
linear identities support inverse-function charts; no coarea theorem is used.
-/

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Projection onto the first `k` Euclidean coordinates. -/
def graphProjectionN (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ∑ i : Fin k, (EuclideanSpace.proj i.castSucc).smulRight (EuclideanSpace.single i 1)

@[simp] lemma graphProjectionN_apply {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1)))
    (i : Fin k) : graphProjectionN k x i = x i.castSucc := by
  simp [graphProjectionN, Pi.single_apply]

/-- Append a scalar as the final Euclidean coordinate. -/
def graphAppendN {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  graphBaseN k x + t • EuclideanSpace.single (Fin.last k) 1

@[simp] lemma graphAppendN_castSucc {k : ℕ} (x : EuclideanSpace ℝ (Fin k))
    (t : ℝ) (i : Fin k) : graphAppendN x t i.castSucc = x i := by simp [graphAppendN]

@[simp] lemma graphAppendN_last {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    graphAppendN x t (Fin.last k) = t := by simp [graphAppendN]

@[simp] lemma graphProjectionN_append {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    graphProjectionN k (graphAppendN x t) = x := by ext i; simp

@[simp] lemma graphAppendN_projection {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    graphAppendN (graphProjectionN k x) (x (Fin.last k)) = x := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma norm_sq_graphProjectionN {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖x‖ ^ 2 = ‖graphProjectionN k x‖ ^ 2 + (x (Fin.last k)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq]
  simp

lemma inner_graphAppendN {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1)))
    (x : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    inner ℝ p (graphAppendN x t) =
      inner ℝ (graphProjectionN k p) x + p (Fin.last k) * t := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc, RCLike.inner_apply, mul_comm]

/-- Euclidean last-coordinate splitting, with the scalar first for Tonelli. -/
def euclideanLastEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin k) :=
  ({ toLinearMap := (EuclideanSpace.proj (Fin.last k)).prod (graphProjectionN k)
     invFun := fun p => graphAppendN p.2 p.1
     left_inv := graphAppendN_projection
     right_inv := by intro p; ext <;> simp } :
       EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ]
         ℝ × EuclideanSpace ℝ (Fin k)).toContinuousLinearEquiv

@[simp] lemma euclideanLastEquiv_apply {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    euclideanLastEquiv k x = (x (Fin.last k), graphProjectionN k x) := rfl

@[simp] lemma euclideanLastEquiv_symm_apply {k : ℕ}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    (euclideanLastEquiv k).symm p = graphAppendN p.2 p.1 := rfl

/-- Replace the final coordinate by a scalar function. -/
def coareaCoordinateMap {k : ℕ} (u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin (k + 1)) :=
  graphAppendN (graphProjectionN k x) (u x)

@[simp] lemma coareaCoordinateMap_castSucc {k : ℕ}
    (u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (x : EuclideanSpace ℝ (Fin (k + 1)))
    (i : Fin k) : coareaCoordinateMap u x i.castSucc = x i.castSucc := by
  simp [coareaCoordinateMap]

@[simp] lemma coareaCoordinateMap_last {k : ℕ}
    (u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    coareaCoordinateMap u x (Fin.last k) = u x := by simp [coareaCoordinateMap]

/-- The derivative of the coordinate replacement map. -/
def coareaCoordinateLinear {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1))) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  ContinuousLinearMap.id ℝ _ +
    (innerSL ℝ p - EuclideanSpace.proj (Fin.last k)).smulRight
      (EuclideanSpace.single (Fin.last k) 1)

@[simp] lemma coareaCoordinateLinear_castSucc {k : ℕ}
    (p v : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin k) :
    coareaCoordinateLinear p v i.castSucc = v i.castSucc := by simp [coareaCoordinateLinear]

@[simp] lemma coareaCoordinateLinear_last {k : ℕ}
    (p v : EuclideanSpace ℝ (Fin (k + 1))) :
    coareaCoordinateLinear p v (Fin.last k) = inner ℝ p v := by simp [coareaCoordinateLinear]

lemma det_coareaCoordinateLinear {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1))) :
    (coareaCoordinateLinear p).det = p (Fin.last k) := by
  let b := (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (coareaCoordinateLinear p).toLinearMap =
      1 + Matrix.replicateCol Unit (fun i => if i = Fin.last k then (1 : ℝ) else 0) *
        Matrix.replicateRow Unit (fun i => p i - if i = Fin.last k then 1 else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [b, coareaCoordinateLinear, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.one_apply,
      eq_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hm,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]

/-- The graph slope of a level surface when the last derivative is nonzero. -/
def coareaGraphSlope {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1))) :
    EuclideanSpace ℝ (Fin k) := -(p (Fin.last k))⁻¹ • graphProjectionN k p

lemma coareaGraphSlope_density {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1)))
    (hp : p (Fin.last k) ≠ 0) :
    Real.sqrt (1 + ‖coareaGraphSlope p‖ ^ 2) = ‖p‖ / |p (Fin.last k)| := by
  have hnorm := norm_sq_graphProjectionN p
  have hsq : (Real.sqrt (1 + ‖coareaGraphSlope p‖ ^ 2)) ^ 2 =
      (‖p‖ / |p (Fin.last k)|) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    simp only [coareaGraphSlope, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, mul_pow,
      inv_pow, sq_abs, div_pow]
    field_simp
    nlinarith
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (norm_nonneg _) (abs_nonneg _))).mp hsq

/-- Coordinate replacement is a rank-one perturbation of the identity. -/
lemma coareaCoordinateMap_eq {k : ℕ} (u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    coareaCoordinateMap u x = x + (u x - x (Fin.last k)) •
      EuclideanSpace.single (Fin.last k) 1 := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma contDiffOn_coareaCoordinateMap {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} {U : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    {r : WithTop ℕ∞} (hu : ContDiffOn ℝ r u U) :
    ContDiffOn ℝ r (coareaCoordinateMap u) U := by
  rw [funext (coareaCoordinateMap_eq u)]
  exact contDiffOn_id.add
    ((hu.sub (EuclideanSpace.proj (Fin.last k)).contDiff.contDiffOn).smul contDiffOn_const)

lemma hasFDerivAt_coareaCoordinateMap {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} {x : EuclideanSpace ℝ (Fin (k + 1))}
    (hu : DifferentiableAt ℝ u x) :
    HasFDerivAt (coareaCoordinateMap u) (coareaCoordinateLinear (gradient u x)) x := by
  have heq : fderiv ℝ u x = innerSL ℝ (gradient u x) := by
    ext v
    exact inner_gradient_left.symm
  have hdu := hu.hasFDerivAt
  rw [heq] at hdu
  rw [funext (coareaCoordinateMap_eq u)]
  exact (hasFDerivAt_id x).add
    ((hdu.sub (EuclideanSpace.proj (Fin.last k)).hasFDerivAt).smul_const
      (EuclideanSpace.single (Fin.last k) 1))

/-- Nonzero last derivative makes the coordinate differential invertible. -/
def coareaCoordinateEquiv {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1)))
    (hp : p (Fin.last k) ≠ 0) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  ((coareaCoordinateLinear p).toLinearMap.equivOfIsUnitDet
    (by
      change IsUnit (coareaCoordinateLinear p).det
      rw [det_coareaCoordinateLinear]
      exact isUnit_iff_ne_zero.mpr hp)).toContinuousLinearEquiv

@[simp] lemma coareaCoordinateEquiv_apply {k : ℕ}
    (p x : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0) :
    coareaCoordinateEquiv p hp x = coareaCoordinateLinear p x := by
  simp [coareaCoordinateEquiv]

lemma coareaCoordinateEquiv_toContinuousLinearMap {k : ℕ}
    (p : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0) :
    (coareaCoordinateEquiv p hp).toContinuousLinearMap = coareaCoordinateLinear p := by
  apply ContinuousLinearMap.ext
  intro x
  exact coareaCoordinateEquiv_apply p x hp

lemma coareaCoordinateLinear_graphTangentN {k : ℕ}
    (p : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0)
    (v : EuclideanSpace ℝ (Fin k)) :
    coareaCoordinateLinear p (graphTangentN (coareaGraphSlope p) v) = graphBaseN k v := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [coareaCoordinateLinear_last, graphBaseN_last]
    change inner ℝ p (graphAppendN v (inner ℝ (coareaGraphSlope p) v)) = 0
    rw [inner_graphAppendN, coareaGraphSlope, real_inner_smul_left]
    field_simp
    ring
  · simp

lemma coareaCoordinateEquiv_symm_graphBaseN {k : ℕ}
    (p : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0)
    (v : EuclideanSpace ℝ (Fin k)) :
    (coareaCoordinateEquiv p hp).symm (graphBaseN k v) =
      graphTangentN (coareaGraphSlope p) v := by
  apply (coareaCoordinateEquiv p hp).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, coareaCoordinateEquiv_apply,
    coareaCoordinateLinear_graphTangentN p hp]

lemma det_coareaCoordinateEquiv_symm {k : ℕ}
    (p : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0) :
    (coareaCoordinateEquiv p hp).symm.toContinuousLinearMap.det = (p (Fin.last k))⁻¹ := by
  change (coareaCoordinateEquiv p hp).toLinearEquiv.symm.toLinearMap.det = _
  rw [LinearEquiv.det_coe_symm]
  change (coareaCoordinateEquiv p hp).toContinuousLinearMap.det⁻¹ = _
  rw [coareaCoordinateEquiv_toContinuousLinearMap, det_coareaCoordinateLinear]

/-- Euclidean volume splits as scalar Lebesgue measure times horizontal volume. -/
lemma euclideanLastEquiv_measurePreserving (k : ℕ) :
    MeasurePreserving (euclideanLastEquiv k) volume (volume.prod volume) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin k))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).comp
        (PiLp.volume_preserving_ofLp (Fin (k + 1))))
  have heq : (euclideanLastEquiv k : EuclideanSpace ℝ (Fin (k + 1)) →
      ℝ × EuclideanSpace ℝ (Fin k)) =
      Prod.map id (WithLp.toLp 2) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)) ∘
          WithLp.ofLp := by
    funext x
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro i
      simp [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply, Fin.init]
  rw [heq]
  exact h

/-- Tonelli in horizontal coordinates and the final scalar coordinate. -/
lemma lintegral_euclidean_last {k : ℕ} {q : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞}
    (hq : Measurable q) :
    (∫⁻ z, q z) =
      ∫⁻ t : ℝ, ∫⁻ x : EuclideanSpace ℝ (Fin k), q (graphAppendN x t) := by
  let e := (euclideanLastEquiv k).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume (volume.prod volume) :=
    euclideanLastEquiv_measurePreserving k
  have hi := MeasurePreserving.symm e he
  calc
    _ = ∫⁻ p : ℝ × EuclideanSpace ℝ (Fin k), q (e.symm p) ∂volume.prod volume :=
      (hi.lintegral_comp hq).symm
    _ = _ := lintegral_prod _ (hq.comp hi.measurable).aemeasurable

lemma hasFDerivAt_graphAppendN {k : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    HasFDerivAt (fun y => graphAppendN y t) (graphBaseN k) x :=
  (graphBaseN k).hasFDerivAt.add_const _

lemma contDiff_graphAppendN {k : ℕ} (t : ℝ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun x : EuclideanSpace ℝ (Fin k) => graphAppendN x t) :=
  (graphBaseN k).contDiff.add contDiff_const

/-- The inverse coordinate Jacobian converts gradient mass into graph area. -/
lemma coarea_inverse_jacobian_factor {k : ℕ}
    (p : EuclideanSpace ℝ (Fin (k + 1))) (hp : p (Fin.last k) ≠ 0) :
    |(coareaCoordinateEquiv p hp).symm.toContinuousLinearMap.det| * ‖p‖ =
      Real.sqrt (1 + ‖coareaGraphSlope p‖ ^ 2) := by
  rw [det_coareaCoordinateEquiv_symm, abs_inv, coareaGraphSlope_density p hp]
  simp [div_eq_mul_inv, mul_comm]

end LiquidDrop
