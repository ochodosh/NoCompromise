module

public import NoCompromise.CapacitaryK.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-!
# Level-set frame identities (blueprint `lem:K-level-identities`)

At a point where `w = |∇u| > 0`, in an orthonormal frame `e₁, e₂, ν` adapted to the level
surface, `D²u(eᵢ, eⱼ) = -w Aᵢⱼ`, `D²u(eᵢ, ν) = -eᵢ w`, and, if `Δu = 0`,
`D²u(ν, ν) = H w`, `∂_ν w = -H w`; consequently
`(|D²u|² - |∇w|²) / w = w |A|² + |∇_Σ w|² / w`.
-/

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace Gradient Topology

namespace LiquidDrop
namespace CapacitaryK

variable {u : E3 → ℝ} {x : E3}

lemma inner_gradient_eq_fderiv (f : E3 → ℝ) (y v : E3) :
    ⟪gradient f y, v⟫ = fderiv ℝ f y v := by
  simp [gradient, toDual_symm_apply]

lemma differentiableAt_fderiv_of_contDiffAt (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (fderiv ℝ u) x :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

lemma differentiableAt_gradient_of_contDiffAt (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (gradient u) x := by
  rw [differentiableAt_euclidean]
  intro i
  have h : (fun y => gradient u y i) = fun y => fderiv ℝ u y (basisVec i) :=
    funext fun y => gradient_apply_eq_fderiv_basisVec u y i
  rw [h]
  exact (differentiableAt_fderiv_of_contDiffAt hu).clm_apply (differentiableAt_const _)

/-- `D²u(X, Y) = ⟪D_X ∇u, Y⟫`. -/
lemma dirHess_eq_inner (hu : ContDiffAt ℝ 2 u x) (X Y : E3) :
    dirHess u x X Y = ⟪fderiv ℝ (gradient u) x X, Y⟫ := by
  have h : (fun y => fderiv ℝ u y Y) = fun y => ⟪gradient u y, Y⟫ :=
    funext fun y => (inner_gradient_eq_fderiv u y Y).symm
  unfold dirHess
  rw [h, fderiv_inner_apply ℝ (differentiableAt_gradient_of_contDiffAt hu)
    (differentiableAt_const Y)]
  simp

/-- `D²u(X, Y) = D²u(Y, X)` for `u` of class `C²`. -/
lemma dirHess_comm (hu : ContDiffAt ℝ 2 u x) (X Y : E3) :
    dirHess u x X Y = dirHess u x Y X := by
  have hD := differentiableAt_fderiv_of_contDiffAt hu
  have key : ∀ X Y : E3, dirHess u x X Y = fderiv ℝ (fderiv ℝ u) x X Y := by
    intro X Y
    unfold dirHess
    rw [fderiv_clm_apply hD (differentiableAt_const Y)]
    simp
  rw [key, key]
  exact hu.isSymmSndFDerivAt (by simp) X Y

lemma gradient_ne_zero_of_gradNorm_pos (hw : 0 < gradNorm u x) : gradient u x ≠ 0 := by
  intro h
  simp [gradNorm, h] at hw

lemma differentiableAt_gradNorm (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) :
    DifferentiableAt ℝ (gradNorm u) x :=
  (differentiableAt_gradient_of_contDiffAt hu).norm ℝ (gradient_ne_zero_of_gradNorm_pos hw)

/-- `D_X w = w⁻¹ D²u(X, ∇u)`. -/
lemma fderiv_gradNorm_apply (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) (X : E3) :
    fderiv ℝ (gradNorm u) x X = (gradNorm u x)⁻¹ * dirHess u x X (gradient u x) := by
  have hG := (differentiableAt_gradient_of_contDiffAt hu).hasFDerivAt
  have hd := (differentiableAt_gradNorm hu hw).hasFDerivAt
  have h1 := hG.norm_sq
  have h2 := hd.mul hd
  have hfun : (gradNorm u * gradNorm u) = (‖gradient u ·‖ ^ 2) := by
    funext y; simp [gradNorm, sq]
  rw [hfun] at h2
  have := congrArg (fun L => L X) (h2.unique h1)
  simp only [add_apply, smul_apply,
    FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat] at this
  rw [dirHess_eq_inner hu, real_inner_comm, eq_inv_mul_iff_mul_eq₀ hw.ne']
  linarith

lemma gradient_eq_neg_smul_unitNormal (hw : 0 < gradNorm u x) :
    gradient u x = -(gradNorm u x • unitNormal u x) := by
  simp [unitNormal, smul_smul, hw.ne']

lemma inner_gradient_unitNormal (hw : 0 < gradNorm u x) :
    ⟪gradient u x, unitNormal u x⟫ = -gradNorm u x := by
  rw [unitNormal, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [gradNorm] at hw ⊢
  have := hw.ne'
  field_simp

lemma fderiv_unitNormal_apply (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) (X : E3) :
    fderiv ℝ (unitNormal u) x X = -((gradNorm u x)⁻¹ • fderiv ℝ (gradient u) x X +
      (-((gradNorm u x) ^ 2)⁻¹ * fderiv ℝ (gradNorm u) x X) • gradient u x) := by
  have hG := (differentiableAt_gradient_of_contDiffAt hu).hasFDerivAt
  have hd := (differentiableAt_gradNorm hu hw).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (gradNorm u y)⁻¹)
      ((-((gradNorm u x) ^ 2)⁻¹) • fderiv ℝ (gradNorm u) x) x :=
    (hasDerivAt_inv hw.ne').comp_hasFDerivAt x hd
  have hν : HasFDerivAt (unitNormal u) (-((gradNorm u x)⁻¹ • fderiv ℝ (gradient u) x +
      ((-((gradNorm u x) ^ 2)⁻¹) • fderiv ℝ (gradNorm u) x).smulRight (gradient u x))) x :=
    (hinv.fun_smul hG).neg
  rw [hν.fderiv]
  simp only [neg_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- `A(X, Y) = -w⁻¹ D²u(X, Y) + w⁻² (D_X w) ⟪∇u, Y⟫`. -/
lemma secondFF_eq (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) (X Y : E3) :
    secondFF u x X Y = -((gradNorm u x)⁻¹ * dirHess u x X Y) +
      ((gradNorm u x) ^ 2)⁻¹ * fderiv ℝ (gradNorm u) x X * ⟪gradient u x, Y⟫ := by
  rw [secondFF, fderiv_unitNormal_apply hu hw, dirHess_eq_inner hu]
  simp only [inner_neg_left, inner_add_left, real_inner_smul_left]
  ring

lemma dirHess_unitNormal_right (hu : ContDiffAt ℝ 2 u x) (X : E3) :
    dirHess u x X (unitNormal u x) = -((gradNorm u x)⁻¹ * dirHess u x X (gradient u x)) := by
  rw [dirHess_eq_inner hu, dirHess_eq_inner hu, unitNormal, inner_neg_right,
    real_inner_smul_right]

lemma dirHess_unitNormal_left (hu : ContDiffAt ℝ 2 u x) (Y : E3) :
    dirHess u x (unitNormal u x) Y = -((gradNorm u x)⁻¹ * dirHess u x (gradient u x) Y) := by
  rw [dirHess_eq_inner hu, dirHess_eq_inner hu, unitNormal, map_neg, map_smul, inner_neg_left,
    real_inner_smul_left]

theorem dirHess_eq_neg_gradNorm_mul_secondFF (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (X : E3) {Y : E3} (hY : ⟪Y, gradient u x⟫ = 0) :
    dirHess u x X Y = -(gradNorm u x * secondFF u x X Y) := by
  rw [secondFF_eq hu hw, real_inner_comm, hY]
  have := hw.ne'
  field_simp
  ring

theorem dirHess_unitNormal (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) (X : E3) :
    dirHess u x X (unitNormal u x) = -(fderiv ℝ (gradNorm u) x X) := by
  rw [dirHess_unitNormal_right hu, fderiv_gradNorm_apply hu hw]

/-- `∑ᵢ D²u(bᵢ, Y) ⟪Z, bᵢ⟫ = D²u(Z, Y)`. -/
lemma sum_dirHess_basisVec_mul_inner (hu : ContDiffAt ℝ 2 u x) (Y Z : E3) :
    ∑ i, dirHess u x (basisVec i) Y * ⟪Z, basisVec i⟫ = dirHess u x Z Y := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_inner_mul_inner Z
    (fderiv ℝ (gradient u) x Y)
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [dirHess_comm hu Z, dirHess_eq_inner hu, real_inner_comm, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dirHess_comm hu, dirHess_eq_inner hu,
    real_inner_comm (basisVec i) (fderiv ℝ (gradient u) x Y)]
  exact mul_comm _ _

lemma laplacianN_eq_sum_dirHess (u : E3 → ℝ) (x : E3) :
    laplacianN u x = ∑ i, dirHess u x (basisVec i) (basisVec i) := rfl

/-- For harmonic `u`, `H = w⁻³ D²u(∇u, ∇u)`. -/
lemma meanCurv_eq (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (hΔ : laplacianN u x = 0) :
    meanCurv u x = ((gradNorm u x) ^ 3)⁻¹ * dirHess u x (gradient u x) (gradient u x) := by
  have hw0 := hw.ne'
  have hsum : ∑ i, secondFF u x (basisVec i) (basisVec i) =
      -((gradNorm u x)⁻¹ * ∑ i, dirHess u x (basisVec i) (basisVec i)) +
        ((gradNorm u x) ^ 3)⁻¹ *
          ∑ i, dirHess u x (basisVec i) (gradient u x) * ⟪gradient u x, basisVec i⟫ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [secondFF_eq hu hw, fderiv_gradNorm_apply hu hw]
    field_simp
  have hνν : secondFF u x (unitNormal u x) (unitNormal u x) = 0 := by
    rw [secondFF_eq hu hw, fderiv_gradNorm_apply hu hw, inner_gradient_unitNormal hw,
      dirHess_unitNormal_right hu, dirHess_unitNormal_left hu]
    field_simp
    ring
  rw [meanCurv, hsum, hνν, ← laplacianN_eq_sum_dirHess, hΔ,
    sum_dirHess_basisVec_mul_inner hu]
  ring

theorem dirHess_unitNormal_unitNormal (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (hΔ : laplacianN u x = 0) :
    dirHess u x (unitNormal u x) (unitNormal u x) = meanCurv u x * gradNorm u x := by
  rw [meanCurv_eq hu hw hΔ, dirHess_unitNormal_right hu, dirHess_unitNormal_left hu]
  have := hw.ne'
  field_simp

theorem fderiv_gradNorm_unitNormal (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (hΔ : laplacianN u x = 0) :
    fderiv ℝ (gradNorm u) x (unitNormal u x) = -(meanCurv u x * gradNorm u x) := by
  rw [← dirHess_unitNormal_unitNormal hu hw hΔ, dirHess_unitNormal hu hw, neg_neg]

/-- Parseval in an orthonormal basis of `ℝ³`. -/
lemma sum_inner_sq_eq_norm_sq (b : OrthonormalBasis (Fin 3) ℝ E3) (v : E3) :
    ∑ i, ⟪v, b i⟫ ^ 2 = ‖v‖ ^ 2 := by
  have h := b.sum_inner_mul_inner v v
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq, real_inner_comm (b i) v]

lemma sum_sq_dirHess_eq_sum_norm_sq (hu : ContDiffAt ℝ 2 u x)
    (e : OrthonormalBasis (Fin 3) ℝ E3) :
    ∑ i, ∑ j, dirHess u x (e i) (e j) ^ 2 = ∑ i, ‖fderiv ℝ (gradient u) x (e i)‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [dirHess_eq_inner hu]
  exact sum_inner_sq_eq_norm_sq e _

/-- Hilbert–Schmidt invariance of `∑ᵢⱼ D²u(eᵢ, eⱼ)²`. -/
lemma sum_sq_dirHess_invariant (hu : ContDiffAt ℝ 2 u x)
    (e f : OrthonormalBasis (Fin 3) ℝ E3) :
    ∑ i, ∑ j, dirHess u x (e i) (e j) ^ 2 = ∑ k, ∑ l, dirHess u x (f k) (f l) ^ 2 := by
  rw [sum_sq_dirHess_eq_sum_norm_sq hu e, sum_sq_dirHess_eq_sum_norm_sq hu f]
  calc ∑ i, ‖fderiv ℝ (gradient u) x (e i)‖ ^ 2
      = ∑ i, ∑ k, dirHess u x (e i) (f k) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [dirHess_eq_inner hu]
        exact (sum_inner_sq_eq_norm_sq f _).symm
    _ = ∑ k, ∑ i, dirHess u x (f k) (e i) ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [dirHess_comm hu (e _)]
    _ = ∑ k, ‖fderiv ℝ (gradient u) x (f k)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp_rw [dirHess_eq_inner hu]
        exact sum_inner_sq_eq_norm_sq e _

lemma hessNormSq_eq_sum_frame (hu : ContDiffAt ℝ 2 u x) (f : OrthonormalBasis (Fin 3) ℝ E3) :
    hessNormSq u x = ∑ k, ∑ l, dirHess u x (f k) (f l) ^ 2 := by
  rw [← sum_sq_dirHess_invariant hu (EuclideanSpace.basisFun (Fin 3) ℝ) f]
  simp only [hessNormSq, hess_eq_dirHess, EuclideanSpace.basisFun_apply]

lemma norm_gradient_sq_eq_sum_frame (g : E3 → ℝ) (f : OrthonormalBasis (Fin 3) ℝ E3) :
    ‖gradient g x‖ ^ 2 = ∑ k, (fderiv ℝ g x (f k)) ^ 2 := by
  rw [← sum_inner_sq_eq_norm_sq f]
  simp_rw [inner_gradient_eq_fderiv]

/-- Second equality of eq:K-density in an adapted orthonormal frame `f 0, f 1, f 2 = ν`. -/
theorem density_frame (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (hΔ : laplacianN u x = 0) (f : OrthonormalBasis (Fin 3) ℝ E3) (hf : f 2 = unitNormal u x) :
    (hessNormSq u x - ‖gradient (gradNorm u) x‖ ^ 2) / gradNorm u x =
      gradNorm u x * (∑ a : Fin 2, ∑ b : Fin 2,
          secondFF u x (f a.castSucc) (f b.castSucc) ^ 2) +
        (∑ a : Fin 2, (fderiv ℝ (gradNorm u) x (f a.castSucc)) ^ 2) / gradNorm u x := by
  have tang : ∀ i : Fin 3, i ≠ 2 → ⟪f i, gradient u x⟫ = 0 := by
    intro i hi
    rw [gradient_eq_neg_smul_unitNormal hw, ← hf, inner_neg_right, real_inner_smul_right,
      f.inner_eq_zero hi, mul_zero, neg_zero]
  have t0 := tang 0 (by decide)
  have t1 := tang 1 (by decide)
  have c0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
  have c1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
  rw [hessNormSq_eq_sum_frame hu f, norm_gradient_sq_eq_sum_frame (gradNorm u) f]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, c0, c1, hf]
  rw [dirHess_eq_neg_gradNorm_mul_secondFF hu hw (f 0) t0,
    dirHess_eq_neg_gradNorm_mul_secondFF hu hw (f 0) t1,
    dirHess_eq_neg_gradNorm_mul_secondFF hu hw (f 1) t0,
    dirHess_eq_neg_gradNorm_mul_secondFF hu hw (f 1) t1,
    dirHess_unitNormal hu hw (f 0), dirHess_unitNormal hu hw (f 1),
    dirHess_comm hu (unitNormal u x) (f 0), dirHess_comm hu (unitNormal u x) (f 1),
    dirHess_unitNormal hu hw (f 0), dirHess_unitNormal hu hw (f 1),
    dirHess_unitNormal_unitNormal hu hw hΔ, fderiv_gradNorm_unitNormal hu hw hΔ]
  have := hw.ne'
  field_simp
  ring

end CapacitaryK
end LiquidDrop
