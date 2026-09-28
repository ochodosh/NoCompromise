import NoCompromise.Elliptic.CampanatoComparisonFrozen
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quantitative linear normalization of frozen elliptic coefficients

The symmetric part has the same quadratic form as the original, possibly
nonsymmetric coefficient. Finite-dimensional spectral decomposition constructs
an actual invertible square root with explicit ellipticity bounds.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The symmetric part of a real coefficient operator. -/
def frozenSymmetricPart {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) : E →L[ℝ] E := (1 / 2 : ℝ) • (A + A.adjoint)

lemma frozenSymmetricPart_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (x : E) :
    inner ℝ (frozenSymmetricPart A x) x = inner ℝ (A x) x := by
  simp only [frozenSymmetricPart, FunLike.coe_smul, Pi.smul_apply,
    add_apply, real_inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm x (A x)]
  ring

lemma frozenSymmetricPart_isSymmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) :
    (frozenSymmetricPart A).IsSymmetric := by
  intro x y
  change inner ℝ ((1 / 2 : ℝ) • (A x + A.adjoint x)) y =
    inner ℝ x ((1 / 2 : ℝ) • (A y + A.adjoint y))
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  ring

lemma norm_frozenSymmetricPart_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) :
    ‖frozenSymmetricPart A‖ ≤ ‖A‖ := by
  calc
    ‖frozenSymmetricPart A‖ = (1 / 2 : ℝ) * ‖A + A.adjoint‖ := by
      rw [frozenSymmetricPart, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖A.adjoint‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

/-- A coercive real operator admits a symmetric invertible square root of its
symmetric part. The map and its inverse have the sharp ellipticity norm bounds. -/
theorem exists_frozen_normalizing_equiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hell : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) (hbound : ‖A‖ ≤ cap) :
    ∃ L : E ≃L[ℝ] E, L.toContinuousLinearMap.adjoint = L.toContinuousLinearMap ∧
      L.toContinuousLinearMap.comp L.toContinuousLinearMap = frozenSymmetricPart A ∧
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt cap ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ := by
  classical
  let S := frozenSymmetricPart A
  have hS : S.IsPositive := ⟨frozenSymmetricPart_isSymmetric A, fun x => by
    change 0 ≤ inner ℝ (frozenSymmetricPart A x) x
    rw [frozenSymmetricPart_inner]
    exact (mul_nonneg hlam.le (sq_nonneg _)).trans (hell x)⟩
  let b := hS.isSymmetric.eigenvectorBasis rfl
  let ev := hS.isSymmetric.eigenvalues rfl
  let T : E →L[ℝ] E := ∑ i, Real.sqrt (ev i) • rankOne ℝ (b i) (b i)
  have hTb (i : Fin (Module.finrank ℝ E)) : T (b i) = Real.sqrt (ev i) • b i := by
    simp [T, rankOne_apply, b.inner_eq_ite]
  have hTadj : T.adjoint = T := by
    simp only [T, map_sum, map_smul, adjoint_rankOne]
  have hTsq : T.comp T = S := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    change T (T (b i)) = S (b i)
    rw [hTb, map_smul, hTb, smul_smul, ← sq,
      Real.sq_sqrt (hS.toLinearMap.nonneg_eigenvalues rfl i)]
    exact (hS.isSymmetric.apply_eigenvectorBasis rfl i).symm
  have hnorm (x : E) : ‖T x‖ ^ 2 = inner ℝ (A x) x := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left, hTadj, hTsq]
    exact frozenSymmetricPart_inner A x
  have hlower (x : E) : Real.sqrt lam * ‖x‖ ≤ ‖T x‖ := by
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
    simp only [← sq]
    rw [mul_pow, Real.sq_sqrt hlam.le, hnorm]
    exact hell x
  have hupper (x : E) : ‖T x‖ ≤ Real.sqrt cap * ‖x‖ := by
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [← sq]
    rw [mul_pow, Real.sq_sqrt hcap, hnorm]
    calc
      inner ℝ (A x) x ≤ ‖A x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (cap * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        ((A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))
        (norm_nonneg _)
      _ = cap * ‖x‖ ^ 2 := by ring
  have hinj : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    change T x = 0 at hx
    have hi := hlower x
    rw [hx, norm_zero] at hi
    exact norm_eq_zero.mp (le_antisymm
      (nonpos_of_mul_nonpos_right hi (Real.sqrt_pos.mpr hlam)) (norm_nonneg _))
  let L := (LinearEquiv.ofBijective T.toLinearMap
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hL : L.toContinuousLinearMap = T := rfl
  refine ⟨L, hL.symm ▸ hTadj, ?_, ?_, ?_⟩
  · simpa only [hL] using hTsq
  · rw [hL]
    exact T.opNorm_le_bound (Real.sqrt_nonneg _) hupper
  · apply L.symm.toContinuousLinearMap.opNorm_le_bound (by positivity)
    intro x
    apply (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hlam)).mpr
    simpa only [← hL, ContinuousLinearEquiv.coe_coe,
      L.apply_symm_apply] using hlower (L.symm x)

end LiquidDrop
