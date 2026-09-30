module

public import NoCompromise.Elliptic.NondivSchauderNorm
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section

/-!
# Coordinate regularity and the full Hessian

This finite-dimensional step is independent of any PDE. C¹ regularity of every
actual coordinate derivative gives actual C² regularity. Common gradient bounds
for those scalar derivatives give operator-norm bounds for the Hessian, with the
explicit dimension factor n.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_euclidean_sum_single {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) = v := by
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

lemma nondiv_norm_clm_le_coordinate_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ≤ C) : ‖L‖ ≤ (n : ℝ) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : L v = ∑ i : Fin n, v i • L (EuclideanSpace.single i 1) := by
    calc
      L v = L (∑ i : Fin n, v i • EuclideanSpace.single i 1) := by
        rw [nondiv_euclidean_sum_single]
      _ = _ := by simp only [map_sum, map_smul]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v i) (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * C * ‖v‖ := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]; ring

/-- Actual coordinate derivatives C¹ imply actual C² on the same open set. -/
theorem nondiv_contDiff_two_of_coordinate_derivatives {n : ℕ}
    {z : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hz : ContDiffOn ℝ 1 z U)
    (hD : ∀ i : Fin n, ContDiffOn ℝ 1
      (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) U) :
    ContDiffOn ℝ 2 z U ∧ ContDiffOn ℝ 1 (fderiv ℝ z) U ∧
      ContDiffOn ℝ 1 (gradient z) U := by
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ z) U := by
    apply contDiffOn_clm_apply.mpr
    intro v
    have he : (fun x => fderiv ℝ z x v) =
        fun x => ∑ i : Fin n, v i * fderiv ℝ z x (EuclideanSpace.single i 1) := by
      funext x
      calc
        fderiv ℝ z x v = fderiv ℝ z x (∑ i : Fin n, v i • EuclideanSpace.single i 1) := by
          rw [nondiv_euclidean_sum_single]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [he]
    exact ContDiffOn.sum (fun i _ => contDiffOn_const.mul (hD i))
  have hz₂ : ContDiffOn ℝ 2 z U := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hz.differentiableOn one_ne_zero, by simp, hDf⟩
  refine ⟨hz₂, hDf, ?_⟩
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.contDiff
    |>.comp_contDiffOn hDf

lemma nondiv_fderiv_coordinate_eq {n : ℕ}
    {z : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hz : ContDiffOn ℝ 2 z U) (i : Fin n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x =
      (fderiv ℝ (fderiv ℝ z) x).flip (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ z) x :=
    (((hz.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero)
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add] using
    fderiv_clm_apply hd (differentiableAt_const (EuclideanSpace.single i (1 : ℝ)))

/-- Uniform scalar coordinate-gradient estimates control the full operator Hessian
and its Hölder norm, without changing the domain. -/
theorem nondiv_hessian_holder_of_coordinate_derivatives {n : ℕ} {α C : ℝ} (hC : 0 ≤ C)
    {z : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hz : ContDiffOn ℝ 1 z U)
    (hD : ∀ i : Fin n, ContDiffOn ℝ 1
      (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) U)
    (hb : ∀ i : Fin n, ∀ x ∈ U,
      ‖gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x‖ ≤ C)
    (hh : ∀ i : Fin n, ∀ x ∈ U, ∀ y ∈ U,
      ‖gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x -
        gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) y‖ ≤
          C * ‖x - y‖ ^ α) :
    ContDiffOn ℝ 2 z U ∧ ContDiffOn ℝ 1 (gradient z) U ∧
      HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ z)) U ∧
      holderNorm α (fderiv ℝ (fderiv ℝ z)) U ≤ 2 * (n : ℝ) * C ∧
      (∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ z) x‖ ≤ (n : ℝ) * C) ∧
      ∀ x ∈ U, ∀ y ∈ U,
        ‖fderiv ℝ (fderiv ℝ z) x - fderiv ℝ (fderiv ℝ z) y‖ ≤
          (n : ℝ) * C * ‖x - y‖ ^ α := by
  obtain ⟨hz₂, _, hgrad⟩ := nondiv_contDiff_two_of_coordinate_derivatives hU hz hD
  have hval (x) (hx : x ∈ U) : ‖fderiv ℝ (fderiv ℝ z) x‖ ≤ (n : ℝ) * C := by
    rw [← ContinuousLinearMap.opNorm_flip]
    apply nondiv_norm_clm_le_coordinate_bound _ hC
    intro i
    rw [← nondiv_fderiv_coordinate_eq hU hz₂ i hx]
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hb i x hx
  have hdiff (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      ‖fderiv ℝ (fderiv ℝ z) x - fderiv ℝ (fderiv ℝ z) y‖ ≤
        (n : ℝ) * C * ‖x - y‖ ^ α := by
    rw [← ContinuousLinearMap.opNorm_flip, mul_assoc]
    apply nondiv_norm_clm_le_coordinate_bound _
      (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg (x - y)) α))
    intro i
    have he : (fderiv ℝ (fderiv ℝ z) x - fderiv ℝ (fderiv ℝ z) y).flip
        (EuclideanSpace.single i 1) =
        fderiv ℝ (fun w => fderiv ℝ z w (EuclideanSpace.single i 1)) x -
          fderiv ℝ (fun w => fderiv ℝ z w (EuclideanSpace.single i 1)) y := by
      rw [nondiv_fderiv_coordinate_eq hU hz₂ i hx,
        nondiv_fderiv_coordinate_eq hU hz₂ i hy]
      rfl
    rw [he]
    simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using hh i x hx y hy
  have hq (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      ‖fderiv ℝ (fderiv ℝ z) x - fderiv ℝ (fderiv ℝ z) y‖ / ‖x - y‖ ^ α ≤
        (n : ℝ) * C := by
    by_cases he : x = y
    · subst y
      simp only [sub_self, norm_zero, zero_div]
      positivity
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr (hdiff x hx y hy)
  refine ⟨hz₂, hgrad, HasFiniteHolderNormOn.of_bounds (by positivity) (by positivity) hval hq,
    (holderNorm_le (by positivity) (by positivity) hval hq).trans_eq (by ring), hval, hdiff⟩

end LiquidDrop
