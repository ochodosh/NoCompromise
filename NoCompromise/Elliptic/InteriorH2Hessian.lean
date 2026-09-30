module

public import NoCompromise.Elliptic.InteriorH2Energy
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-!
# The compact smooth Hessian identity

Two elementary integrations by parts identify the squared L² norm of the full
Hessian with that of the Laplacian. No elliptic regularity theorem is assumed.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

lemma poissonCoordinateDerivative_smooth {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (poissonCoordinateDerivative i u) := by
  exact (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

lemma poissonCoordinateDerivative_second {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  change fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x _ = _
  rw [h.fderiv]
  simp

lemma poissonCoordinateDerivative_comm {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x =
      poissonCoordinateDerivative j (poissonCoordinateDerivative i u) x := by
  rw [poissonCoordinateDerivative_second hu i j x, poissonCoordinateDerivative_second hu j i x]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Two integrations by parts transfer a mixed derivative's square to diagonal derivatives. -/
lemma integral_poissonCoordinateDerivative_second_sq {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcu : HasCompactSupport u) (i j : Fin n) :
    (∫ x, poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x ^ 2) =
      ∫ x, poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x *
        poissonCoordinateDerivative j (poissonCoordinateDerivative j u) x := by
  have hD (k : Fin n) := poissonCoordinateDerivative_smooth hu k
  have hDD (k l : Fin n) := poissonCoordinateDerivative_smooth (hD l) k
  have hcD (k : Fin n) := HasCompactSupport.poissonCoordinateDerivative hcu k
  have hcDD (k l : Fin n) := HasCompactSupport.poissonCoordinateDerivative (hcD l) k
  have he : poissonCoordinateDerivative j (poissonCoordinateDerivative i u) =
      poissonCoordinateDerivative i (poissonCoordinateDerivative j u) :=
    funext (poissonCoordinateDerivative_comm (hu.of_le (by simp)) j i)
  have he3 :
      poissonCoordinateDerivative j
        (poissonCoordinateDerivative i (poissonCoordinateDerivative i u)) =
      poissonCoordinateDerivative i
        (poissonCoordinateDerivative i (poissonCoordinateDerivative j u)) :=
    (funext (poissonCoordinateDerivative_comm ((hD i).of_le (by simp)) j i)).trans
      (congrArg (poissonCoordinateDerivative i) he)
  have hleft := integral_mul_poissonCoordinateDerivative ((hD j).of_le (by simp))
    ((hDD i j).of_le (by simp)) (hcDD i j) i
  have hright := integral_mul_poissonCoordinateDerivative ((hDD i i).of_le (by simp))
    ((hD j).of_le (by simp)) (hcD j) j
  rw [he3] at hright
  simp only [pow_two]
  linarith only [hleft, hright]

/-- The total squared Hessian equals the squared Laplacian in L² for compact smooth functions. -/
theorem integral_poisson_hessian_sq_eq_laplacian_sq {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcu : HasCompactSupport u) :
    (∑ i, ∑ j, ∫ x, poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x ^ 2) =
      ∫ x, laplacianN u x ^ 2 := by
  classical
  have hD (i : Fin n) := poissonCoordinateDerivative_smooth hu i
  have hDD (i : Fin n) := poissonCoordinateDerivative_smooth (hD i) i
  have hcD (i : Fin n) := HasCompactSupport.poissonCoordinateDerivative hcu i
  have hcDD (i : Fin n) := HasCompactSupport.poissonCoordinateDerivative (hcD i) i
  have hi (i j : Fin n) : Integrable (fun x =>
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x *
        poissonCoordinateDerivative j (poissonCoordinateDerivative j u) x) :=
    ((hDD i).continuous.mul (hDD j).continuous).integrable_of_hasCompactSupport
      ((hcDD i).mul_right (f' := poissonCoordinateDerivative j (poissonCoordinateDerivative j u)))
  simp_rw [integral_poissonCoordinateDerivative_second_sq hu hcu]
  simp only [laplacianN, pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hi i j)).symm

lemma tsupport_laplacianN_subset {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (laplacianN u) ⊆ tsupport u := by
  classical
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun h => hn
    ((tsupport_poissonCoordinateDerivative_subset i u)
      ((tsupport_poissonCoordinateDerivative_subset i (poissonCoordinateDerivative i u)) h)))

/-- Each Hessian row is L²-bounded by the Laplacian for a compact smooth function. -/
theorem lpNorm_gradient_poissonCoordinateDerivative_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcu : HasCompactSupport u) (i : Fin n) :
    lpNorm (gradient (poissonCoordinateDerivative i u)) 2 volume ≤
      lpNorm (laplacianN u) 2 volume := by
  classical
  have hD (j : Fin n) := poissonCoordinateDerivative_smooth hu j
  have hDD (j k : Fin n) := poissonCoordinateDerivative_smooth (hD k) j
  have hcD (j : Fin n) := HasCompactSupport.poissonCoordinateDerivative hcu j
  have hcDD (j k : Fin n) := HasCompactSupport.poissonCoordinateDerivative (hcD k) j
  have hmDD (j k : Fin n) : MemLp
      (poissonCoordinateDerivative j (poissonCoordinateDerivative k u)) 2 volume :=
    (hDD j k).continuous.memLp_of_hasCompactSupport (hcDD j k)
  have hiDD (j k : Fin n) : Integrable
      (fun x => poissonCoordinateDerivative j (poissonCoordinateDerivative k u) x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hmDD j k).integrable_norm_pow (by norm_num)
  have hmgrad : MemLp (gradient (poissonCoordinateDerivative i u)) 2 volume :=
    (continuous_gradient_of_contDiff ((hD i).of_le (by simp))).memLp_of_hasCompactSupport
      ((hcD i).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_gradient_subset (poissonCoordinateDerivative i u)))
  have hmlap : MemLp (laplacianN u) 2 volume :=
    (continuous_laplacianN (hu.of_le (by simp))).memLp_of_hasCompactSupport
      (hcu.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset u))
  have hrow : (∫ x, ‖gradient (poissonCoordinateDerivative i u) x‖ ^ 2) =
      ∑ j, ∫ x, poissonCoordinateDerivative j (poissonCoordinateDerivative i u) x ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs,
      ← poissonCoordinateDerivative_eq_gradient]
    exact integral_finsetSum _ (fun j _ => hiDD j i)
  have htotal :
      (∑ k, ∑ j, ∫ x, poissonCoordinateDerivative j (poissonCoordinateDerivative k u) x ^ 2) =
        ∫ x, laplacianN u x ^ 2 := by
    rw [Finset.sum_comm]
    exact integral_poisson_hessian_sq_eq_laplacian_sq hu hcu
  have hbound : (∫ x, ‖gradient (poissonCoordinateDerivative i u) x‖ ^ 2) ≤
      ∫ x, laplacianN u x ^ 2 := by
    rw [hrow, ← htotal]
    have hn (k : Fin n) : 0 ≤
        ∑ j, ∫ x, poissonCoordinateDerivative j (poissonCoordinateDerivative k u) x ^ 2 :=
      Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
    exact Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)
  have hsq : lpNorm (gradient (poissonCoordinateDerivative i u)) 2 volume ^ 2 ≤
      lpNorm (laplacianN u) 2 volume ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hmgrad, lpNorm_two_sq_eq_integral_norm_sq hmlap]
    simpa only [Real.norm_eq_abs, sq_abs] using hbound
  have h0 : 0 ≤ lpNorm (laplacianN u) 2 volume := lpNorm_nonneg
  have h0g : 0 ≤ lpNorm (gradient (poissonCoordinateDerivative i u)) 2 volume := lpNorm_nonneg
  nlinarith

/-- The coordinate definition of the Laplacian agrees with divergence of the gradient. -/
lemma laplacianN_eq_divergenceN_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ (Fin n)) : laplacianN u x = divergenceN (gradient u) x := by
  classical
  have hG : ContDiff ℝ 1 (gradient u) := contDiff_gradient_of_contDiff_succ hu
  apply Finset.sum_congr rfl
  intro i _
  have heq : poissonCoordinateDerivative i u = fun y => gradient u y i :=
    funext (poissonCoordinateDerivative_eq_gradient i u)
  rw [heq]
  change fderiv ℝ ((EuclideanSpace.proj i) ∘ gradient u) x _ = _
  rw [((EuclideanSpace.proj i).hasFDerivAt.comp x
    ((hG.differentiable one_ne_zero x).hasFDerivAt)).fderiv]
  rfl

/-- The classical Laplacian product rule used to localize the Hessian identity. -/
lemma laplacianN_mul {n : ℕ} {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 2 η) (x : EuclideanSpace ℝ (Fin n)) :
    laplacianN (fun y => η y * u y) x = η x * laplacianN u x + u x * laplacianN η x +
      2 * inner ℝ (gradient η x) (gradient u x) := by
  have hu1 := hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hη1 := hη.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hGu : ContDiff ℝ 1 (gradient u) := contDiff_gradient_of_contDiff_succ hu
  have hGη : ContDiff ℝ 1 (gradient η) := contDiff_gradient_of_contDiff_succ hη
  rw [laplacianN_eq_divergenceN_gradient (hη.mul hu)]
  rw [funext (gradient_mul hη1 hu1)]
  change divergenceN ((fun y => η y • gradient u y) +
    (fun y => u y • gradient η y)) x = _
  rw [divergenceN_add (X := fun y => η y • gradient u y)
    (Y := fun y => u y • gradient η y) (hη1.smul hGu) (hu1.smul hGη),
    divergenceN_smul hη1 hGu, divergenceN_smul hu1 hGη,
    ← laplacianN_eq_divergenceN_gradient hu, ← laplacianN_eq_divergenceN_gradient hη]
  rw [real_inner_comm (gradient u x)]
  ring

end LiquidDrop
