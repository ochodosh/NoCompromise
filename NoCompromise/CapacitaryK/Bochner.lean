import NoCompromise.CapacitaryK.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bochner identity for the regularised gradient length

All derivatives use the standard coordinate directions on `E3`. Harmonicity is
assumed on a neighbourhood of the point, so it can be differentiated there.
-/

noncomputable section
open Filter
open scoped Topology Gradient ContDiff

namespace LiquidDrop.CapacitaryK

private lemma contDiffAt_coord {u : E3 → ℝ} {x : E3} {n : ℕ∞ω}
    (hu : ContDiffAt ℝ (n + 1) u x) (i : Fin 3) :
    ContDiffAt ℝ n (poissonCoordinateDerivative i u) x :=
  (hu.fderiv_right le_rfl).clm_apply contDiffAt_const

private lemma coord_sum {f : Fin 3 → E3 → ℝ} {x : E3}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 3) :
    poissonCoordinateDerivative i (fun y => ∑ j, f j y) x =
      ∑ j, poissonCoordinateDerivative i (f j) x := by
  simp only [poissonCoordinateDerivative, fderiv_fun_sum (fun j _ => hf j),
    sum_apply]

private lemma coord_mul {f g : E3 → ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    poissonCoordinateDerivative i (fun y => f y * g y) x =
      f x * poissonCoordinateDerivative i g x +
        g x * poissonCoordinateDerivative i f x := by
  simp [poissonCoordinateDerivative, fderiv_fun_mul hf hg]

private lemma contDiffAt_gradient_coord {u : E3 → ℝ} {x : E3} {n : ℕ∞ω}
    (hu : ContDiffAt ℝ (n + 1) u x) (i : Fin 3) :
    ContDiffAt ℝ n (fun y => gradient u y i) x := by
  have h := contDiffAt_coord hu i
  change ContDiffAt ℝ n (fun y => poissonCoordinateDerivative i u y) x at h
  simpa only [poissonCoordinateDerivative_eq_gradient] using h

private lemma contDiffAt_gradNorm_sq {u : E3 → ℝ} {x : E3} {n : ℕ∞ω}
    (hu : ContDiffAt ℝ (n + 1) u x) :
    ContDiffAt ℝ n (fun y => gradNorm u y ^ 2) x := by
  simp only [gradNorm_sq]
  exact ContDiffAt.sum fun i _ => (contDiffAt_gradient_coord hu i).pow 2

private lemma coord_gradNorm_sq {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i : Fin 3) :
    poissonCoordinateDerivative i (fun y => gradNorm u y ^ 2) x =
      2 * hessGrad u x i := by
  simp only [gradNorm_sq]
  rw [coord_sum (f := fun j y => gradient u y j ^ 2)
    (fun j => ((contDiffAt_gradient_coord (n := 1) hu j).differentiableAt (by norm_num)).pow 2)]
  simp only [hessGrad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj := (contDiffAt_gradient_coord (n := 1) hu j).differentiableAt (by norm_num)
  simp only [pow_two]
  rw [coord_mul hj hj]
  have heq : poissonCoordinateDerivative i (fun y => gradient u y j) x =
      hess u x i j := by
    change poissonCoordinateDerivative i (fun y => gradient u y j) x =
      poissonCoordinateDerivative i (fun y => poissonCoordinateDerivative j u y) x
    simp only [poissonCoordinateDerivative_eq_gradient]
  rw [heq]
  ring

private lemma contDiffAt_gradNormEps {u : E3 → ℝ} {x : E3} {ε : ℝ} {n : ℕ∞ω}
    (hu : ContDiffAt ℝ (n + 1) u x) (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) :
    ContDiffAt ℝ n (gradNormEps ε u) x :=
  ((contDiffAt_gradNorm_sq hu).add contDiffAt_const).sqrt (ne_of_gt hpos)

/-- Gradient of `w_ε`: `∂ᵢ w_ε = (D²u ∇u)ᵢ / w_ε`. -/
theorem poissonCoordinateDerivative_gradNormEps {u : E3 → ℝ} {x : E3} {ε : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) (i : Fin 3) :
    poissonCoordinateDerivative i (gradNormEps ε u) x = hessGrad u x i / gradNormEps ε u x := by
  have hd : DifferentiableAt ℝ (fun y => gradNorm u y ^ 2 + ε ^ 2) x :=
    ((contDiffAt_gradNorm_sq (n := 1) hu).differentiableAt (by norm_num)).add_const _
  change fderiv ℝ (fun y => Real.sqrt (gradNorm u y ^ 2 + ε ^ 2)) x (basisVec i) = _
  rw [fderiv_sqrt hd (ne_of_gt hpos), ContinuousLinearMap.smul_apply,
    fderiv_add_const]
  change (1 / (2 * gradNormEps ε u x)) *
    poissonCoordinateDerivative i (fun y => gradNorm u y ^ 2) x = _
  rw [coord_gradNorm_sq hu]
  ring

private lemma coord_congr {f g : E3 → ℝ} {x : E3}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 3) :
    poissonCoordinateDerivative i f x = poissonCoordinateDerivative i g x :=
  congrArg (fun L : E3 →L[ℝ] ℝ => L (basisVec i)) h.fderiv_eq

private lemma coord_comm {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x =
      poissonCoordinateDerivative j (poissonCoordinateDerivative i u) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt one_ne_zero
  have key : ∀ a b : Fin 3, poissonCoordinateDerivative a (poissonCoordinateDerivative b u) x =
      fderiv ℝ (fderiv ℝ u) x (basisVec a) (basisVec b) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ u y (basisVec b)) x (basisVec a) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hu.isSymmSndFDerivAt (by simp) (basisVec i) (basisVec j)

private lemma coord_third_comm {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (i j : Fin 3) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative i
      (poissonCoordinateDerivative j u)) x =
      poissonCoordinateDerivative j (poissonCoordinateDerivative i
        (poissonCoordinateDerivative i u)) x := by
  -- Commute the inner pair on a neighbourhood before differentiating it.
  have heq : poissonCoordinateDerivative i (poissonCoordinateDerivative j u) =ᶠ[𝓝 x]
      poissonCoordinateDerivative j (poissonCoordinateDerivative i u) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact coord_comm (hy.of_le (by norm_num)) i j
  rw [coord_congr heq i]
  exact coord_comm (contDiffAt_coord (n := 2) hu i) i j

private lemma sum_coord_third_eq_zero {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (j : Fin 3) :
    (∑ i, poissonCoordinateDerivative i (poissonCoordinateDerivative i
      (poissonCoordinateDerivative j u)) x) = 0 := by
  simp_rw [coord_third_comm hu]
  rw [← coord_sum (fun i => (contDiffAt_coord (n := 1) (contDiffAt_coord (n := 2) hu i) i).differentiableAt
    (by norm_num))]
  change poissonCoordinateDerivative j (laplacianN u) x = 0
  rw [coord_congr hΔ j]
  simp [poissonCoordinateDerivative]

private lemma coord_div {f g : E3 → ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hg0 : g x ≠ 0) (i : Fin 3) :
    poissonCoordinateDerivative i (fun y => f y / g y) x =
      poissonCoordinateDerivative i f x / g x -
        f x * poissonCoordinateDerivative i g x / g x ^ 2 := by
  have hinv : poissonCoordinateDerivative i (fun y => (g y)⁻¹) x =
      -(g x ^ 2)⁻¹ * poissonCoordinateDerivative i g x := by
    have h : HasFDerivAt (fun y => (g y)⁻¹) ((-(g x ^ 2)⁻¹) • fderiv ℝ g x) x :=
      (hasDerivAt_inv hg0).comp_hasFDerivAt x hg.hasFDerivAt
    show fderiv ℝ (fun y => (g y)⁻¹) x (basisVec i) = -(g x ^ 2)⁻¹ * fderiv ℝ g x (basisVec i)
    rw [h.fderiv]
    simp
  simp only [div_eq_mul_inv]
  rw [coord_mul (g := fun y => (g y)⁻¹) hf (hg.inv hg0), hinv]
  ring

private lemma contDiffAt_hess {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (i j : Fin 3) :
    ContDiffAt ℝ 1 (fun y => hess u y i j) x :=
  contDiffAt_coord (n := 1) (contDiffAt_coord (n := 2) hu j) i

private lemma contDiffAt_hessGrad {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (i : Fin 3) :
    ContDiffAt ℝ 1 (fun y => hessGrad u y i) x := by
  exact ContDiffAt.sum fun j _ => (contDiffAt_hess hu i j).mul
    (contDiffAt_gradient_coord (hu.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)) j)

private lemma coord_hessGrad {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (i : Fin 3) :
    poissonCoordinateDerivative i (fun y => hessGrad u y i) x =
      (∑ j, hess u x i j ^ 2) +
        ∑ j, gradient u x j * poissonCoordinateDerivative i
          (poissonCoordinateDerivative i (poissonCoordinateDerivative j u)) x := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  simp only [hessGrad]
  rw [coord_sum (f := fun j y => hess u y i j * gradient u y j)
    (fun j => ((contDiffAt_hess hu i j).differentiableAt one_ne_zero).mul
    ((contDiffAt_gradient_coord (n := 1) hu2 j).differentiableAt one_ne_zero))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [coord_mul ((contDiffAt_hess hu i j).differentiableAt one_ne_zero)
    ((contDiffAt_gradient_coord (n := 1) hu2 j).differentiableAt one_ne_zero)]
  have heq : poissonCoordinateDerivative i (fun y => gradient u y j) x =
      hess u x i j := by
    change poissonCoordinateDerivative i (fun y => gradient u y j) x =
      poissonCoordinateDerivative i (fun y => poissonCoordinateDerivative j u y) x
    simp only [poissonCoordinateDerivative_eq_gradient]
  rw [heq, pow_two]
  rfl

private lemma coord_twice_gradNormEps {u : E3 → ℝ} {x : E3} {ε : ℝ}
    (hu : ContDiffAt ℝ 3 u x) (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) (i : Fin 3) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative i (gradNormEps ε u)) x =
      ((∑ j, hess u x i j ^ 2) +
        ∑ j, gradient u x j * poissonCoordinateDerivative i
          (poissonCoordinateDerivative i (poissonCoordinateDerivative j u)) x) /
        gradNormEps ε u x - hessGrad u x i ^ 2 / gradNormEps ε u x ^ 3 := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hnear : ∀ᶠ y in 𝓝 x, 0 < gradNorm u y ^ 2 + ε ^ 2 :=
    ((contDiffAt_gradNorm_sq (n := 1) hu2).continuousAt.add continuousAt_const).eventually
      (Ioi_mem_nhds hpos)
  have heq : poissonCoordinateDerivative i (gradNormEps ε u) =ᶠ[𝓝 x]
      (fun y => hessGrad u y i / gradNormEps ε u y) := by
    filter_upwards [hu2.eventually (by norm_num), hnear] with y hy hp
    exact poissonCoordinateDerivative_gradNormEps hy hp i
  -- This neighbourhood equality licenses the second differentiation.
  have hw : gradNormEps ε u x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  rw [coord_congr heq i, coord_div
    ((contDiffAt_hessGrad hu i).differentiableAt one_ne_zero)
    ((contDiffAt_gradNormEps (n := 1) hu2 hpos).differentiableAt one_ne_zero) hw,
    poissonCoordinateDerivative_gradNormEps hu2 hpos, coord_hessGrad hu]
  field_simp [hw]

/-- The Bochner identity (first equality of eq:K-bochner).
Also valid at `ε = 0` where `w > 0`. -/
theorem laplacianN_gradNormEps {u : E3 → ℝ} {x : E3} {ε : ℝ}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) :
    laplacianN (gradNormEps ε u) x =
      hessNormSq u x / gradNormEps ε u x - hessGradNormSq u x / gradNormEps ε u x ^ 3 := by
  -- The derivative of harmonicity cancels the third-derivative contribution.
  have hthird : (∑ i, ∑ j, gradient u x j * poissonCoordinateDerivative i
      (poissonCoordinateDerivative i (poissonCoordinateDerivative j u)) x) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_coord_third_eq_zero hu hΔ, mul_zero]
    exact Finset.sum_const_zero
  simp only [laplacianN, coord_twice_gradNormEps hu hpos, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_add_distrib, hthird, add_zero, hessNormSq, hessGradNormSq]

/-- Cauchy–Schwarz `|D²u ∇u|² ≤ |D²u|² |∇u|²` (pure algebra, no regularity). -/
theorem hessGradNormSq_le (u : E3 → ℝ) (x : E3) :
    hessGradNormSq u x ≤ hessNormSq u x * gradNorm u x ^ 2 := by
  rw [hessGradNormSq, hessNormSq, gradNorm_sq, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (hess u x i) (fun j => gradient u x j)

/-- The two inequalities of eq:K-bochner (pure algebra). -/
theorem bochner_rhs_ge (u : E3 → ℝ) (x : E3) {ε : ℝ}
    (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) :
    ε ^ 2 * hessNormSq u x / gradNormEps ε u x ^ 3 ≤
      hessNormSq u x / gradNormEps ε u x - hessGradNormSq u x / gradNormEps ε u x ^ 3 ∧
    0 ≤ ε ^ 2 * hessNormSq u x / gradNormEps ε u x ^ 3 := by
  have hw : 0 < gradNormEps ε u x := Real.sqrt_pos.mpr hpos
  have hH : 0 ≤ hessNormSq u x :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · have heq : hessNormSq u x / gradNormEps ε u x -
        hessGradNormSq u x / gradNormEps ε u x ^ 3 =
        (hessNormSq u x * gradNormEps ε u x ^ 2 - hessGradNormSq u x) /
          gradNormEps ε u x ^ 3 := by
      field_simp [ne_of_gt hw]
    rw [heq]
    apply (div_le_div_iff_of_pos_right (pow_pos hw 3)).mpr
    rw [sq_gradNormEps]
    nlinarith [hessGradNormSq_le u x]
  · exact div_nonneg (mul_nonneg (sq_nonneg ε) hH) (le_of_lt (pow_pos hw 3))

end LiquidDrop.CapacitaryK
