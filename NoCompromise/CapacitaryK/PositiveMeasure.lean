import NoCompromise.CapacitaryK.Bochner
import NoCompromise.CapacitaryK.LevelFrame
import NoCompromise.CapacitaryK.MuPositive
import NoCompromise.CapacitaryK.MuMeasure

/-!
# The positive measure `Δ|∇u|`: pointwise identities (chapter 31)

`lem:K-bochner` and `lem:K-level-identities`, for a `C³` function `u` on `ℝ³` that is harmonic
(`laplacianN u = 0`) on a neighbourhood of the point. The `C³` hypothesis replaces the
blueprint's "where u is harmonic" by the regularity actually used; harmonic functions are
smooth, and in the application `u` is the (smooth) capacitary potential.

File choice: the coordinate computations live in `CapacitaryK/Bochner.lean` (Bochner identity)
and `CapacitaryK/LevelFrame.lean` (frame identities), and the positivity of the distribution
`Δw` in `CapacitaryK/MuPositive.lean`, and its representation by a positive Radon measure in
`CapacitaryK/MuMeasure.lean`; this assigned module collects the blueprint statements.
For `prop:K-mu` the measure is obtained as a weak-star limit of the positive measures
`Δw_ε dx` (positive Riesz representation on `C_c(U)`), which is equivalent to the blueprint's
order-zero-plus-Riesz route.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop
open CapacitaryK

/-- `lem:K-bochner`: for `w_ε = (w² + ε²)^{1/2}` at a point where `w² + ε² > 0`,
`Δw_ε = |D²u|²/w_ε - |D²u∇u|²/w_ε³ ≥ ε²|D²u|²/w_ε³ ≥ 0`. -/
theorem CapacitaryK.K_bochner {u : E3 → ℝ} {x : E3} {ε : ℝ}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hpos : 0 < gradNorm u x ^ 2 + ε ^ 2) :
    laplacianN (gradNormEps ε u) x =
        hessNormSq u x / gradNormEps ε u x - hessGradNormSq u x / gradNormEps ε u x ^ 3 ∧
      ε ^ 2 * hessNormSq u x / gradNormEps ε u x ^ 3 ≤
        hessNormSq u x / gradNormEps ε u x - hessGradNormSq u x / gradNormEps ε u x ^ 3 ∧
      0 ≤ ε ^ 2 * hessNormSq u x / gradNormEps ε u x ^ 3 :=
  ⟨laplacianN_gradNormEps hu hΔ hpos, bochner_rhs_ge u x hpos⟩

/-- `|∇w|² = |D²u∇u|²/w²` where `w > 0`. -/
theorem CapacitaryK.norm_gradient_gradNorm_sq {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x) :
    ‖gradient (gradNorm u) x‖ ^ 2 = hessGradNormSq u x / gradNorm u x ^ 2 := by
  have hpos : 0 < gradNorm u x ^ 2 + (0:ℝ) ^ 2 := by positivity
  have hd : ∀ i, gradient (gradNorm u) x i = hessGrad u x i / gradNorm u x := by
    intro i
    have := poissonCoordinateDerivative_gradNormEps hu hpos i
    rw [gradNormEps_zero] at this
    rw [← poissonCoordinateDerivative_eq_gradient, this]
  have := gradNorm_sq (gradNorm u) x
  rw [gradNorm] at this
  rw [this, hessGradNormSq, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [hd, div_pow]

/-- `lem:K-level-identities`. At a point with `w > 0`, in an orthonormal frame
`e₁ = f 0, e₂ = f 1, ν = f 2` with `ν = -∇u/w`:
`∇u = -wν`, `D²u(eᵢ,eⱼ) = -wAᵢⱼ`, `D²u(eᵢ,ν) = -eᵢw`, `D²u(ν,ν) = Hw`, `∂_ν w = -Hw`, and
`Δw = (|D²u|² - |∇w|²)/w = w|A|² + |∇_Σ w|²/w`. -/
theorem CapacitaryK.K_level_identities {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hw : 0 < gradNorm u x)
    (f : OrthonormalBasis (Fin 3) ℝ E3) (hf : f 2 = unitNormal u x) :
    gradient u x = -(gradNorm u x • unitNormal u x) ∧
    (∀ a b : Fin 2, dirHess u x (f a.castSucc) (f b.castSucc) =
        -(gradNorm u x * secondFF u x (f a.castSucc) (f b.castSucc))) ∧
    (∀ a : Fin 2, dirHess u x (f a.castSucc) (unitNormal u x) =
        -(fderiv ℝ (gradNorm u) x (f a.castSucc))) ∧
    dirHess u x (unitNormal u x) (unitNormal u x) = meanCurv u x * gradNorm u x ∧
    fderiv ℝ (gradNorm u) x (unitNormal u x) = -(meanCurv u x * gradNorm u x) ∧
    laplacianN (gradNorm u) x =
      (hessNormSq u x - ‖gradient (gradNorm u) x‖ ^ 2) / gradNorm u x ∧
    (hessNormSq u x - ‖gradient (gradNorm u) x‖ ^ 2) / gradNorm u x =
      gradNorm u x * (∑ a : Fin 2, ∑ b : Fin 2,
          secondFF u x (f a.castSucc) (f b.castSucc) ^ 2) +
        (∑ a : Fin 2, (fderiv ℝ (gradNorm u) x (f a.castSucc)) ^ 2) / gradNorm u x := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hΔx : laplacianN u x = 0 := hΔ.self_of_nhds
  have hwne : gradNorm u x ≠ 0 := hw.ne'
  have hgrad : gradient u x = -(gradNorm u x • unitNormal u x) := by
    rw [unitNormal, smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hwne, one_smul]
  have htan : ∀ a : Fin 2, ⟪f a.castSucc, gradient u x⟫ = 0 := by
    intro a
    have hne : a.castSucc ≠ (2 : Fin 3) := by
      fin_cases a <;> decide
    rw [hgrad, inner_neg_right, inner_smul_right, ← hf,
      f.orthonormal.2 hne, mul_zero, neg_zero]
  refine ⟨hgrad, fun a b => dirHess_eq_neg_gradNorm_mul_secondFF hu2 hw _ (htan b),
    fun a => dirHess_unitNormal hu2 hw _, dirHess_unitNormal_unitNormal hu2 hw hΔx,
    fderiv_gradNorm_unitNormal hu2 hw hΔx, ?_, density_frame hu2 hw hΔx f hf⟩
  have hpos : 0 < gradNorm u x ^ 2 + (0:ℝ) ^ 2 := by positivity
  have hB := laplacianN_gradNormEps hu hΔ hpos
  rw [gradNormEps_zero] at hB
  rw [hB, norm_gradient_gradNorm_sq hu2 hw]
  ring

/-- `prop:K-mu`, positive-distribution half: on an open set `U` where `u` is `C³` and harmonic,
`⟨Δw, φ⟩ = ∫ w Δφ ≥ 0` for every nonnegative smooth test function `φ` with compact support in
`U`. The Radon-measure half is `CapacitaryK.K_mu`. -/
theorem CapacitaryK.K_mu_positive_distribution {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, gradNorm u x * laplacianN φ x :=
  integral_gradNorm_mul_laplacianN_nonneg hU hu hΔ hφ hcφ hsφ hφ0

/-- `prop:K-mu`: on an open set `U` where `u` is `C³` and harmonic, `Δw`, `w = |∇u|`, is a
positive Radon measure `μ` on `U`: `μ` is carried by `U`, finite on compact subsets of `U`, and
`⟨Δw, φ⟩ = ∫ w Δφ = ∫ φ dμ` for every smooth `φ` with compact support in `U`. -/
theorem CapacitaryK.K_mu {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) :
    ∃ μ : Measure E3, μ Uᶜ = 0 ∧ (∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤) ∧
      ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ :=
  K_mu_measure hU hu hΔ

end LiquidDrop
