module

public import NoCompromise.Elliptic.NondivSchauderEquation
public import NoCompromise.Elliptic.NondivSchauderDifference

@[expose] public section

/-!
# Difference quotients of the actual weak equation

Translations are justified by translated compact test functions. The resulting
scalar-source equation keeps the exact product-rule correction δₕA·Dz.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_gradient_addRight {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => φ (y + a)) x = gradient φ (x + a) := by
  simp only [gradient, fderiv_comp_add_right]

lemma IsWeakScalarDivergenceEquationOn.mono {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakScalarDivergenceEquationOn A D g U) (hVU : V ⊆ U) :
    IsWeakScalarDivergenceEquationOn A D g V :=
  fun φ hφ hcφ hsφ => he φ hφ hcφ (hsφ.trans hVU)

/-- Translation of the genuine distributional equation requires only the geometric
inclusion of translated test supports. -/
theorem IsWeakScalarDivergenceEquationOn.translate {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakScalarDivergenceEquationOn A D g U) (a : EuclideanSpace ℝ (Fin n))
    (hmap : ∀ x ∈ V, x + a ∈ U) :
    IsWeakScalarDivergenceEquationOn (fun x => A (x + a)) (fun x => D (x + a))
      (fun x => g (x + a)) V := by
  intro φ hφ hcφ hsφ
  let ψ := fun x => φ (x + -a)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.addRight (-a))
  have hsψ : tsupport ψ ⊆ U := by
    intro x hx
    change x ∈ tsupport (φ ∘ Homeomorph.addRight (-a)) at hx
    rw [tsupport_comp_eq_preimage] at hx
    have hxV : x + -a ∈ V := hsφ hx
    simpa only [add_assoc, neg_add_cancel, add_zero] using hmap (x + -a) hxV
  have ht := he ψ hψ hcψ hsψ
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : gradient ψ x = gradient φ (x + -a) :=
    nondiv_gradient_addRight φ (-a) x
  simp_rw [hgrad] at ht
  rw [← integral_add_right_eq_self
    (fun x => inner ℝ (A x (D x)) (gradient φ (x + -a))) a,
    ← integral_add_right_eq_self (fun x => ψ x * g x) a] at ht
  simpa only [ψ, add_neg_cancel_right] using ht

lemma nondiv_integrable_flux_test {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hF : ContinuousOn F U)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    Integrable (fun x => inner ℝ (F x) (gradient φ x)) := by
  have hcgrad : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  simpa only [real_inner_comm] using integrable_inner_compact_factor_on
    (hF.locallyIntegrableOn hU.measurableSet) (continuous_gradient_of_contDiff hφ)
    hcgrad ((tsupport_gradient_subset φ).trans hsφ)

/-- The discrete product rule for an operator field and vector field. -/
lemma nondiv_differenceQuotient_product {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (i : Fin n) (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    LiquidDrop.coordinateDifferenceQuotient i h (fun y => A y (D y)) x =
      A (x + h • EuclideanSpace.single i 1) (LiquidDrop.coordinateDifferenceQuotient i h D x) +
        LiquidDrop.coordinateDifferenceQuotient i h A x (D x) := by
  simp only [LiquidDrop.coordinateDifferenceQuotient, map_smul, map_sub, smul_apply, sub_apply]
  module

/-- Difference quotients satisfy the exact scalar-source equation. The correction
δₕA·D appears explicitly in the principal flux. No h-uniform derivative bound is assumed. -/
theorem IsWeakScalarDivergenceEquationOn.coordinateDifferenceQuotient {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakScalarDivergenceEquationOn A D g U) (hU : IsOpen U) (hV : IsOpen V)
    (hA : ContinuousOn A U) (hD : ContinuousOn D U) (hg : ContinuousOn g U)
    (hVU : V ⊆ U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x, inner ℝ
        (A (x + h • EuclideanSpace.single i 1) (LiquidDrop.coordinateDifferenceQuotient i h D x) +
          LiquidDrop.coordinateDifferenceQuotient i h A x (D x)) (gradient φ x)) =
        -(∫ x, φ x * LiquidDrop.coordinateDifferenceQuotient i h g x) := by
  intro φ hφ hcφ hsφ
  let a := h • EuclideanSpace.single i (1 : ℝ)
  have he₁ := he.translate a hmap φ hφ hcφ hsφ
  have he₀ := he φ hφ hcφ (hsφ.trans hVU)
  have hi₀ := nondiv_integrable_flux_test hU (hA.clm_apply hD)
    (hφ.of_le (by simp)) hcφ (hsφ.trans hVU)
  have hFc : ContinuousOn (fun x => A (x + a) (D (x + a))) V :=
    (hA.clm_apply hD).comp (continuous_id.add continuous_const).continuousOn hmap
  have hi₁ := nondiv_integrable_flux_test hV hFc (hφ.of_le (by simp)) hcφ hsφ
  have hig₀ := integrable_mul_compact_factor_on (hg.locallyIntegrableOn hU.measurableSet)
    hφ.continuous hcφ (hsφ.trans hVU)
  have hgc : ContinuousOn (fun x => g (x + a)) V :=
    hg.comp (continuous_id.add continuous_const).continuousOn hmap
  have hig₁ := integrable_mul_compact_factor_on (hgc.locallyIntegrableOn hV.measurableSet)
    hφ.continuous hcφ hsφ
  have hflux (x : EuclideanSpace ℝ (Fin n)) :
      A (x + h • EuclideanSpace.single i 1) (LiquidDrop.coordinateDifferenceQuotient i h D x) +
        LiquidDrop.coordinateDifferenceQuotient i h A x (D x) =
          LiquidDrop.coordinateDifferenceQuotient i h (fun y => A y (D y)) x :=
    (nondiv_differenceQuotient_product A D i h x).symm
  simp_rw [hflux]
  simp only [LiquidDrop.coordinateDifferenceQuotient, real_inner_smul_left,
    inner_sub_left, smul_eq_mul]
  have heR : (fun x => φ x * (h⁻¹ * (g (x + a) - g x))) =
      fun x => h⁻¹ * (φ x * g (x + a) - φ x * g x) := by
    funext x
    ring
  change (∫ x, h⁻¹ * (inner ℝ (A (x + a) (D (x + a))) (gradient φ x) -
      inner ℝ (A x (D x)) (gradient φ x))) = -(∫ x, φ x * (h⁻¹ * (g (x + a) - g x)))
  rw [heR, integral_const_mul, integral_const_mul, integral_sub hi₁ hi₀,
    integral_sub hig₁ hig₀, he₁, he₀]
  ring

end LiquidDrop
