import NoCompromise.Elliptic.NondivSchauderData

/-!
# Distributional nondivergence equations

For C¹ coefficients and a C¹ solution, `aᵢⱼ∂ᵢ∂ⱼz` is defined by integrating
once by parts: its action on φ is `-∫ ⟪∇z, div(φ A)⟫`. The test functions are
C∞ with compact support in the domain. This is equivalent to the genuine
scalar-source divergence equation, and uses no second derivative of z.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The distributional equation aᵢⱼ∂ᵢ∂ⱼz+bᵢ∂ᵢz=f, with the principal term
paired by one integration by parts. -/
def IsWeakNondivergenceEquationOn {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ → tsupport φ ⊆ U →
    -(∫ x, inner ℝ (gradient z x) (nondivCoefficientDivergence (fun y => φ y • A y) x)) +
      (∫ x, φ x * inner ℝ (b x) (gradient z x)) = ∫ x, φ x * f x

/-- A scalar-source divergence equation, initially with genuine C∞ test functions. -/
def IsWeakScalarDivergenceEquationOn {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x, inner ℝ (A x (D x)) (gradient φ x)) = -(∫ x, φ x * g x)

lemma nondivCoefficientDivergence_eq_zero_of_notMem_tsupport {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport A) :
    nondivCoefficientDivergence A x = 0 := by
  simp only [nondivCoefficientDivergence, fderiv_of_notMem_tsupport ℝ hx, map_zero]

lemma continuousOn_nondivCoefficientDivergence {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) :
    ContinuousOn (nondivCoefficientDivergence A) U :=
  (nondivCoefficientContraction n).continuous.comp_continuousOn
    (hA.continuousOn_fderiv_of_isOpen hU le_rfl)

/-- Multiplication by a supported test gives the global product identity, even
when coefficients are only regular on the open domain. -/
lemma nondivCoefficientDivergence_smul_test {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ) (hsφ : tsupport φ ⊆ U)
    (x : EuclideanSpace ℝ (Fin n)) :
    nondivCoefficientDivergence (fun y => φ y • A y) x =
      φ x • nondivCoefficientDivergence A x + (A x).adjoint (gradient φ x) := by
  by_cases hx : x ∈ U
  · exact nondivCoefficientDivergence_smul
      ((hA.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)
      (hφ.differentiable one_ne_zero x)
  · have hxφ : x ∉ tsupport φ := fun h => hx (hsφ h)
    rw [nondivCoefficientDivergence_eq_zero_of_notMem_tsupport
      (fun h => hxφ (tsupport_smul_subset_left φ A h)),
      image_eq_zero_of_notMem_tsupport hxφ, gradient_eq_zero_of_notMem_tsupport hxφ,
      zero_smul, map_zero, add_zero]

lemma integral_nondivCoefficientDivergence_smul_test {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {z φ : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hz : ContDiffOn ℝ 1 z U)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (gradient z x) (nondivCoefficientDivergence (fun y => φ y • A y) x)) =
      (∫ x, φ x * inner ℝ (nondivCoefficientDivergence A x) (gradient z x)) +
        ∫ x, inner ℝ (A x (gradient z x)) (gradient φ x) := by
  have hG := continuousOn_gradient_of_contDiffOn hU hz
  have hD := continuousOn_nondivCoefficientDivergence hU hA
  have hi₁ := integrable_mul_compact_factor_on
    ((hD.inner hG).locallyIntegrableOn hU.measurableSet) hφ.continuous hcφ hsφ
  have hcgrad : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  have hi₂ : Integrable (fun x => inner ℝ (A x (gradient z x)) (gradient φ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      ((hA.continuousOn.clm_apply hG).locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hφ) hcgrad ((tsupport_gradient_subset φ).trans hsφ)
  rw [← integral_add hi₁ hi₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change inner ℝ (gradient z x)
      (nondivCoefficientDivergence (fun y => φ y • A y) x) = _
    rw [nondivCoefficientDivergence_smul_test hU hA hφ hsφ,
      inner_add_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      real_inner_comm (nondivCoefficientDivergence A x) (gradient z x)]

/-- Exact equivalence between the original distributional nondivergence equation
and its scalar-source divergence form. All regularity is only C¹ for A and z. -/
theorem isWeakNondivergenceEquationOn_iff_divergence {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hb : ContinuousOn b U)
    (hz : ContDiffOn ℝ 1 z U) (hf : ContinuousOn f U) :
    IsWeakNondivergenceEquationOn A b z f U ↔
      IsWeakScalarDivergenceEquationOn A (gradient z) (nondivDivergenceSource A b z f) U := by
  have htest (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
      (∫ x, φ x * nondivDivergenceSource A b z f x) = (∫ x, φ x * f x) +
        (∫ x, φ x * inner ℝ (nondivCoefficientDivergence A x) (gradient z x)) -
          ∫ x, φ x * inner ℝ (b x) (gradient z x) := by
    have hG := continuousOn_gradient_of_contDiffOn hU hz
    have hD := continuousOn_nondivCoefficientDivergence hU hA
    have hi₁ := integrable_mul_compact_factor_on (hf.locallyIntegrableOn hU.measurableSet)
      hφ.continuous hcφ hsφ
    have hi₂ := integrable_mul_compact_factor_on
      ((hD.inner hG).locallyIntegrableOn hU.measurableSet) hφ.continuous hcφ hsφ
    have hi₃ := integrable_mul_compact_factor_on
      ((hb.inner hG).locallyIntegrableOn hU.measurableSet) hφ.continuous hcφ hsφ
    simp only [nondivDivergenceSource, inner_sub_left, mul_add, mul_sub]
    have hi₂₃ : Integrable (fun x =>
        φ x * inner ℝ (nondivCoefficientDivergence A x) (gradient z x) -
          φ x * inner ℝ (b x) (gradient z x)) := by simpa using! hi₂.sub hi₃
    rw [integral_add hi₁ hi₂₃, integral_sub hi₂ hi₃]
    ring
  constructor
  · intro he φ hφ hcφ hsφ
    have he' := he φ hφ hcφ hsφ
    rw [integral_nondivCoefficientDivergence_smul_test hU hA hz
      (hφ.of_le (by simp)) hcφ hsφ] at he'
    rw [htest φ hφ hcφ hsφ]
    linarith
  · intro he φ hφ hcφ hsφ
    have he' := he φ hφ hcφ hsφ
    rw [htest φ hφ hcφ hsφ] at he'
    rw [integral_nondivCoefficientDivergence_smul_test hU hA hz
      (hφ.of_le (by simp)) hcφ hsφ]
    linarith

/-- The precise divergence equation and Hölder datum supplied by the blueprint hypotheses. -/
theorem IsWeakNondivergenceEquationOn.divergence {n : ℕ} {α : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakNondivergenceEquationOn A b z f U) (hU : IsOpen U)
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U) :
    IsWeakScalarDivergenceEquationOn A (gradient z) (nondivDivergenceSource A b z f) U ∧
      HasFiniteHolderNormOn α (nondivDivergenceSource A b z f) U ∧
      holderNorm α (nondivDivergenceSource A b z f) U ≤ holderNorm α f U +
        3 * (n * nondivC1HolderNorm α A U + holderNorm α b U) * nondivC1HolderNorm α z U :=
  ⟨(isWeakNondivergenceEquationOn_iff_divergence hU hA.contDiff
    (hb.nondiv_continuousOn hα) hz.contDiff (hf.nondiv_continuousOn hα)).mp he,
    nondivDivergenceSource_holder hA hb hz hf⟩

end LiquidDrop
