module

public import NoCompromise.BV.ScalarDistribution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

/-!
# Uniqueness of local scalar derivative representations

Smooth compact coordinate tests determine a locally integrable vector density
on an open overlap. For different underlying measures, Radon–Nikodym densities
with respect to their sum reduce uniqueness to the same-measure statement.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Compact continuous vector fields can be paired with any locally integrable
vector density, even if the underlying measure has infinite total mass. -/
lemma integrable_inner_density_compact {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hX : Continuous X) (hcX : HasCompactSupport X) :
    Integrable (fun x => inner ℝ (X x) (σ x)) μ := by
  have hi := integrable_finsetSum Finset.univ
    (fun i _ => integrable_coordinate_density_pairing hσ hX hcX i)
  simpa only [PiLp.inner_apply, Real.inner_apply] using! hi

/-- Coordinate test equality under a common measure gives actual AE density
agreement on the open overlap. -/
theorem ae_eq_density_on_of_coordinate_pairings {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hσ : LocallyIntegrable σ μ) (hτ : LocallyIntegrable τ μ)
    (hpair : ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
      ContDiff ℝ 1 φ → tsupport φ ⊆ U →
        (∫ x, φ x * σ x i ∂μ) = ∫ x, φ x * τ x i ∂μ) :
    σ =ᵐ[μ.restrict U] τ := by
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hσ.sub hτ).locallyIntegrableOn U) ?_
  · apply (ae_restrict_iff' hU.measurableSet).mpr
    exact hz.mono fun x hx hxU => sub_eq_zero.mp (hx hxU)
  · intro φ hφ hcφ hsφ
    have hiσ := hσ.integrable_smul_left_of_hasCompactSupport hφ.continuous hcφ
    have hiτ := hτ.integrable_smul_left_of_hasCompactSupport hφ.continuous hcφ
    have heq : (∫ x, φ x • σ x ∂μ) = ∫ x, φ x • τ x ∂μ := by
      apply PiLp.ext
      intro i
      rw [eval_integral_piLp hiσ.eval_piLp, eval_integral_piLp hiτ.eval_piLp]
      let ψ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ :=
        ⟨⟨φ, hφ.continuous⟩, hcφ⟩
      simpa only [PiLp.smul_apply, smul_eq_mul] using!
        hpair i ψ (hφ.of_le (by simp)) hsφ
    simp_rw [Pi.sub_apply, smul_sub]
    rw [integral_sub hiσ hiτ, heq, sub_self]

/-- A locally integrable density transports to a dominating sigma-finite measure
by multiplication by the actual Radon–Nikodym derivative. -/
lemma locallyIntegrable_rnDeriv_smul {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin n))} [SigmaFinite μ] [SigmaFinite ρ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hμρ : μ ≪ ρ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ρ x).toReal • σ x) ρ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hm : (ρ.restrict K).withDensity (μ.rnDeriv ρ) = μ.restrict K := by
    rw [← restrict_withDensity hK.measurableSet, Measure.withDensity_rnDeriv_eq _ _ hμρ]
  apply (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
    (ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _))).mp
  rw [hm]
  exact hσ.integrableOn_isCompact hK

/-- Distinct positive measures and their locally integrable vector densities
represent the same derivative on every Borel part of an open overlap if their
original coordinate test pairings agree. -/
theorem setIntegral_inner_eq_of_coordinate_pairings {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin n))} [SigmaFinite μ] [SigmaFinite ρ]
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hσ : LocallyIntegrable σ μ) (hτ : LocallyIntegrable τ ρ)
    (hpair : ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
      ContDiff ℝ 1 φ → tsupport φ ⊆ U →
        (∫ x, φ x * σ x i ∂μ) = ∫ x, φ x * τ x i ∂ρ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    (∫ x in A, inner ℝ (X x) (σ x) ∂μ) = ∫ x in A, inner ℝ (X x) (τ x) ∂ρ := by
  let κ := μ + ρ
  have hμκ : μ ≪ κ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hρκ : ρ ≪ κ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let S := fun x => (μ.rnDeriv κ x).toReal • σ x
  let T := fun x => (ρ.rnDeriv κ x).toReal • τ x
  have hS := locallyIntegrable_rnDeriv_smul hσ hμκ
  have hT := locallyIntegrable_rnDeriv_smul hτ hρκ
  have hpair' (i : Fin n)
      (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
      (hφ : ContDiff ℝ 1 φ) (hsφ : tsupport φ ⊆ U) :
      (∫ x, φ x * S x i ∂κ) = ∫ x, φ x * T x i ∂κ := by
    simp only [S, T, PiLp.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (φ _) _]
    rw [integral_toReal_rnDeriv_mul hμκ, integral_toReal_rnDeriv_mul hρκ]
    exact hpair i φ hφ hsφ
  have heq := ae_eq_density_on_of_coordinate_pairings hU hS hT hpair'
  have heqA : S =ᵐ[κ.restrict A] T := ae_mono (Measure.restrict_mono hAU le_rfl) heq
  calc
    _ = ∫ x in A, inner ℝ (X x) (S x) ∂κ := by
      simpa only [S, inner_smul_right] using
        (setIntegral_toReal_rnDeriv_mul hμκ hA
          (f := fun x => inner ℝ (X x) (σ x))).symm
    _ = ∫ x in A, inner ℝ (X x) (T x) ∂κ := integral_congr_ae
      (heqA.mono fun x hx => congrArg (fun v => inner ℝ (X x) v) hx)
    _ = _ := by
      simpa only [T, inner_smul_right] using
        (setIntegral_toReal_rnDeriv_mul hρκ hA
          (f := fun x => inner ℝ (X x) (τ x)))

end LiquidDrop
