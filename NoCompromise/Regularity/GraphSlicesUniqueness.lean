module

public import NoCompromise.BV.ScalarDistributionUniqueness

@[expose] public section

/-! # Localization of scalar measure pairings from genuine compact C1 tests -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Scalar compact-test equality determines all restricted weighted integrals.
This uses actual locally integrable densities under sigma-finite measures. -/
theorem setIntegral_mul_eq_of_scalar_pairings {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin (n + 1)))} [SigmaFinite μ] [SigmaFinite ρ]
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g ρ)
    (hpair : ∀ (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ),
      ContDiff ℝ 1 φ → tsupport φ ⊆ U →
        (∫ x, φ x * f x ∂μ) = ∫ x, φ x * g x ∂ρ)
    {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : MeasurableSet A) (hAU : A ⊆ U)
    (q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    (∫ x in A, q x * f x ∂μ) = ∫ x in A, q x * g x ∂ρ := by
  let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hLf : LocallyIntegrable (fun x => f x • v) μ :=
    locallyIntegrableOn_univ.mp (L.locallyIntegrableOn_comp (hf.locallyIntegrableOn univ))
  have hLg : LocallyIntegrable (fun x => g x • v) ρ :=
    locallyIntegrableOn_univ.mp (L.locallyIntegrableOn_comp (hg.locallyIntegrableOn univ))
  have he := setIntegral_inner_eq_of_coordinate_pairings hU hLf hLg
    (fun i φ hφ hsφ => by
      simp only [PiLp.smul_apply, smul_eq_mul]
      simp_rw [← mul_assoc]
      rw [integral_mul_const, integral_mul_const, hpair φ hφ hsφ]) hA hAU
    (fun x => q x • v)
  have hv : inner ℝ v v = 1 := by simp [v]
  simpa only [inner_smul_left, inner_smul_right, hv, mul_one, starRingEnd_apply, star_trivial,
    mul_comm] using he

end LiquidDrop
