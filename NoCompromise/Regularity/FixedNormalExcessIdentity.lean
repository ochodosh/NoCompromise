module

public import NoCompromise.Regularity.FixedNormalExcessPairing

@[expose] public section

/-! # The exact quadratic identity for unit-normal excess -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
variable {n : ℕ}

lemma integrable_compact_test_of_local_mass
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hfin : μ (tsupport φ) < ∞) : Integrable φ μ := by
  obtain ⟨B, hB⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  apply integrable_of_finite_support_bound (isClosed_tsupport φ).measurableSet hfin
    φ.continuous.aestronglyMeasurable (fun x hx => image_eq_zero_of_notMem_tsupport hx) B
  exact ae_of_all _ hB

/-- The normal is required to be unit only on the open domain containing the test.
In particular the ambient extension need not be a unit field off that domain. -/
theorem integral_fixed_normal_excess_identity
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : Measurable σ) (hunit : ∀ᵐ x ∂μ.restrict U, ‖σ x‖ = 1)
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ‖ν‖ = 1)
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hsφ : tsupport φ ⊆ U) (hfin : μ (tsupport φ) < ∞) :
    (∫ x, φ x * ‖σ x - ν‖ ^ 2 ∂μ) =
      2 * (∫ x, φ x ∂μ) - 2 * ∫ x, inner ℝ (φ x • ν) (σ x) ∂μ := by
  have hi := integrable_compact_test_of_local_mass φ hfin
  have hp : Integrable (fun x => inner ℝ (φ x • ν) (σ x)) μ :=
    integrable_local_normal_pairing φ.hasCompactSupport hsφ hfin hσ hunit
      (φ.continuous.smul continuous_const) (tsupport_smul_subset_left _ _)
  have he : (fun x => φ x * ‖σ x - ν‖ ^ 2) =ᵐ[μ]
      (fun x => 2 * φ x - 2 * inner ℝ (φ x • ν) (σ x)) := by
    filter_upwards [(ae_restrict_iff' hU).mp hunit] with x hx
    by_cases hxu : x ∈ U
    · rw [norm_sub_sq_real, hx hxu, hν, inner_smul_left, real_inner_comm (σ x) ν]
      simp only [one_pow, RCLike.conj_to_real]
      ring
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hxu (hsφ hh))
      simp [hz]
  rw [integral_congr_ae he, integral_sub (hi.const_mul 2) (hp.const_mul 2),
    integral_const_mul, integral_const_mul]

end LiquidDrop
