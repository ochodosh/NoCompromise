import NoCompromise.Regularity.FixedNormalExcessTests

/-! # Continuity of local normal pairings under uniform test approximation -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
variable {n : ℕ}

lemma integrable_local_normal_pairing
    {U K : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hfin : μ K < ∞)
    (hσ : Measurable σ) (hunit : ∀ᵐ x ∂μ.restrict U, ‖σ x‖ = 1)
    (hX : Continuous X) (hsX : tsupport X ⊆ K) :
    Integrable (fun x => inner ℝ (X x) (σ x)) μ := by
  have hcX : HasCompactSupport X := hK.of_isClosed_subset (isClosed_tsupport X) hsX
  obtain ⟨B, hB⟩ := hcX.exists_bound_of_continuous hX
  apply integrable_of_finite_support_bound hK.measurableSet hfin
    (hX.measurable.inner hσ).aestronglyMeasurable
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsX hh)),
      inner_zero_left]) B
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hunit] with x hx
  exact (norm_inner_le_norm _ _).trans (by simpa only [hx, mul_one] using hB x)

lemma norm_normal_pairing_sub_le
    {U K : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ X Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hfin : μ K < ∞)
    (hσ : Measurable σ) (hunit : ∀ᵐ x ∂μ.restrict U, ‖σ x‖ = 1)
    (hX : Continuous X) (hsX : tsupport X ⊆ K)
    (hY : Continuous Y) (hsY : tsupport Y ⊆ K)
    {ε : ℝ} (hε : ∀ x, ‖X x - Y x‖ ≤ ε) :
    ‖(∫ x, inner ℝ (X x) (σ x) ∂μ) - ∫ x, inner ℝ (Y x) (σ x) ∂μ‖ ≤ ε * μ.real K := by
  rw [← integral_sub (integrable_local_normal_pairing hK hKU hfin hσ hunit hX hsX)
    (integrable_local_normal_pairing hK hKU hfin hσ hunit hY hsY)]
  have he : (∫ x in K, inner ℝ (X x) (σ x) - inner ℝ (Y x) (σ x) ∂μ) =
      ∫ x, inner ℝ (X x) (σ x) - inner ℝ (Y x) (σ x) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsX hh)),
      image_eq_zero_of_notMem_tsupport (fun hh => hx (hsY hh))]
    simp
  rw [← he]
  let : IsFiniteMeasure (μ.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hb : ∀ᵐ x ∂μ.restrict K,
      ‖inner ℝ (X x) (σ x) - inner ℝ (Y x) (σ x)‖ ≤ ε := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hunit] with x hx
    rw [← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans (by simpa only [hx, mul_one] using hε x)
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const hb

end LiquidDrop
