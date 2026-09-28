import NoCompromise.BV.Basic

/-! # Ambient realization of genuine polar data on an open subdomain -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
variable {n : ℕ}

/-- Extend the outward normal, the negative distributional polar, by zero. -/
def localOutwardNormal (U : Set (EuclideanSpace ℝ (Fin n)))
    (σ : U → EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  Function.extend (Subtype.val : U → EuclideanSpace ℝ (Fin n)) (fun x => -σ x) (fun _ => 0)

@[simp] lemma localOutwardNormal_coe {U : Set (EuclideanSpace ℝ (Fin n))}
    (σ : U → EuclideanSpace ℝ (Fin n)) (x : U) : localOutwardNormal U σ x = -σ x :=
  Subtype.coe_injective.extend_apply _ _ x

lemma measurable_localOutwardNormal {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) {σ : U → EuclideanSpace ℝ (Fin n)} (hσ : Measurable σ) :
    Measurable (localOutwardNormal U σ) :=
  (MeasurableEmbedding.subtype_coe hU).measurable_extend hσ.neg measurable_const

lemma map_subtype_measure_compact_lt_top {U : Set (EuclideanSpace ℝ (Fin n))}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ρ K < ∞ := by
  rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
  have hc : IsCompact ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' K) := by
    rw [Subtype.isCompact_iff]
    simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hKU] using hK
  exact hc.measure_lt_top

lemma IsDistributionalPolarRepresentation.localOutwardNormal_norm
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : Measure U}
    {σ : U → EuclideanSpace ℝ (Fin n)} (hp : IsDistributionalPolarRepresentation f U ρ σ) :
    ∀ᵐ x ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ρ,
      ‖localOutwardNormal U σ x‖ = 1 := by
  rw [(MeasurableEmbedding.subtype_coe hU).ae_map_iff]
  simpa only [localOutwardNormal_coe, norm_neg] using hp.norm_ae

/-- The true local derivative identity becomes the outward normal pairing
against supported ambient fields, with its sign proved explicitly. -/
lemma IsDistributionalPolarRepresentation.localOutwardNormal_pairing
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ]
    {σ : U → EuclideanSpace ℝ (Fin n)} (hp : IsDistributionalPolarRepresentation f U ρ σ)
    (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    (∫ x, f x * divergenceN X x) =
      ∫ x, inner ℝ (X x) (localOutwardNormal U σ x)
        ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ρ := by
  rw [(MeasurableEmbedding.subtype_coe hU).integral_map]
  simp only [localOutwardNormal_coe, inner_neg_right, integral_neg]
  have hp' := congrArg Neg.neg (hp.integral_divergence_eq hf hX hcX hsX)
  rw [neg_neg] at hp'
  rw [← hp']
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [divergenceN_eq_zero_of_notMem_tsupport (fun hh => hx (hsX hh)), mul_zero]

end LiquidDrop
