import NoCompromise.Regularity.FixedNormalExcessLocalPolar
import NoCompromise.Regularity.FixedNormalExcessContinuous

/-! # Genuine local L¹ convergence implies convergence of normal pairings -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
variable {n : ℕ}

theorem tendsto_localOutwardNormal_pairing_of_locally_l1
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (ρs : ℕ → Measure U) (ρ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (ρs j)] [IsFiniteMeasureOnCompacts ρ]
    (σs : ℕ → U → EuclideanSpace ℝ (Fin n)) (σ : U → EuclideanSpace ℝ (Fin n))
    (hps : ∀ j, IsDistributionalPolarRepresentation (f j) U (ρs j) (σs j))
    (hp : IsDistributionalPolarRepresentation g U ρ σ)
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    Tendsto (fun j => ∫ x, inner ℝ (X x) (localOutwardNormal U (σs j) x)
      ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) (ρs j)) atTop
      (𝓝 (∫ x, inner ℝ (X x) (localOutwardNormal U σ x)
        ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ρ)) := by
  simp_rw [← IsDistributionalPolarRepresentation.localOutwardNormal_pairing
    hU.measurableSet (hps _) (hf _) hX hcX hsX,
    ← hp.localOutwardNormal_pairing hU.measurableSet hg hX hcX hsX]
  have hsupport (u : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x in tsupport X, u x * divergenceN X x) = ∫ x, u x * divergenceN X x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport hx, mul_zero]
  have ht := tendsto_integral_mul_of_l1_on_compact hcX
    (fun j => (hf j).integrableOn_compact_subset hsX hcX)
    (hg.integrableOn_compact_subset hsX hcX)
    (continuous_divergenceN hX).continuousOn (hconv _ hcX hsX)
  simpa only [hsupport] using ht

/-- Actual scalar L¹ convergence and convergence of the positive variation measures
give all continuous normal pairings. No vector-measure convergence is a premise. -/
theorem tendsto_localOutwardNormal_continuous_pairing
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (ρs : ℕ → Measure U) (ρ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (ρs j)] [IsFiniteMeasureOnCompacts ρ]
    (σs : ℕ → U → EuclideanSpace ℝ (Fin n)) (σ : U → EuclideanSpace ℝ (Fin n))
    (hps : ∀ j, IsDistributionalPolarRepresentation (f j) U (ρs j) (σs j))
    (hp : IsDistributionalPolarRepresentation g U ρ σ)
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0))
    (hμ : ∀ φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      tsupport φ ⊆ U →
      Tendsto (fun j => ∫ x, φ x ∂Measure.map (Subtype.val : U → _) (ρs j)) atTop
        (𝓝 (∫ x, φ x ∂Measure.map (Subtype.val : U → _) ρ)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    Tendsto (fun j => ∫ x, inner ℝ (X x) (localOutwardNormal U (σs j) x)
      ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) (ρs j)) atTop
      (𝓝 (∫ x, inner ℝ (X x) (localOutwardNormal U σ x)
        ∂Measure.map (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ρ)) := by
  apply tendsto_normal_pairing_of_smooth_tests hU
    (fun j => Measure.map (Subtype.val : U → _) (ρs j))
    (Measure.map (Subtype.val : U → _) ρ)
    (fun j => localOutwardNormal U (σs j)) (localOutwardNormal U σ)
    (fun _ _ hK hKU => map_subtype_measure_compact_lt_top hK hKU)
    (fun _ hK hKU => map_subtype_measure_compact_lt_top hK hKU)
    (fun j => measurable_localOutwardNormal hU.measurableSet (hps j).measurable)
    (measurable_localOutwardNormal hU.measurableSet hp.measurable)
    (fun j => ae_restrict_of_ae ((hps j).localOutwardNormal_norm hU.measurableSet))
    (ae_restrict_of_ae (hp.localOutwardNormal_norm hU.measurableSet)) hμ
    (fun Y hY hcY hsY => tendsto_localOutwardNormal_pairing_of_locally_l1
      hU ρs ρ σs σ hps hp hf hg hconv hY hcY hsY) hX hcX hsX

end LiquidDrop
