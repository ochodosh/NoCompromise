import NoCompromise.Regularity.FixedNormalExcessDistribution
import NoCompromise.Regularity.FixedNormalExcessIdentity

/-! # Fixed-normal excess under strict perimeter convergence

The theorem uses genuine local polar representations on the open subtype.
Thus it imposes no perimeter assumption outside the domain, and distributional
normal convergence is derived from the actual local L¹ convergence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
variable {n : ℕ}

/-- Local BV functions with a fixed outward polar in the limit satisfy the
quadratic normal convergence for every compact continuous test, including
signed tests. The indicator specialization is the blueprint lemma. -/
theorem fixed_normal_excess_convergence_of_local_polar
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
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ‖ν‖ = 1)
    (hnormal : ∀ᵐ x ∂ρ, -σ x = ν)
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hsφ : tsupport φ ⊆ U) :
    Tendsto (fun j => ∫ x : U, φ x * ‖-σs j x - ν‖ ^ 2 ∂ρs j) atTop (𝓝 0) := by
  have hX : Continuous (fun x => φ x • ν) := φ.continuous.smul continuous_const
  have hsX : tsupport (fun x => φ x • ν) ⊆ tsupport φ := tsupport_smul_subset_left _ _
  have hcX : HasCompactSupport (fun x => φ x • ν) :=
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hsX
  have ht := tendsto_localOutwardNormal_continuous_pairing hU ρs ρ σs σ
    hps hp hf hg hconv hμ hX hcX (hsX.trans hsφ)
  have hn : (∫ x, inner ℝ (φ x • ν) (localOutwardNormal U σ x)
      ∂Measure.map (Subtype.val : U → _) ρ) =
      ∫ x, φ x ∂Measure.map (Subtype.val : U → _) ρ := by
    rw [(MeasurableEmbedding.subtype_coe hU.measurableSet).integral_map,
      (MeasurableEmbedding.subtype_coe hU.measurableSet).integral_map]
    apply integral_congr_ae
    filter_upwards [hnormal] with x hx
    rw [localOutwardNormal_coe, hx, inner_smul_left, real_inner_self_eq_norm_sq, hν]
    simp
  rw [hn] at ht
  have ht' := ((hμ φ hsφ).const_mul 2).sub (ht.const_mul 2)
  simp only [sub_self] at ht'
  convert ht' using 1
  ext j
  rw [← integral_fixed_normal_excess_identity hU.measurableSet
    (measurable_localOutwardNormal hU.measurableSet (hps j).measurable)
    (ae_restrict_of_ae ((hps j).localOutwardNormal_norm hU.measurableSet)) hν φ hsφ
    (map_subtype_measure_compact_lt_top φ.hasCompactSupport hsφ)]
  rw [(MeasurableEmbedding.subtype_coe hU.measurableSet).integral_map]
  simp only [localOutwardNormal_coe]

/-- Blueprint `lem:fixed-normal-excess-convergence`, with the actual local
indicator polar measures and outward normals. The support condition is the
ambient realization of C_c(U). Nonnegativity is unnecessary for this stronger
signed-test conclusion. -/
theorem fixed_normal_excess_convergence
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (E : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : Set (EuclideanSpace ℝ (Fin n)))
    (ρs : ℕ → Measure U) (ρ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (ρs j)] [IsFiniteMeasureOnCompacts ρ]
    (σs : ℕ → U → EuclideanSpace ℝ (Fin n)) (σ : U → EuclideanSpace ℝ (Fin n))
    (hps : ∀ j, IsDistributionalPolarRepresentation
      ((E j).indicator (fun _ => (1 : ℝ))) U (ρs j) (σs j))
    (hp : IsDistributionalPolarRepresentation (F.indicator (fun _ => (1 : ℝ))) U ρ σ)
    (hf : ∀ j, LocallyIntegrableOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hg : LocallyIntegrableOn (F.indicator (fun _ => (1 : ℝ))) U)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0))
    (hμ : ∀ φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      tsupport φ ⊆ U →
      Tendsto (fun j => ∫ x, φ x ∂Measure.map (Subtype.val : U → _) (ρs j)) atTop
        (𝓝 (∫ x, φ x ∂Measure.map (Subtype.val : U → _) ρ)))
    {ν : EuclideanSpace ℝ (Fin n)} (hν : ‖ν‖ = 1)
    (hnormal : ∀ᵐ x ∂ρ, -σ x = ν)
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hsφ : tsupport φ ⊆ U) :
    Tendsto (fun j => ∫ x : U, φ x * ‖-σs j x - ν‖ ^ 2 ∂ρs j) atTop (𝓝 0) :=
  fixed_normal_excess_convergence_of_local_polar hU ρs ρ σs σ hps hp hf hg hconv hμ
    hν hnormal φ hsφ

end LiquidDrop
