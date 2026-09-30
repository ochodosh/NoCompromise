module

public import NoCompromise.Measure.WeakStar

@[expose] public section

/-!
# Positive local weak-star limits

Uniform compact-set bounds give a subsequential limit of positive test
functionals. Positivity passes to the limit, so positive Riesz representation
produces one regular locally finite measure, without signed-measure conversion.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported
namespace LiquidDrop

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Positive, uniformly locally bounded functionals admit a positive Riesz subsequential limit. -/
theorem exists_subseq_positive_riesz
    (L : ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ) (hL : IsUniformlyLocallyBounded L)
    (hpos : ∀ j (f : C_c(X, ℝ)), 0 ≤ f → 0 ≤ L j f) :
    ∃ (μ : Measure X) (σ : ℕ → ℕ), StrictMono σ ∧ μ.Regular ∧
      IsFiniteMeasureOnCompacts μ ∧ ∀ f : C_c(X, ℝ),
        Tendsto (fun j => L (σ j) f) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨Λ, σ, hσ, _, ht⟩ := exists_subseq_locallyBoundedFunctional L hL
  let Λp := PositiveLinearMap.mk₀ Λ (by
    intro f hf
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (ht f)
      (Eventually.of_forall fun j => hpos (σ j) f hf))
  refine ⟨RealRMK.rieszMeasure Λp, σ, hσ, inferInstance, inferInstance, ?_⟩
  intro f
  rw [RealRMK.integral_rieszMeasure]
  exact ht f

/-- Uniform bounds on each compact set give weak-star compactness for positive measures. -/
theorem exists_subseq_positive_measure (μ : ℕ → Measure X)
    [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hμ : ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ j, (μ j K).toReal ≤ C) :
    ∃ (ν : Measure X) (σ : ℕ → ℕ), StrictMono σ ∧ ν.Regular ∧
      IsFiniteMeasureOnCompacts ν ∧ ∀ f : C_c(X, ℝ),
        Tendsto (fun j => ∫ x, f x ∂μ (σ j)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply exists_subseq_positive_riesz
    (fun j => (CompactlySupportedContinuousMap.integralPositiveLinearMap (μ j)).toLinearMap)
  · intro K hK
    obtain ⟨C, hC, hb⟩ := hμ K hK
    refine ⟨C, hC, fun j f hf => ?_⟩
    change |∫ x, f x ∂μ j| ≤ C * ‖f.toBoundedContinuousFunction‖
    rw [← Real.norm_eq_abs]
    exact (norm_integral_compactlySupported_le (μ j) f hK hf).trans
      (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg _))
  · intro j f hf
    exact integral_nonneg (fun x => hf x)

/-- It is enough that each compact-set mass bound holds eventually along the sequence. -/
theorem exists_subseq_positive_measure_of_eventually (μ : ℕ → Measure X)
    [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hμ : ∀ K : Set X, IsCompact K →
      ∃ C : ℝ, ∀ᶠ j in atTop, (μ j K).toReal ≤ C) :
    ∃ (ν : Measure X) (σ : ℕ → ℕ), StrictMono σ ∧ ν.Regular ∧
      IsFiniteMeasureOnCompacts ν ∧ ∀ f : C_c(X, ℝ),
        Tendsto (fun j => ∫ x, f x ∂μ (σ j)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply exists_subseq_positive_measure μ
  intro K hK
  obtain ⟨C, hC⟩ := hμ K hK
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun j => (μ j K).toReal) := ⟨C, hC⟩
  obtain ⟨D, hD⟩ := hb.bddAbove_range
  exact ⟨max D 0, le_max_right _ _, fun j => (hD (mem_range_self j)).trans (le_max_left _ _)⟩

end LiquidDrop
