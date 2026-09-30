module

public import NoCompromise.Regularity.PerimeterConvergenceVague
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-! # Upper bounds on precompact continuity sets under local weak convergence -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Compact cutoffs reduce local weak convergence to the finite-measure
Portmanteau upper bound on each compact subset of the open domain. -/
theorem limsup_local_compact_le_of_compact_test_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure U) (μ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (μs j)] [IsFiniteMeasureOnCompacts μ]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z, φ z ∂μs j) atTop (𝓝 (∫ z, φ z ∂μ)))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    limsup (fun j => μs j (Subtype.val ⁻¹' K)) atTop ≤ μ (Subtype.val ⁻¹' K) := by
  obtain ⟨ψ, hψK, hcψ, hsψ, hbψ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let Ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨ψ, hcψ⟩
  let φ : C_c(U, ℝ) := restrictSupportedCC ⟨Ψ, hsψ⟩
  have hn (z : U) : 0 ≤ φ z := (hbψ z).1
  let : ∀ j, IsFiniteMeasure (cutoffAmbientMeasure (μs j) φ) :=
    fun j => finite_cutoffAmbientMeasure (μs j) φ hn
  let : IsFiniteMeasure (cutoffAmbientMeasure μ φ) := finite_cutoffAmbientMeasure μ φ hn
  let νs : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin n)) :=
    fun j => ⟨cutoffAmbientMeasure (μs j) φ, inferInstance⟩
  let ν : FiniteMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨cutoffAmbientMeasure μ φ, inferInstance⟩
  have ht : Tendsto νs atTop (𝓝 ν) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    let g : C_c(U, ℝ) :=
      ⟨⟨fun z => φ z * f z,
        φ.continuous.mul (f.continuous.comp continuous_subtype_val)⟩,
        φ.hasCompactSupport.mul_right⟩
    change Tendsto (fun j => ∫ z, f z ∂cutoffAmbientMeasure (μs j) φ) atTop
      (𝓝 (∫ z, f z ∂cutoffAmbientMeasure μ φ))
    have hm : Measurable (fun z => f z) := f.continuous.measurable
    simp only [integral_cutoffAmbientMeasure _ φ hn hm]
    exact hweak g
  have h := FiniteMeasure.limsup_measure_closed_le_of_tendsto ht hK.isClosed
  change limsup (fun j => cutoffAmbientMeasure (μs j) φ K) atTop ≤
    cutoffAmbientMeasure μ φ K at h
  have hφ : ∀ z : U, (z : EuclideanSpace ℝ (Fin n)) ∈ K → φ z = 1 :=
    fun z hz => hψK hz
  simpa only [cutoffAmbientMeasure_apply_of_one _ φ hK.measurableSet hφ] using h

/-- The upper bound applies to any precompact set with null ambient boundary. -/
theorem limsup_local_set_le_of_compact_test_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure U) (μ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (μs j)] [IsFiniteMeasureOnCompacts μ]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z, φ z ∂μs j) atTop (𝓝 (∫ z, φ z ∂μ)))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hcA : IsCompact (closure A))
    (hAU : closure A ⊆ U) (hnull : μ (Subtype.val ⁻¹' frontier A) = 0) :
    limsup (fun j => μs j (Subtype.val ⁻¹' A)) atTop ≤ μ (Subtype.val ⁻¹' A) := by
  have heq : μ (Subtype.val ⁻¹' closure A) = μ (Subtype.val ⁻¹' A) := by
    apply le_antisymm
    · rw [closure_eq_self_union_frontier, preimage_union]
      exact (measure_union_le _ _).trans (by rw [hnull, add_zero])
    · exact measure_mono (preimage_mono subset_closure)
  exact ((limsup_le_limsup (Eventually.of_forall fun j =>
    measure_mono (μ := μs j) (preimage_mono subset_closure))).trans
      (limsup_local_compact_le_of_compact_test_convergence hU μs μ hweak hcA hAU)).trans_eq heq

end LiquidDrop
