import NoCompromise.BV.Basic
import Mathlib.Topology.UrysohnsLemma

/-! # Compact smooth approximation and local mass bounds for excess limits -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal CompactlySupported Convolution
namespace LiquidDrop

/-- Compact continuous vector fields admit uniform C¹ approximants, all
supported in one compact subset of the same open region. -/
theorem exists_smooth_field_approximation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      ∃ Y : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        IsCompact K ∧ K ⊆ U ∧ tsupport X ⊆ K ∧
        (∀ j, ContDiff ℝ 1 (Y j) ∧ HasCompactSupport (Y j) ∧ tsupport (Y j) ⊆ K) ∧
        TendstoUniformly Y X atTop := by
  obtain ⟨δ, hδ, hδU⟩ := hcX.exists_cthickening_subset_open hU hsX
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j : ℕ) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let Y := fun j => mollifyTestField (φ j) X
  have hsY (j : ℕ) := mollifyTestField_support (X := X) (φ j) (hφδ j)
  refine ⟨cthickening δ (tsupport X), Y, hcX.cthickening, hδU,
    self_subset_cthickening _, ?_, ?_⟩
  · intro j
    exact ⟨(mollifyTestField_contDiff _ hX).of_le (by simp),
      (φ j).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcX, hsY j⟩
  · exact tendstoUniformly_mollifyTestField hφlim (hcX.uniformContinuous_of_continuous hX)

/-- A compactly supported measurable function is integrable whenever its
support has finite measure and it has a finite uniform bound. -/
lemma integrable_of_finite_support_bound {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {K : Set α}
    (hK : MeasurableSet K) (hfin : μ K < ∞) (hm : AEStronglyMeasurable f μ)
    (hs : ∀ x ∉ K, f x = 0) (B : ℝ) (hb : ∀ᵐ x ∂μ.restrict K, ‖f x‖ ≤ B) :
    Integrable f μ := by
  have he : K.indicator f = f := by
    ext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx, hs x hx]
  rw [← he, integrable_indicator_iff hK]
  let : IsFiniteMeasure (μ.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  exact (integrable_const B).mono' hm.restrict hb

/-- Local vague convergence of positive measures bounds every compact mass
eventually; no extra uniform-mass hypothesis is imposed. -/
theorem eventually_compact_mass_bound_of_test_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure (EuclideanSpace ℝ (Fin n))) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hfin : ∀ j K, IsCompact K → K ⊆ U → μs j K < ∞)
    (ht : ∀ φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      tsupport φ ⊆ U →
      Tendsto (fun j => ∫ x, φ x ∂μs j) atTop (𝓝 (∫ x, φ x ∂μ)))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop, (μs j).real K ≤ C := by
  obtain ⟨φ, heq, hc, hs, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let Φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ := ⟨φ, hc⟩
  let C := |∫ x, φ x ∂μ| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlt : (∫ x, φ x ∂μ) < C := by
    dsimp [C]
    linarith [le_abs_self (∫ x, φ x ∂μ)]
  filter_upwards [(ht Φ hs).eventually (gt_mem_nhds hlt)] with j hj
  have hi : Integrable φ (μs j) := by
    apply integrable_of_finite_support_bound hc.measurableSet (hfin j _ hc hs)
      φ.continuous.aestronglyMeasurable
      (fun x hx => image_eq_zero_of_notMem_tsupport hx) 1
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact (hb x).2)
  have hmass : (μs j).real K ≤ ∫ x, φ x ∂μs j := by
    calc
      _ = ∫ x in K, φ x ∂μs j := by
        rw [setIntegral_congr_fun hK.measurableSet (fun x hx => heq hx)]
        simp
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall (fun x => (hb x).1))
  exact hmass.trans hj.le

end LiquidDrop
