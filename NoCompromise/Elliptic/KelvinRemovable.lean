module

public import NoCompromise.Elliptic.KelvinRemovableCutoff

@[expose] public section

/-!
# Kelvin removability

A bounded function satisfying the genuine distributional harmonic equation off
the origin satisfies it across the origin as well. The shrinking cutoff error
vanishes directly in the Laplacian formulation, so no gradient-integrability
hypothesis is needed. Harmonic regularity then yields a smooth representative,
with exact agreement on the punctured domain when the original representative
is continuous there.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Bounded factors preserve the vanishing cutoff error for every measure
bounded above by three-dimensional Lebesgue measure. -/
lemma tendsto_integral_mul_laplacianN_kelvinCutoff_mul
    {μ : Measure (EuclideanSpace ℝ (Fin 3))} (hμ : μ ≤ volume)
    {q φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hq : MemLp q ∞ μ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ x, q x * laplacianN (fun y => kelvinCutoff j y * φ y) x ∂μ)
      atTop (𝓝 0) := by
  have hb (j : ℕ) :
      ‖∫ x, q x * laplacianN (fun y => kelvinCutoff j y * φ y) x ∂μ‖ ≤
        lpNorm q ∞ μ * ∫ x, ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖ := by
    have hj := (kelvinCutoff_contDiff j).mul hφ
    have hcj := (kelvinCutoff_hasCompactSupport j).mul_right (f' := φ)
    have hi : Integrable (laplacianN (fun y => kelvinCutoff j y * φ y)) volume :=
      (continuous_laplacianN (hj.of_le (by simp))).integrable_of_hasCompactSupport
        (hcj.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset _))
    calc
      _ ≤ ∫ x, ‖q x * laplacianN (fun y => kelvinCutoff j y * φ y) x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, lpNorm q ∞ μ * ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖ ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hi.norm.mono_measure hμ).const_mul _)
        filter_upwards [ae_le_lpNorm_exponent_top hq] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ ∫ x, lpNorm q ∞ μ * ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖ :=
        integral_mono_measure hμ (Eventually.of_forall fun _ => mul_nonneg lpNorm_nonneg
          (norm_nonneg _)) (hi.norm.const_mul _)
      _ = _ := integral_const_mul _ _
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using
    (tendsto_integral_norm_laplacianN_kelvinCutoff_mul hφ hcφ).const_mul (lpNorm q ∞ μ)

lemma kelvin_restrict_punctured_eq (U : Set (EuclideanSpace ℝ (Fin 3))) :
    volume.restrict (U \ {0}) = volume.restrict U := by
  apply Measure.restrict_congr_set
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin 3))] with x hx
  change (x ∈ U \ {0}) = (x ∈ U)
  simp only [Set.mem_sdiff, mem_singleton_iff, hx, not_false_eq_true, and_true]

/-- The puncture can be filled in the genuine distributional equation. Only
boundedness and the equation away from the point are assumed. -/
theorem kelvin_removable_distributional
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    {q : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : HasDistributionalLaplacianOn q (fun _ => 0) (U \ {0}))
    (hb : ∃ B : ℝ, ∀ x ∈ U \ {0}, ‖q x‖ ≤ B) :
    HasDistributionalLaplacianOn q (fun _ => 0) U := by
  obtain ⟨B, hB⟩ := hb
  let : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hbU.measure_lt_top⟩
  have hqm : AEStronglyMeasurable q (volume.restrict U) := by
    rw [← kelvin_restrict_punctured_eq U]
    exact h.locallyIntegrable_function.aestronglyMeasurable
  have hqb : ∀ᵐ x ∂volume.restrict U, ‖q x‖ ≤ B := by
    filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin 3)))] with x hx hn
    exact hB x ⟨hx, hn⟩
  have hq := memLp_top_of_bound hqm B hqb
  have hiq : IntegrableOn q U := hq.integrable le_top
  refine ⟨hiq.locallyIntegrableOn, locallyIntegrableOn_const 0, ?_⟩
  intro φ hφ hcφ hsφ
  simp only [zero_mul, integral_zero]
  have hi (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
      IntegrableOn (fun x => q x * laplacianN ψ x) U := by
    simpa only [mul_comm] using (integrable_mul_compact_factor hiq.locallyIntegrableOn
      (continuous_laplacianN (hψ.of_le (by simp)))
      (hcψ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset _))
      ((tsupport_laplacianN_subset ψ).trans hsψ)).integrableOn
  have he (j : ℕ) : (∫ x in U, q x * laplacianN φ x) =
      ∫ x in U, q x * laplacianN (fun y => kelvinCutoff j y * φ y) x := by
    have hj := kelvinCutoff_contDiff j
    have hcP : HasCompactSupport (fun y => kelvinCutoff j y * φ y) := hcφ.mul_left
    have hsP : tsupport (fun y => kelvinCutoff j y * φ y) ⊆ U :=
      tsupport_mul_subset_right.trans hsφ
    have hs : tsupport (fun x => φ x - kelvinCutoff j x * φ x) ⊆ U \ {0} :=
      (kelvin_test_away_zero j).trans (sdiff_subset_sdiff_left hsφ)
    have ht := h.test_eq (fun x => φ x - kelvinCutoff j x * φ x)
      (hφ.sub (hj.mul hφ)) (hcφ.sub hcP) hs
    rw [kelvin_restrict_punctured_eq U] at ht
    simp only [zero_mul, integral_zero] at ht
    change (∫ x in U, q x * laplacianN (φ - fun y => kelvinCutoff j y * φ y) x) = 0 at ht
    rw [sobolevChain_laplacianN_sub (hφ.of_le (by simp)) ((hj.mul hφ).of_le (by simp))] at ht
    simp only [Pi.sub_apply, mul_sub] at ht
    rw [integral_sub (hi φ hφ hcφ hsφ) (hi _ (hj.mul hφ) hcP hsP)] at ht
    exact sub_eq_zero.mp ht
  have ht := tendsto_integral_mul_laplacianN_kelvinCutoff_mul
    (Measure.restrict_le_self (s := U)) hq hφ hcφ
  have hc : Tendsto (fun _ : ℕ => ∫ x in U, q x * laplacianN φ x) atTop (𝓝 0) :=
    ht.congr' (Eventually.of_forall fun j => (he j).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- A bounded weakly harmonic function on a punctured bounded open set has a
single smooth harmonic representative on the entire set. -/
theorem kelvin_removable_ae
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    {q : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : HasDistributionalLaplacianOn q (fun _ => 0) (U \ {0}))
    (hb : ∃ B : ℝ, ∀ x ∈ U \ {0}, ‖q x‖ ≤ B) :
    ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ v =ᵐ[volume.restrict U] q ∧
      (∀ x ∈ U, laplacianN v x = 0) := by
  have hh := kelvin_removable_distributional hU hbU h hb
  obtain ⟨B, hB⟩ := hb
  have hm := hh.locallyIntegrable_function.aestronglyMeasurable
  have hqb : ∀ᵐ x ∂volume.restrict U, ‖q x‖ ≤ B := by
    filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin 3)))] with x hx hn
    exact hB x ⟨hx, hn⟩
  have hq := memLp_top_of_bound hm B hqb
  have hlocal : ∀ x ∈ U, ∃ R > 0, ball x R ⊆ U ∧
      MemLp q 2 (volume.restrict (ball x R)) := by
    intro x hx
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let : IsFiniteMeasure (volume.restrict (ball x R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
    exact ⟨R, hR, hRU, (hq.mono_measure (Measure.restrict_mono hRU le_rfl)).mono_exponent le_top⟩
  obtain ⟨v, hv, he, hz, _⟩ := hh.exists_smooth_mean_value (by norm_num) hU hlocal
  exact ⟨v, hv, he, hz⟩

/-- Kelvin removability for the original continuous representative: the smooth
extension agrees at every point of the punctured domain. -/
theorem kelvin_removable
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    {q : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : HasDistributionalLaplacianOn q (fun _ => 0) (U \ {0}))
    (hc : ContinuousOn q (U \ {0}))
    (hb : ∃ B : ℝ, ∀ x ∈ U \ {0}, ‖q x‖ ≤ B) :
    ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ EqOn v q (U \ {0}) ∧
      (∀ x ∈ U, laplacianN v x = 0) := by
  obtain ⟨v, hv, he, hz⟩ := kelvin_removable_ae hU hbU h hb
  refine ⟨v, hv, ?_, hz⟩
  exact Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset sdiff_subset he)
    (hU.sdiff isClosed_singleton) (hv.continuousOn.mono sdiff_subset) hc

/-- The unit-ball formulation of blueprint `prop:kelvin-removable`. -/
theorem kelvin_removable_unit_ball {q : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : HasDistributionalLaplacianOn q (fun _ => 0) (ball 0 1 \ {0}))
    (hc : ContinuousOn q (ball 0 1 \ {0}))
    (hb : ∃ B : ℝ, ∀ x ∈ ball 0 1 \ {0}, ‖q x‖ ≤ B) :
    ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 1) ∧ EqOn v q (ball 0 1 \ {0}) ∧
      (∀ x ∈ ball 0 1, laplacianN v x = 0) :=
  kelvin_removable isOpen_ball isBounded_ball h hc hb

end LiquidDrop
