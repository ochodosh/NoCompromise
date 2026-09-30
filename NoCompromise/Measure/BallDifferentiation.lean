module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Differentiation over open Euclidean balls

Mathlib's Besicovitch Vitali family uses closed balls. Bounds on numerator and
denominator measures pass from all inner closed balls to an open ball by monotone
continuity. Applied to the norm-difference density, this transfers the Lebesgue
point property to the full positive-radius open-ball limit. Vector averages then
converge at points in the measure's conull support. The measure is only assumed
locally finite; neither doubling nor null sphere boundaries are required.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace LiquidDrop

variable {α : Type*} [MetricSpace α] [MeasurableSpace α]

/-- Bounds on all inner closed balls pass to an open ball by continuity from below. -/
theorem measure_ball_le_of_closedBall_le (μ ν : Measure α) (x : α) {r : ℝ}
    (hr : 0 < r) {C : ℝ≥0∞}
    (h : ∀ s, 0 < s → s < r → ν (closedBall x s) ≤ C * μ (closedBall x s)) :
    ν (ball x r) ≤ C * μ (ball x r) := by
  obtain ⟨u, hu, hur, hlim⟩ := exists_seq_strictMono_tendsto' hr
  have hm : Monotone (fun n => closedBall x (u n)) :=
    fun i j hij => closedBall_subset_closedBall (hu.monotone hij)
  have heq : (⋃ n, closedBall x (u n)) = ball x r := by
    apply Subset.antisymm
    · refine iUnion_subset fun n => ?_
      exact closedBall_subset_ball (hur n).2
    · intro y hy
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds (mem_ball.mp hy))).exists
      exact mem_iUnion.mpr ⟨n, hn.le⟩
  rw [← heq, hm.measure_iUnion]
  apply iSup_le
  intro n
  exact (h (u n) (hur n).1 (hur n).2).trans
    (mul_le_mul' le_rfl (measure_mono (fun y hy => mem_iUnion.mpr ⟨n, hy⟩)))

/-- A zero closed-ball ratio limit transfers to open balls for an absolutely
continuous numerator, with finite denominator measure on closed balls. -/
theorem tendsto_measure_ball_div_zero_of_closedBall (μ ν : Measure α) (x : α)
    (hν : ν ≪ μ) (hfin : ∀ r, 0 < r → μ (closedBall x r) ≠ ∞)
    (h : Tendsto (fun r => ν (closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => ν (ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (ENNReal.tendsto_nhds_zero.mp h ε hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  apply ENNReal.div_le_of_le_mul
  apply measure_ball_le_of_closedBall_le μ ν x hr.1
  intro s hs hsr
  by_cases hzero : μ (closedBall x s) = 0
  · rw [hν hzero, hzero, mul_zero]
  · exact (ENNReal.div_le_iff hzero (hfin s hs)).mp (hbound ⟨hs, hsr.trans hr.2⟩)

section Euclidean

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]
  (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]

/-- Besicovitch differentiation with the full positive-radius limit over open balls. -/
theorem ae_tendsto_lintegral_enorm_sub_div_ball {f : EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r =>
      (∫⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) / μ (ball x r)) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_lintegral_enorm_sub_div hf] with x hx
  let ν := μ.withDensity (fun y => ‖f y - f x‖ₑ)
  have hc : Tendsto (fun r => ν (closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [ν, withDensity_apply _ measurableSet_closedBall, Function.comp_def] using
      hx.comp (Besicovitch.tendsto_filterAt μ x)
  have ho := tendsto_measure_ball_div_zero_of_closedBall μ ν x
    (withDensity_absolutelyContinuous μ _)
    (fun r _ => (isCompact_closedBall x r).measure_lt_top.ne) hc
  simpa only [ν, withDensity_apply _ measurableSet_ball] using ho

/-- Almost every point is a norm Lebesgue point for open-ball averages, without
any doubling hypothesis on the locally finite measure. -/
theorem ae_tendsto_average_norm_sub_ball {f : EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in ball x r, ‖f y - f x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_tendsto_lintegral_enorm_sub_div_ball μ hf] with x hx
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
  simp only [ENNReal.toReal_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : μ (ball x r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_lt_top.ne
      (measure_mono ball_subset_closedBall)
  have hi : IntegrableOn (fun y => ‖f y - f x‖) (ball x r) μ :=
    ((hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
      |>.sub (integrableOn_const hfin)).norm
  simp only [Function.comp_apply, ENNReal.toReal_div, setAverage_eq, div_eq_inv_mul]
  have heq := ofReal_integral_norm_eq_lintegral_enorm hi
  simp only [Real.norm_of_nonneg (norm_nonneg _), enorm_norm] at heq
  rw [← heq, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  rfl

/-- A measurable field with an almost-everywhere constant norm bound is locally
integrable for every locally finite Euclidean measure. -/
lemma locallyIntegrable_of_ae_norm_le {f : EuclideanSpace ℝ (Fin n) → E} {C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    LocallyIntegrable f μ :=
  (locallyIntegrable_const (μ := μ) C).mono hf
    (hbound.mono fun _ hx => hx.trans (le_abs_self C))

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The vector average converges at almost every point for arbitrary locally finite
Euclidean measures; all averages here use open balls. -/
theorem ae_tendsto_average_ball {f : EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [ae_tendsto_average_norm_sub_ball μ hf, μ.support_mem_ae] with x hx hsupp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hx
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hpos : μ (ball x r) ≠ 0 :=
    ((Measure.mem_support_iff_forall x).mp hsupp _ (ball_mem_nhds x hr)).ne'
  have hfin : μ (ball x r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_lt_top.ne
      (measure_mono ball_subset_closedBall)
  have hi := (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hc : IntegrableOn (fun _ => f x) (ball x r) μ := integrableOn_const hfin
  have heq : (⨍ y in ball x r, f y ∂μ) - f x =
      ⨍ y in ball x r, (f y - f x) ∂μ := by
    rw [show (fun y => f y - f x) = f - (fun _ => f x) from rfl,
      setAverage_sub hi hc, setAverage_const hpos hfin]
  rw [heq, setAverage_eq, setAverage_eq, norm_smul, measureReal_def,
    Real.norm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Simultaneous norm Lebesgue-point and vector-average limits for an a.e. bounded
measurable field, in particular for a unit polar field. -/
theorem ae_ball_differentiation_of_ae_norm_le {f : EuclideanSpace ℝ (Fin n) → E} {C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ,
      Tendsto (fun r => ⨍ y in ball x r, ‖f y - f x‖ ∂μ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  have hi := locallyIntegrable_of_ae_norm_le μ hf hbound
  exact (ae_tendsto_average_norm_sub_ball μ hi).and (ae_tendsto_average_ball μ hi)

end Euclidean

end LiquidDrop
