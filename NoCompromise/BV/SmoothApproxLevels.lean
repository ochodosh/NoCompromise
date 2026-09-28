import NoCompromise.BV.Coarea
import NoCompromise.BV.AnnularGluingDiagonal
import NoCompromise.Sard.ThreeDimensional

/-!
# Choosing regular superlevels for smooth set approximation

Interior levels of any real-valued approximation to an indicator have a
uniform L¹ error bound. BV coarea and the scalar Sard theorem then select
regular levels with the required perimeter bound.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma mul_norm_superlevelIndicator_sub_indicator_le {α : Type*}
    (E : Set α) (u : α → ℝ) (x : α) {a t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ 1 - a) :
    a * ‖superlevelIndicator u t x - E.indicator (fun _ => (1 : ℝ)) x‖ ≤
      ‖u x - E.indicator (fun _ => (1 : ℝ)) x‖ := by
  classical
  by_cases hx : x ∈ E
  · by_cases hu : t < u x
    · simp [superlevelIndicator_apply, hx, hu]
    · simp only [superlevelIndicator_apply, hu, ite_false, indicator_of_mem hx,
        zero_sub, norm_neg, norm_one, mul_one]
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [le_of_not_gt hu] : u x - 1 ≤ 0)]
      linarith [le_of_not_gt hu]
  · by_cases hu : t < u x
    · simp only [superlevelIndicator_apply, hu, ite_true, indicator_of_notMem hx,
        sub_zero, norm_one, mul_one]
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u x)]
      linarith
    · simp [superlevelIndicator_apply, hx, hu]

lemma eLpNorm_superlevelIndicator_sub_indicator_le {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hvE : volume E < ∞)
    {u : AmbientSpace → ℝ} (hu : Continuous u) (hiu : Integrable u)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ 1 - a) :
    eLpNorm (superlevelIndicator u t - E.indicator (fun _ => (1 : ℝ))) 1 volume ≤
      ENNReal.ofReal (a⁻¹ * ∫ x, ‖u x - E.indicator (fun _ => (1 : ℝ)) x‖) := by
  have hiE : Integrable (E.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvE.ne).integrable_indicator₀ hmE
  have hm : AEStronglyMeasurable
      (superlevelIndicator u t - E.indicator (fun _ => (1 : ℝ))) volume := by
    apply AEStronglyMeasurable.sub _ hiE.aestronglyMeasurable
    exact (measurable_const.indicator
      (isOpen_lt continuous_const hu).measurableSet).aestronglyMeasurable
  have hp (x : AmbientSpace) :
      ‖superlevelIndicator u t x - E.indicator (fun _ => (1 : ℝ)) x‖ ≤
        a⁻¹ * ‖u x - E.indicator (fun _ => (1 : ℝ)) x‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ ha).mpr (by
      simpa only [mul_comm] using mul_norm_superlevelIndicator_sub_indicator_le E u x ha hat hta)
  have hid : Integrable (superlevelIndicator u t - E.indicator (fun _ => (1 : ℝ))) :=
    ((hiu.sub hiE).norm.const_mul a⁻¹).mono' hm (Eventually.of_forall hp)
  rw [eLpNorm_one_eq_lintegral_enorm hid.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hid]
  apply ENNReal.ofReal_le_ofReal
  have hb := integral_mono hid.norm ((hiu.sub hiE).norm.const_mul a⁻¹) hp
  simpa only [integral_const_mul, Pi.sub_apply] using hb

/-- The first moment of superlevel perimeter may be realized at a regular
value, since the exceptional critical values have zero Lebesgue measure. -/
theorem exists_regular_level_perimeter_le {u : AmbientSpace → ℝ}
    (hu : ContDiff ℝ 3 u) (hi : Integrable (gradient u))
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b,
      (∀ x : AmbientSpace, u x = t → gradient u x ≠ 0) ∧
      perimeter {x | t < u x} ≤
        ENNReal.ofReal (∫ x, ‖gradient u x‖) / ENNReal.ofReal (b - a) := by
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  have hμ : μ ≠ 0 := by
    intro hz
    have hh : μ univ = 0 := by simp only [hz, Measure.coe_zero, Pi.zero_apply]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' (by
      simpa only [μ, Measure.restrict_apply_univ, Real.volume_Ioo] using hh)
  have hreg : ∀ᵐ t ∂μ, t ∈ Ioo a b ∧
      ∀ x : AmbientSpace, u x = t → gradient u x ≠ 0 := by
    have hh := ae_restrict_of_ae (s := Ioo a b) (ae_regular_values_c3 isOpen_univ hu.contDiffOn)
    exact (ae_restrict_mem measurableSet_Ioo).and (hh.mono fun t ht x hx => ht x (mem_univ x) hx)
  have hloc : LocallyIntegrableOn u univ := hu.continuous.locallyIntegrable.locallyIntegrableOn _
  obtain ⟨t, ht, hb⟩ := exists_notMem_null_le_laverage hμ
    ((measurable_perimeter_superlevel hloc).aemeasurable (μ := μ)) (ae_iff.mp hreg)
  have ht' : t ∈ Ioo a b ∧ ∀ x : AmbientSpace, u x = t → gradient u x ≠ 0 := by
    simpa only [mem_ofPred_eq, not_not] using ht
  refine ⟨t, ht'.1, ht'.2, ?_⟩
  have hmeas : NullMeasurableSet {x | t < u x} volume :=
    (isOpen_lt continuous_const hu.continuous).measurableSet.nullMeasurableSet
  rw [← perimeterN_eq_perimeter _ hmeas]
  change perimeterIn {x | t < u x} univ ≤ _
  apply hb.trans
  rw [laverage_eq, Measure.restrict_apply_univ, Real.volume_Ioo]
  apply ENNReal.div_le_div_right
  apply (setLIntegral_le_lintegral (s := Ioo a b) _).trans
  rw [lintegral_perimeter_superlevel_eq_lintegral_norm_gradient isOpen_univ
    (hu.of_le (by norm_num)).contDiffOn, Measure.restrict_univ]
  simpa only [← ofReal_norm] using (ofReal_integral_norm_eq_lintegral_enorm hi).ge

end LiquidDrop
