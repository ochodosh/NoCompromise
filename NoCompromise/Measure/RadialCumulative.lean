import NoCompromise.Measure.CumulativeDerivative

/-!
# Scalar radial cumulative integrals

Scalar integrals over balls are measurable and locally integrable in their
radius. At a non-atomic center they tend to zero. A direct interval estimate
then gives the vanishing one-sided mean needed to fix a distributional constant.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma measurable_integral_ball_real {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    (c : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun r : ℝ => ∫ x in ball c r, f x ∂μ) := by
  have hS : MeasurableSet {z : ℝ × EuclideanSpace ℝ (Fin n) | dist z.2 c < z.1} :=
    measurableSet_lt (by fun_prop) measurable_fst
  have hj := ((hf.comp measurable_snd).indicator hS).stronglyMeasurable.integral_prod_right'
    (ν := μ)
  have heq (r : ℝ) : (∫ y, {z : ℝ × EuclideanSpace ℝ (Fin n) | dist z.2 c < z.1}.indicator
      (f ∘ Prod.snd) (r, y) ∂μ) = ∫ y in ball c r, f y ∂μ := by
    change (∫ y, (ball c r).indicator f y ∂μ) = _
    rw [integral_indicator measurableSet_ball]
  simpa only [heq] using hj.measurable

lemma locallyIntegrable_integral_ball_real {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hi : LocallyIntegrable f μ)
    (c : EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrable (fun r : ℝ => ∫ x in ball c r, f x ∂μ) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hic : IntegrableOn f (closedBall c R) μ :=
    hi.integrableOn_isCompact (isCompact_closedBall _ _)
  have hb (r : ℝ) (hr : r ∈ K) : ‖∫ x in ball c r, f x ∂μ‖ ≤
      ∫ x in closedBall c R, ‖f x‖ ∂μ := by
    apply (norm_integral_le_integral_norm _).trans
    apply setIntegral_mono_set hic.norm (Eventually.of_forall fun _ => norm_nonneg _)
    have hr' : r ≤ R := (le_abs_self r).trans (by simpa [Real.dist_eq] using hR hr)
    exact ae_of_all _ (fun x hx =>
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hr')) hx)
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  apply Integrable.mono' (integrable_const (∫ x in closedBall c R, ‖f x‖ ∂μ))
    (measurable_integral_ball_real μ hf c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with r hr
  exact hb r hr

lemma tendsto_integral_ball_real_zero {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hi : LocallyIntegrable f μ)
    (c : EuclideanSpace ℝ (Fin n)) (hc : μ {c} = 0) :
    Tendsto (fun r : ℝ => ∫ x in ball c r, f x ∂μ) (𝓝 0) (𝓝 0) := by
  let v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 1) :=
    fun x => euclideanOneReal.symm (f x)
  have hvm : Measurable v := euclideanOneReal.symm.continuous.measurable.comp hf
  have hvi : LocallyIntegrable v μ := hi.mono hvm.aestronglyMeasurable
    (Eventually.of_forall fun x => (euclideanOneReal.symm.norm_map (f x)).le)
  have ht := tendsto_integral_ball_zero μ hvm hvi c hc
  have hte := euclideanOneReal.continuous.continuousAt.tendsto.comp ht
  have heq (r : ℝ) : euclideanOneReal (∫ x in ball c r, v x ∂μ) =
      ∫ x in ball c r, f x ∂μ := by
    have he := euclideanOneReal.toLinearIsometry.integral_comp_comm
      (μ := μ.restrict (ball c r)) v
    change (∫ x in ball c r, euclideanOneReal (v x) ∂μ) =
      euclideanOneReal (∫ x in ball c r, v x ∂μ) at he
    simpa only [v, euclideanOneReal.apply_symm_apply] using he.symm
  simpa only [Function.comp_def, heq, euclideanOneReal.map_zero] using hte

/-- A function tending to zero along positive radii has vanishing one-sided means. -/
lemma tendsto_mean_Ioo_zero_of_tendsto_zero {f : ℝ → ℝ}
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo 0 r, f t) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr hdr => ?_⟩
  have hrp : 0 < r := hr
  have hrδ : r < δ := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hrp] using hdr
  have hb : ∀ᵐ t ∂volume.restrict (Ioo 0 r), ‖f t‖ ≤ ε / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h := hbound ht.1 (by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht.1] using ht.2.trans hrδ)
    simpa only [dist_zero_right] using h.le
  have hI := norm_integral_le_of_norm_le_const hb
  have hI' : ‖∫ t in Ioo 0 r, f t‖ ≤ ε / 2 * r := by
    simpa only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal hrp.le] using hI
  rw [dist_zero_right, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hrp.le)]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hI' (inv_nonneg.mpr hrp.le))
  have heq : r⁻¹ * (ε / 2 * r) = ε / 2 := by field_simp
  rw [heq]
  linarith

end LiquidDrop
