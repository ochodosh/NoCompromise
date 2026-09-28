import NoCompromise.BV.StrictApprox
import NoCompromise.BV.AnnularGluingCoarea
import NoCompromise.Energy.Scaling
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Strong L¹ continuity of dilations

Compact continuous functions are handled by dominated convergence with one
fixed compact support bound. Density and the exact Haar scaling factor then
give the result for arbitrary L¹ functions. This is the continuity needed by
exact-volume correction of varying approximating sets.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_integral_norm_dilate_sub_of_compact {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {g : EuclideanSpace ℝ (Fin n) → F}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    Tendsto (fun r : ℝ => ∫ x, ‖g (r • x) - g x‖) (𝓝 1) (𝓝 0) := by
  obtain ⟨R, hR, hb⟩ := hcg.isBounded.exists_pos_norm_le
  obtain ⟨C, hC⟩ := hcg.exists_bound_of_continuous hg
  let D : EuclideanSpace ℝ (Fin n) → ℝ :=
    (closedBall 0 (2 * R)).indicator (fun _ => 2 * C)
  have hD : Integrable D :=
    (integrableOn_const (C := 2 * C) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n))
      (2 * R)).measure_ne_top).integrable_indicator isClosed_closedBall.measurableSet
  have hlim : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      Tendsto (fun r : ℝ => ‖g (r • x) - g x‖) (𝓝 1) (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    have hh : Continuous (fun r : ℝ => ‖g (r • x) - g x‖) := by fun_prop
    simpa only [one_smul, sub_self, norm_zero] using hh.tendsto 1
  have hm (r : ℝ) : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) => ‖g (r • x) - g x‖) volume :=
    (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖g (r • x) - g x‖) by
      fun_prop).aestronglyMeasurable
  have hd : ∀ᶠ r : ℝ in 𝓝 1,
      ∀ᵐ x : EuclideanSpace ℝ (Fin n), ‖‖g (r • x) - g x‖‖ ≤ D x := by
      filter_upwards [eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      apply Eventually.of_forall
      intro x
      rw [norm_norm]
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)
      · change ‖g (r • x) - g x‖ ≤
          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)).indicator (fun _ => 2 * C) x
        rw [indicator_of_mem hx]
        exact (norm_sub_le _ _).trans (by linarith [hC (r • x), hC x])
      · have hxR : 2 * R < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
        have hzero : g x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxs => by have hh := hb x hxs; linarith)
        have hrzero : g (r • x) = 0 := image_eq_zero_of_notMem_tsupport (by
          intro hxs
          have hh := hb (r • x) hxs
          rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ r)] at hh
          nlinarith [norm_nonneg x])
        simp only [hzero, hrzero, sub_self, norm_zero, D, indicator_of_notMem hx, le_refl]
  have ht : Tendsto (fun r : ℝ => ∫ x, ‖g (r • x) - g x‖) (𝓝 1)
      (𝓝 (∫ _ : EuclideanSpace ℝ (Fin n), (0 : ℝ))) :=
    tendsto_integral_filter_of_dominated_convergence D (Eventually.of_forall hm) hd hD hlim
  simpa only [integral_zero] using ht

lemma integral_norm_sub_triangle {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f g h : α → F}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ‖f x - h x‖ ∂μ) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ∫ x, ‖g x - h x‖ ∂μ := by
  have hi := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at hi
  rw [← hi]
  apply integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm)
  intro x
  simpa only [Pi.add_apply, Pi.sub_apply, dist_eq_norm] using dist_triangle (f x) (g x) (h x)

/-- Strong continuity at the identity of scalar dilations on actual L¹ functions. -/
theorem tendsto_integral_norm_dilate_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Tendsto (fun r : ℝ => ∫ x, ‖f (r • x) - f x‖) (𝓝 1) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun r => ha.trans_le (integral_nonneg fun _ => norm_nonneg _)
  · intro ε hε
    obtain ⟨g, hcg, hfg, hg, hig⟩ :=
      hf.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 8 by positivity)
    have hcont : ContinuousAt (fun r : ℝ => |(r ^ n)⁻¹|) 1 := by
      fun_prop (disch := simp)
    have hbound : ∀ᶠ r : ℝ in 𝓝 1, |(r ^ n)⁻¹| < 2 := by
      simpa only [one_pow, inv_one, abs_one] using
        hcont.eventually (Iio_mem_nhds (by norm_num : |((1 : ℝ) ^ n)⁻¹| < 2))
    have hsmall := (tendsto_order.mp (tendsto_integral_norm_dilate_sub_of_compact hg hcg)).2
      (ε / 2) (by positivity)
    filter_upwards [hbound, hsmall, eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)]
      with r hr he hr0
    have hfr := hf.comp_smul hr0
    have hgr := hig.comp_smul hr0
    have ht := (integral_norm_sub_triangle hfr hgr hf).trans
      (add_le_add le_rfl (integral_norm_sub_triangle hgr hig hf))
    have heq : (∫ x, ‖f (r • x) - g (r • x)‖) =
        |(r ^ n)⁻¹| * ∫ x, ‖f x - g x‖ := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
        Measure.integral_comp_smul volume (fun x => ‖f x - g x‖) r
    rw [heq] at ht
    have hsym : (∫ x, ‖g x - f x‖) = ∫ x, ‖f x - g x‖ :=
      integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)
    rw [hsym] at ht
    have hmul : |(r ^ n)⁻¹| * (∫ x, ‖f x - g x‖) ≤ 2 * (ε / 8) :=
      mul_le_mul hr.le hfg (integral_nonneg fun _ => norm_nonneg _) (by norm_num)
    linarith

/-- The inverse-dilation convention used by dilated indicators. -/
theorem tendsto_integral_norm_inv_dilate_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Tendsto (fun r : ℝ => ∫ x, ‖f (r⁻¹ • x) - f x‖) (𝓝 1) (𝓝 0) := by
  exact (tendsto_integral_norm_dilate_sub hf).comp
    (by simpa only [inv_one] using (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto)

/-- L¹ convergence survives dilation by factors tending to one, even when the
functions being dilated vary with the sequence. -/
theorem tendsto_integral_norm_inv_dilate_varying_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ j, Integrable (f j)) (hg : Integrable g)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖) atTop (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ j, r j ≠ 0) (hrt : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun j => ∫ x, ‖f j ((r j)⁻¹ • x) - g x‖) atTop (𝓝 0) := by
  have hbase := (tendsto_integral_norm_inv_dilate_sub hg).comp hrt
  have hscale : Tendsto (fun j => |r j ^ n| * ∫ x, ‖f j x - g x‖) atTop (𝓝 0) := by
    simpa only [one_pow, abs_one, one_mul] using (hrt.pow n).abs.mul ht
  have hsum : Tendsto (fun j => |r j ^ n| * (∫ x, ‖f j x - g x‖) +
      ∫ x, ‖g ((r j)⁻¹ • x) - g x‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_add] using hscale.add hbase
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) _ hsum
  intro j
  have htri := integral_norm_sub_triangle
    ((hf j).comp_smul (inv_ne_zero (hr j))) (hg.comp_smul (inv_ne_zero (hr j))) hg
  have heq : (∫ x, ‖f j ((r j)⁻¹ • x) - g ((r j)⁻¹ • x)‖) =
      |r j ^ n| * ∫ x, ‖f j x - g x‖ := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
      Measure.integral_comp_inv_smul volume (fun x => ‖f j x - g x‖) (r j)
  rwa [heq] at htri

lemma indicator_image_smul_eq_inv_smul {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : r ≠ 0) :
    ((fun x => r • x) '' E).indicator (fun _ => (1 : ℝ)) =
      fun x => E.indicator (fun _ => (1 : ℝ)) (r⁻¹ • x) := by
  classical
  funext x
  have hx : x ∈ (fun x => r • x) '' E ↔ r⁻¹ • x ∈ E := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hy
    · intro hy
      exact ⟨r⁻¹ • x, hy, by simp only [smul_smul, mul_inv_cancel₀ hr, one_smul]⟩
  simp only [indicator_apply, hx]

/-- The explicit L¹ dilation step for varying finite-volume sets. -/
theorem tendsto_eLpNorm_indicator_dilate_sub {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {G : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmG : NullMeasurableSet G volume)
    (hvE : ∀ j, volume (E j) < ∞) (hvG : volume G < ∞)
    (ht : Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ))) 1 volume)
      atTop (𝓝 0)) {r : ℕ → ℝ} (hr : ∀ j, r j ≠ 0) (hrt : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun j => eLpNorm
      (((fun x => r j • x) '' E j).indicator (fun _ => (1 : ℝ)) -
        G.indicator (fun _ => (1 : ℝ))) 1 volume) atTop (𝓝 0) := by
  have hiE (j) : Integrable ((E j).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (hvE j).ne).integrable_indicator₀ (hmE j)
  have hiG : Integrable (G.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hvG.ne).integrable_indicator₀ hmG
  have heqreal (j) : (eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ)))
      1 volume).toReal = ∫ x,
        ‖(E j).indicator (fun _ => (1 : ℝ)) x - G.indicator (fun _ => (1 : ℝ)) x‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hiE j).sub hiG).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hiE j).sub hiG),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
    rfl
  have hreal : Tendsto (fun j => ∫ x,
      ‖(E j).indicator (fun _ => (1 : ℝ)) x - G.indicator (fun _ => (1 : ℝ)) x‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, heqreal, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  have hmain := tendsto_integral_norm_inv_dilate_varying_sub hiE hiG hreal hr hrt
  have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmain
  have heq (j) : eLpNorm
      (((fun x => r j • x) '' E j).indicator (fun _ => (1 : ℝ)) -
        G.indicator (fun _ => (1 : ℝ))) 1 volume =
      ENNReal.ofReal (∫ x, ‖(E j).indicator (fun _ => (1 : ℝ)) ((r j)⁻¹ • x) -
        G.indicator (fun _ => (1 : ℝ)) x‖) := by
    rw [indicator_image_smul_eq_inv_smul _ (hr j),
      eLpNorm_one_eq_lintegral_enorm
        (((hiE j).comp_smul (inv_ne_zero (hr j))).sub hiG).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm
        (((hiE j).comp_smul (inv_ne_zero (hr j))).sub hiG)]
    rfl
  simpa only [Function.comp_def, ENNReal.ofReal_zero, ← heq] using hout

end LiquidDrop
