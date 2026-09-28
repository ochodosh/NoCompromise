import NoCompromise.BV.CoareaLayerCake

/-!
# Strict approximation with almost-everywhere convergence of superlevels

The global integrability of the strict-approximation errors supplies one common
subsequence for almost every level. Lower semicontinuity and Fatou transfer
measurable perimeter majorants to the limiting locally BV function.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Almost every superlevel converges along a subsequence when the real L1 errors vanish. -/
theorem exists_subseq_superlevel_l1_of_integral_errors {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, AEMeasurable (f j) μ) (hg : AEMeasurable g μ)
    (hi : ∀ j, Integrable (fun x => f j x - g x) μ)
    (ht : Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun j => ∫⁻ x, ENNReal.ofReal
        |superlevelIndicator (f (σ j)) t x - superlevelIndicator g t x| ∂μ)
        atTop (𝓝 0) := by
  apply exists_subseq_superlevel_l1_of_l1_errors hf hg hi
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ENNReal.ofReal_zero,
    ofReal_integral_eq_lintegral_ofReal (hi _).abs (ae_of_all _ fun _ => abs_nonneg _)] using h

/-- The level indicators of a locally integrable function are locally integrable. -/
lemma locallyIntegrableOn_superlevelIndicator {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) (t : ℝ) :
    LocallyIntegrableOn (superlevelIndicator f t) U := by
  apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
  intro K hKU hK
  have hm := (hf.integrableOn_compact_subset hKU hK).aestronglyMeasurable
  change Integrable (superlevelIndicator f t) (volume.restrict K)
  apply (integrableOn_const (μ := volume) (C := (1 : ℝ)) hK.measure_ne_top).mono'
  · exact aestronglyMeasurable_const.indicator₀
      (nullMeasurableSet_lt aemeasurable_const hm.aemeasurable)
  · exact ae_of_all _ fun x => by
      simp only [superlevelIndicator_apply]
      split_ifs <;> norm_num

/-- Global extended L1 convergence on an open set implies local real L1 convergence. -/
lemma tendsto_integral_abs_on_compact_of_lintegral {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U)
    (ht : Tendsto (fun j => ∫⁻ x in U, ENNReal.ofReal |f j x - g x|) atTop (𝓝 0))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - g x|)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun j => lintegral_mono_set hKU)
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hs
  have heq (j) : (∫ x in K, |f j x - g x|) =
      (∫⁻ x in K, ENNReal.ofReal |f j x - g x|).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
      (((hf j).integrableOn_compact_subset hKU hK).sub
        (hg.integrableOn_compact_subset hKU hK)).abs.aestronglyMeasurable
  simpa only [heq, ENNReal.toReal_zero, Function.comp_def] using hreal

/-- Lower semicontinuity of perimeter from convergence of superlevel indicators. -/
theorem perimeter_superlevel_le_liminf_of_lintegral {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U) (t : ℝ)
    (ht : Tendsto (fun j => ∫⁻ x in U, ENNReal.ofReal
      |superlevelIndicator (f j) t x - superlevelIndicator g t x|) atTop (𝓝 0)) :
    perimeterIn {x | t < g x} U ≤ liminf (fun j => perimeterIn {x | t < f j x} U) atTop := by
  exact variation_le_liminf_of_locally_l1 hU
    (fun j => locallyIntegrableOn_superlevelIndicator hU (hf j) t)
    (locallyIntegrableOn_superlevelIndicator hU hg t)
    (fun K hK hKU => tendsto_integral_abs_on_compact_of_lintegral
      (fun j => locallyIntegrableOn_superlevelIndicator hU (hf j) t)
      (locallyIntegrableOn_superlevelIndicator hU hg t) ht hK hKU)

/-- Strict approximation can be chosen so the level indicators converge for almost every level. -/
theorem strict_approximation_with_superlevel_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) U) ∧
      (∀ j, IntegrableOn (fun x => g j x - f x) U) ∧
      Tendsto (fun j => ∫ x in U, |g j x - f x|) atTop (𝓝 0) ∧
      (∀ᵐ t : ℝ ∂volume, Tendsto (fun j => ∫⁻ x in U, ENNReal.ofReal
        |superlevelIndicator (g j) t x - superlevelIndicator f t x|) atTop (𝓝 0)) ∧
      (variation f U < ∞ → (∀ j, IntegrableOn (gradient (g j)) U) ∧
        Tendsto (fun j => ∫ x in U, ‖gradient (g j) x‖) atTop
          (𝓝 (variation f U).toReal)) := by
  obtain ⟨g, hg, hi, he, _, hgrad⟩ := strict_approximation_on hU hf
  obtain ⟨σ, hσ, hlevels⟩ := exists_subseq_superlevel_l1_of_integral_errors
    (fun j => (hg j).continuousOn.locallyIntegrableOn hU.measurableSet
      |>.aestronglyMeasurable.aemeasurable) hf.1.aestronglyMeasurable.aemeasurable hi he
  refine ⟨fun j => g (σ j), fun j => hg (σ j), fun j => hi (σ j),
    he.comp hσ.tendsto_atTop, hlevels, ?_⟩
  intro hfin
  exact ⟨fun j => (hgrad hfin).1 (σ j), (hgrad hfin).2.comp hσ.tendsto_atTop⟩

/-- Fatou transfers measurable majorants along convergent level indicators. -/
theorem lintegral_perimeter_superlevel_le_of_majorants {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U)
    (ht : ∀ᵐ t : ℝ ∂volume, Tendsto (fun j => ∫⁻ x in U, ENNReal.ofReal
      |superlevelIndicator (f j) t x - superlevelIndicator g t x|) atTop (𝓝 0))
    {q : ℕ → ℝ → ℝ≥0∞} (hq : ∀ j, Measurable (q j))
    (hbound : ∀ j t, perimeterIn {x | t < f j x} U ≤ q j t)
    {e : ℕ → ℝ≥0∞} {v : ℝ≥0∞} (henergy : ∀ j, (∫⁻ t : ℝ, q j t) ≤ e j)
    (he : Tendsto e atTop (𝓝 v)) :
    (∫⁻ t : ℝ, perimeterIn {x | t < g x} U) ≤ v := by
  have hl : (∫⁻ t : ℝ, perimeterIn {x | t < g x} U) ≤
      ∫⁻ t : ℝ, liminf (fun j => q j t) atTop := by
    apply lintegral_mono_ae
    filter_upwards [ht] with t htt
    exact (perimeter_superlevel_le_liminf_of_lintegral hU hf hg t htt).trans
      (liminf_le_liminf (Eventually.of_forall fun j => hbound j t))
  exact hl.trans ((lintegral_liminf_le hq).trans
    ((liminf_le_liminf (Eventually.of_forall henergy)).trans_eq he.liminf_eq))

end LiquidDrop
