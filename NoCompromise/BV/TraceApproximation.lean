module

public import NoCompromise.BV.FlatTraces

@[expose] public section

/-!
# One-sided approximation of BV traces

The actual scalar cumulative representation bounds the normal mean error by
the slice variation. This is the domination needed to integrate the genuine
one-sided trace convergence over a flat interface.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsRealBVPolar.abs_setIntegral_restrict_le_mass {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {K : Set ℝ} (hK : IsCompact K) (S : Set ℝ) :
    |∫ t in S, σ t ∂μ.restrict K| ≤ μ.real K := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ := (μ.restrict K).restrict S)
    ((ae_restrict_of_ae (ae_restrict_of_ae h.norm_ae)).mono fun t ht =>
      show ‖σ t‖ ≤ (1 : ℝ) by simpa only [Real.norm_eq_abs] using ht.le)
  have hh' : |∫ t in S, σ t ∂μ.restrict K| ≤ ((μ.restrict K).restrict S).real univ := by
    simpa only [Real.norm_eq_abs, one_mul] using hh
  apply hh'.trans
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    (measureReal_mono (μ := μ.restrict K) (subset_univ S))

/-- Uniform one-sided normal mean error, controlled by a compact derivative mass. -/
lemma IsRealBVPolar.mean_abs_sub_traces_le {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (a : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    r⁻¹ * (∫ t in Ioo (a - r) a, |f t - bvLeftTrace f a|) ≤
        2 * μ.real (Icc (a - 2) (a + 2)) ∧
    r⁻¹ * (∫ t in Ioo a (a + r), |f t - bvRightTrace f a|) ≤
        2 * μ.real (Icc (a - 2) (a + 2)) := by
  let := h.finiteOnCompacts
  let K := Icc (a - 2) (a + 2)
  let M := μ.real K
  obtain ⟨c, hfc, hL, hR⟩ := h.exists_cumulative_with_traces
    (show a ∈ Ioo (a - 2) (a + 2) from ⟨by linarith, by linarith⟩)
  have hestimate (S : Set ℝ)
      (hs : S ⊆ Ioo (a - 2) (a + 2)) (hvol : volume.real S = r)
      (v : ℝ) (hv : |v| ≤ M) :
      r⁻¹ * (∫ t in S, |f t - (v + c)|) ≤ 2 * M := by
    have hfinite : volume S ≠ ∞ :=
      ne_top_of_le_ne_top isCompact_Icc.measure_ne_top (measure_mono
        (hs.trans Ioo_subset_Icc_self))
    have hi : IntegrableOn f S volume :=
      (h.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
        (hs.trans Ioo_subset_Icc_self)
    have hc : IntegrableOn (fun _ : ℝ => v + c) S volume := integrableOn_const hfinite
    have hie : IntegrableOn (fun t => |f t - (v + c)|) S volume := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using! (hi.sub hc).norm
    have hbound : (∫ t in S, |f t - (v + c)|) ≤ r * (2 * M) := by
      calc
        _ ≤ ∫ _t : ℝ in S, 2 * M := by
          apply integral_mono_ae hie (integrableOn_const hfinite)
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hfc] with t ht
          rw [ht, add_sub_add_right_eq_sub]
          exact (abs_sub _ _).trans (by
            have hb := h.abs_setIntegral_restrict_le_mass
              (isCompact_Icc (a := a - 2) (b := a + 2)) (Iio t)
            change |∫ s in Iio t, σ s ∂μ.restrict K| ≤ M at hb
            linarith)
        _ = _ := by rw [setIntegral_const, hvol, smul_eq_mul]
    calc
      _ ≤ r⁻¹ * (r * (2 * M)) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hr.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hmassL : volume.real (Ioo (a - r) a) = r := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmassR : volume.real (Ioo a (a + r)) = r := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hL, hR]
  constructor
  · apply hestimate _ _ hmassL _
      (h.abs_setIntegral_restrict_le_mass isCompact_Icc (Iio a))
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  · apply hestimate _ _ hmassR _
      (h.abs_setIntegral_restrict_le_mass isCompact_Icc (Iic a))
    intro t ht
    constructor <;> linarith [ht.1, ht.2]

/-- The dominating quantity is the genuine distributional slice variation. -/
lemma IsBVOn.mean_abs_sub_traces_le {f : ℝ → ℝ}
    (hf : IsBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    r⁻¹ * (∫ t in Ioo (a - r) a, |f t - bvLeftTrace f a|) ≤
        2 * (variation (f ∘ euclideanOneReal) univ).toReal ∧
    r⁻¹ * (∫ t in Ioo a (a + r), |f t - bvRightTrace f a|) ≤
        2 * (variation (f ∘ euclideanOneReal) univ).toReal := by
  have hl := isLocallyBVOn_of_variation_lt_top isOpen_univ hf.1.locallyIntegrableOn hf.2
  obtain ⟨μ, σ, h⟩ := exists_real_bv_polar hl
  have hm : μ univ = variation (f ∘ euclideanOneReal) univ := by
    simpa only [preimage_univ] using h.open_eq univ isOpen_univ
  have hfin : μ univ ≠ ∞ := by rw [hm]; exact hf.2.ne
  have hb : μ.real (Icc (a - 2) (a + 2)) ≤
      (variation (f ∘ euclideanOneReal) univ).toReal := by
    simpa only [Measure.real, hm] using
      measureReal_mono (μ := μ) (subset_univ (Icc (a - 2) (a + 2))) hfin
  have hb' := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨(h.mean_abs_sub_traces_le a hr hr1).1.trans hb',
    (h.mean_abs_sub_traces_le a hr hr1).2.trans hb'⟩

/-- The averaged absolute error between the lower normal slab and its actual trace. -/
def flatBVLeftMeanError {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (a r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  r⁻¹ * ∫ t in Ioo (a - r) a, |f (graphAppendN x t) - flatBVLeftTrace f a x|

/-- The averaged absolute error between the upper normal slab and its actual trace. -/
def flatBVRightMeanError {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (a r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  r⁻¹ * ∫ t in Ioo a (a + r), |f (graphAppendN x t) - flatBVRightTrace f a x|

lemma aestronglyMeasurable_normal_mean_error {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : AEStronglyMeasurable f volume) {T : EuclideanSpace ℝ (Fin n) → ℝ}
    (hT : AEStronglyMeasurable T volume) (S : Set ℝ) (r : ℝ) :
    AEStronglyMeasurable (fun x => r⁻¹ * ∫ t in S, |f (graphAppendN x t) - T x|) volume := by
  have hm := hf.aemeasurable.comp_quasiMeasurePreserving
    (realLineCoordinates_measurePreserving n).quasiMeasurePreserving
  have hg : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => |f (graphAppendN p.1 p.2) - T p.1|)
      (volume.prod volume) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_def,
      realLineCoordinates_apply] using!
      (hm.sub hT.aemeasurable.comp_fst).aestronglyMeasurable.norm
  exact ((hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_right'
    ).const_mul _

lemma tendsto_lintegral_of_slice_variation_domination {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ)
    {F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hm : ∀ r, AEStronglyMeasurable (F r) volume)
    (hb : ∀ r, 0 < r → r < 1 → ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      F r x ≤ 2 * (variation (lineSlice f x) univ).toReal)
    (ht : ∀ᵐ x : EuclideanSpace ℝ (Fin n), Tendsto (fun r => F r x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => ∫⁻ x, ENNReal.ofReal (F r x)) (𝓝[>] 0) (𝓝 0) := by
  have hfin : (∫⁻ x : EuclideanSpace ℝ (Fin n), 2 * variation (lineSlice f x) univ) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ (by norm_num)]
    apply ne_top_of_le_ne_top _ (show 2 * (∫⁻ x, variation (lineSlice f x) univ) ≤
        2 * variation f univ from by
      gcongr
      exact hf.ae_lineSlice_and_lintegral_variation_le.2)
    exact (ENNReal.mul_lt_top (by norm_num) hf.2).ne
  have hlim := tendsto_lintegral_filter_of_dominated_convergence'
    (l := 𝓝[>] (0 : ℝ))
    (fun x : EuclideanSpace ℝ (Fin n) => 2 * variation (lineSlice f x) univ)
    (F := fun r x => ENNReal.ofReal (F r x)) (f := fun _ => 0)
    (Eventually.of_forall fun r => (hm r).aemeasurable.ennreal_ofReal) ?_ hfin ?_
  · simpa only [lintegral_zero] using hlim
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    filter_upwards [hb r hr.1 hr.2] with x hx
    apply (ENNReal.ofReal_le_ofReal hx).trans
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    gcongr
    exact ENNReal.ofReal_toReal_le
  · filter_upwards [ht] with x hx
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx

/-- One-sided normal mean errors converge strongly in `L¹` over the whole flat interface. -/
theorem IsBVOn.tendsto_flatBVMeanError_lintegral {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    Tendsto (fun r => ∫⁻ x, ENNReal.ofReal (flatBVLeftMeanError f a r x))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r => ∫⁻ x, ENNReal.ofReal (flatBVRightMeanError f a r x))
      (𝓝[>] 0) (𝓝 0) := by
  have hi := integrableOn_univ.mp hf.1
  have hprod := ((realLineCoordinates_measurePreserving n).integrable_comp
    hi.aestronglyMeasurable).mpr hi
  have hb (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      ∀ᵐ x : EuclideanSpace ℝ (Fin n),
        flatBVLeftMeanError f a r x ≤ 2 * (variation (lineSlice f x) univ).toReal ∧
        flatBVRightMeanError f a r x ≤ 2 * (variation (lineSlice f x) univ).toReal := by
    filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1] with x hx
    have hx' : IsBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hx
    exact hx'.mean_abs_sub_traces_le a hr hr1.le
  have ht : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      Tendsto (fun r => flatBVLeftMeanError f a r x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => flatBVRightMeanError f a r x) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1, hprod.prod_right_ae]
      with x hx hix
    have hl := isLocallyBVOn_of_variation_lt_top isOpen_univ hx.1.locallyIntegrableOn hx.2
    have hl' : IsLocallyBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hl
    exact ⟨(hl'.hasBVLeftTrace a).tendsto_mean_abs_sub hix.locallyIntegrable,
      (hl'.hasBVRightTrace a).tendsto_mean_abs_sub hix.locallyIntegrable⟩
  constructor
  · apply tendsto_lintegral_of_slice_variation_domination hf
      (fun r => aestronglyMeasurable_normal_mean_error hi.aestronglyMeasurable
        (hf.aestronglyMeasurable_flatBVLeftTrace a) _ r)
      (fun r hr hr1 => (hb r hr hr1).mono fun _ hx => hx.1)
    exact ht.mono fun _ hx => hx.1
  · apply tendsto_lintegral_of_slice_variation_domination hf
      (fun r => aestronglyMeasurable_normal_mean_error hi.aestronglyMeasurable
        (hf.aestronglyMeasurable_flatBVRightTrace a) _ r)
      (fun r hr hr1 => (hb r hr hr1).mono fun _ hx => hx.2)
    exact ht.mono fun _ hx => hx.2

lemma tendsto_integral_of_nonneg_lintegral_zero {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {F : ι → α → ℝ}
    (hn : ∀ᶠ i in l, ∀ x, 0 ≤ F i x)
    (ht : Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (F i x) ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have ht' : Tendsto (fun i => (∫⁻ x, ENNReal.ofReal (F i x) ∂μ).toReal) l (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using!
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp ht
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht'
  filter_upwards [hn] with i hi
  calc
    _ ≤ (∫⁻ x, ENNReal.ofReal ‖F i x‖ ∂μ).toReal := norm_integral_le_lintegral_norm _
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hi x)]

/-- Real-integral version of the strong one-sided trace approximation. -/
theorem IsBVOn.tendsto_flatBVMeanError_integral {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    Tendsto (fun r => ∫ x, flatBVLeftMeanError f a r x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r => ∫ x, flatBVRightMeanError f a r x) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  constructor
  · apply tendsto_integral_of_nonneg_lintegral_zero _
      (hf.tendsto_flatBVMeanError_lintegral a).1
    filter_upwards [hpos] with r hr
    exact fun x => mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => abs_nonneg _)
  · apply tendsto_integral_of_nonneg_lintegral_zero _
      (hf.tendsto_flatBVMeanError_lintegral a).2
    filter_upwards [hpos] with r hr
    exact fun x => mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => abs_nonneg _)

end LiquidDrop
