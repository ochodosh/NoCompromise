import NoCompromise.BV.OneDimensional
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The one-dimensional derivative as a jump measure

The scalar polar measure is transported from the established one-dimensional
BV representation. Its cumulative integral determines the unique left-continuous
representative. On a binary region its signed atom at every point is the actual
right-minus-left jump, and the measure is concentrated on the locally finite
jump set. This gives exact finite jump-sum formulas for compactly supported
weights, Borel subsets of compact subintervals, and distributional tests.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- The right limit of a strict cumulative integral includes the threshold level. -/
lemma tendsto_integral_sublevel_right {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w a : α → ℝ} (hw : Integrable w μ) (ha : Measurable a) (t : ℝ) :
    Tendsto (fun s : ℝ => ∫ x in {x | a x < s}, w x ∂μ) (𝓝[>] t)
      (𝓝 (∫ x in {x | a x ≤ t}, w x ∂μ)) := by
  have hi (s : ℝ) : AEStronglyMeasurable ({x | a x < s}.indicator w) μ :=
    hw.aestronglyMeasurable.indicator (measurableSet_lt ha measurable_const)
  have hb (s : ℝ) : ∀ᵐ x ∂μ, ‖{x | a x < s}.indicator w x‖ ≤ ‖w x‖ :=
    ae_of_all _ fun x => norm_indicator_le_norm_self _ _
  have ht : ∀ᵐ x ∂μ, Tendsto (fun s : ℝ => {x | a x < s}.indicator w x)
      (𝓝[>] t) (𝓝 ({x | a x ≤ t}.indicator w x)) := by
    apply ae_of_all
    intro x
    by_cases hx : a x ≤ t
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hxs : a x < s := hx.trans_lt hs
      simp [Set.indicator, hx, hxs]
    · apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds (lt_of_not_ge hx)).filter_mono nhdsWithin_le_nhds]
        with s hs
      have hxs : ¬a x < s := not_lt.mpr hs.le
      simp [Set.indicator, hx, hxs]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖)
    (Eventually.of_forall hi) (Eventually.of_forall hb) hw.norm ht
  simpa only [integral_indicator (measurableSet_lt ha measurable_const),
    integral_indicator (measurableSet_le ha measurable_const)] using hh

/-- The jump of a cumulative primitive is exactly the signed mass of the threshold level. -/
lemma oneDimensionalJump_integral_sublevel {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w a : α → ℝ} (hw : Integrable w μ) (ha : Measurable a) (t c : ℝ) :
    oneDimensionalJump (fun s : ℝ => (∫ x in {x | a x < s}, w x ∂μ) + c) t =
      ∫ x in {x | a x = t}, w x ∂μ := by
  have hr := (tendsto_integral_sublevel_right hw ha t).add_const c
  have he := rightLim_eq_of_tendsto hr
  rw [oneDimensionalJump, he, add_sub_add_right_eq_sub]
  have heq : (∫ x in {x | a x ≤ t}, w x ∂μ) =
      (∫ x in {x | a x < t}, w x ∂μ) + ∫ x in {x | a x = t}, w x ∂μ := by
    have hlt : MeasurableSet {x | a x < t} := measurableSet_lt ha measurable_const
    have heq : MeasurableSet {x | a x = t} := measurableSet_eq_fun ha measurable_const
    rw [← integral_indicator (measurableSet_le ha measurable_const),
      ← integral_indicator hlt, ← integral_indicator heq,
      ← integral_add (hw.indicator hlt) (hw.indicator heq)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      rcases lt_trichotomy (a x) t with h | h | h
      · simp [Set.indicator, h, h.le, h.ne]
      · simp [Set.indicator, h]
      · simp [Set.indicator, not_le_of_gt h, not_lt_of_ge h.le, h.ne']
  rw [heq]
  ring

/-- The scalar distributional derivative on the real line, with its exact variation mass. -/
structure IsRealBVPolar (f : ℝ → ℝ) (μ : Measure ℝ) (σ : ℝ → ℝ) : Prop where
  regular : μ.Regular
  finiteOnCompacts : IsFiniteMeasureOnCompacts μ
  measurable : Measurable σ
  norm_ae : ∀ᵐ t ∂μ, |σ t| = 1
  locallyIntegrable : LocallyIntegrable f volume
  test_eq : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    -(∫ t, f t * deriv ψ t) = ∫ t, ψ t * σ t ∂μ
  open_eq : ∀ O : Set ℝ, IsOpen O → μ O =
    variation (f ∘ euclideanOneReal) (euclideanOneReal ⁻¹' O)

/-- The existing Euclidean polar theorem transports to the ordinary real line. -/
theorem exists_real_bv_polar {f : ℝ → ℝ}
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) :
    ∃ μ : Measure ℝ, ∃ σ : ℝ → ℝ, IsRealBVPolar f μ σ := by
  obtain ⟨ρ, τ, hρ, hfin, hpol⟩ := exists_distributional_polar_representation isOpen_univ hf
  let e : (univ : Set (EuclideanSpace ℝ (Fin 1))) ≃ₜ ℝ :=
    (Homeomorph.Set.univ _).trans euclideanOneReal.toHomeomorph
  let μ : Measure ℝ := Measure.map e ρ
  let σ : ℝ → ℝ := fun t => τ (e.symm t) 0
  let : ρ.Regular := hρ
  let : IsFiniteMeasureOnCompacts ρ := hfin
  let : μ.Regular := Measure.Regular.map e
  have hi : LocallyIntegrable f volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    have hif := (locallyIntegrableOn_univ.mp hf.1).integrableOn_isCompact
      (hK.image euclideanOneReal.symm.continuous)
    have ht := euclideanOneReal.symm.measurePreserving.integrableOn_comp_preimage
      euclideanOneReal.symm.toHomeomorph.measurableEmbedding
      (s := euclideanOneReal.symm '' K) (f := f ∘ euclideanOneReal)
    rw [euclideanOneReal.symm.injective.preimage_image] at ht
    simpa only [Function.comp_def, euclideanOneReal.apply_symm_apply] using ht.mpr hif
  refine ⟨μ, σ, inferInstance, inferInstance, ?_, ?_, hi, ?_, ?_⟩
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).measurable.comp hpol.measurable).comp
      e.symm.continuous.measurable
  · change ∀ᵐ t ∂Measure.map e ρ, |σ t| = 1
    rw [e.measurableEmbedding.ae_map_iff]
    filter_upwards [hpol.norm_ae] with t ht
    change |τ (e.symm (e t)) 0| = 1
    rw [e.symm_apply_apply]
    simpa only [← Real.norm_eq_abs, ← euclideanOneReal_apply,
      euclideanOneReal.norm_map] using ht
  · intro ψ hψ hcψ
    let φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
      ⟨⟨ψ ∘ euclideanOneReal, hψ.continuous.comp euclideanOneReal.continuous⟩,
        hcψ.comp_homeomorph euclideanOneReal.toHomeomorph⟩
    have hφ : ContDiff ℝ 1 φ := hψ.comp euclideanOneReal.toContinuousLinearEquiv.contDiff
    have ht := hpol.test_eq 0 φ hφ (subset_univ _)
    have hd (x : EuclideanSpace ℝ (Fin 1)) :
        fderiv ℝ φ x (EuclideanSpace.single 0 1) = deriv ψ (euclideanOneReal x) := by
      have he : HasFDerivAt (fun y => euclideanOneReal y)
          euclideanOneReal.toContinuousLinearEquiv.toContinuousLinearMap x :=
        euclideanOneReal.toContinuousLinearEquiv.hasFDerivAt
      have hh := (hψ.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x he
      change fderiv ℝ (ψ ∘ euclideanOneReal) x (EuclideanSpace.single 0 1) = _
      rw [hh.fderiv]
      simp [smul_apply, smul_eq_mul]
    simp only [Measure.restrict_univ, hd, Function.comp_def] at ht
    have he := euclideanOneReal.measurePreserving.integral_comp
      euclideanOneReal.toHomeomorph.measurableEmbedding (fun t => f t * deriv ψ t)
    rw [he] at ht
    change -(∫ t, f t * deriv ψ t) =
      (∫ x : (univ : Set (EuclideanSpace ℝ (Fin 1))), ψ (e x) * τ x 0 ∂ρ) at ht
    rw [show μ = Measure.map e ρ from rfl, e.measurableEmbedding.integral_map]
    simpa only [σ, e.symm_apply_apply] using ht
  · intro O hO
    rw [show μ = Measure.map e ρ from rfl, Measure.map_apply e.continuous.measurable
      hO.measurableSet]
    exact (hpol.variation_eq_measure isOpen_univ (hO.preimage euclideanOneReal.continuous)
      (subset_univ _) hf.1).symm

lemma variation_const_eq_zero {n : ℕ} (c : ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation (fun _ => c) U = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have heq : (∫ x in U, divergenceN X x) = ∫ x, divergenceN X x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hX.2.2.1 h))
  simp only [integral_const_mul, heq, integral_divergenceN_eq_zero hX.1 hX.2.1, mul_zero,
    ENNReal.ofReal_zero]
  exact le_rfl

lemma IsRealBVPolar.measure_eq_zero_of_ae_const {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {O : Set ℝ} (hO : IsOpen O) {c : ℝ}
    (hf : f =ᵐ[volume.restrict O] fun _ => c) : μ O = 0 := by
  rw [h.open_eq O hO]
  have hp := euclideanOneReal.measurePreserving.restrict_preimage_emb
    euclideanOneReal.toHomeomorph.measurableEmbedding O
  have he := hp.quasiMeasurePreserving.ae_eq_comp hf
  rw [variation_congr_ae _ he]
  exact variation_const_eq_zero c _

lemma IsRealBVPolar.notMem_support_of_continuousAt_binary {f σ g : ℝ → ℝ}
    {μ : Measure ℝ} (h : IsRealBVPolar f μ σ) {U : Set ℝ} (hU : IsOpen U)
    (hfg : f =ᵐ[volume.restrict U] g) (hb : ∀ t ∈ U, g t ∈ ({0, 1} : Set ℝ))
    {t : ℝ} (ht : t ∈ U) (hct : ContinuousAt g t) : t ∉ μ.support := by
  have hnear : ∀ᶠ s in 𝓝 t, g s ∈ ({0, 1} : Set ℝ) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact hb s hs
  have heq := eventually_eq_of_tendsto_binary hnear hct.tendsto
  have hn : {s | g s = g t} ∩ U ∈ 𝓝 t := inter_mem heq (hU.mem_nhds ht)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hn
  have hsub : ball t r ⊆ U := fun s hs => (hrs hs).2
  have hconst : f =ᵐ[volume.restrict (ball t r)] fun _ => g t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hfg,
      ae_restrict_mem measurableSet_ball] with s hs hsr
    exact hs.trans (hrs hsr).1
  exact Measure.notMem_support_iff_exists.mpr
    ⟨ball t r, ball_mem_nhds t hr, h.measure_eq_zero_of_ae_const isOpen_ball hconst⟩

/-- In a binary region, the one-dimensional polar measure is concentrated on the
nonzero jumps of its canonical left-continuous representative. -/
theorem IsRealBVPolar.ae_mem_jumps_on_binary_region {f σ g : ℝ → ℝ}
    {μ : Measure ℝ} (h : IsRealBVPolar f μ σ) {U : Set ℝ} (hU : IsOpen U)
    (hfg : f =ᵐ[volume.restrict U] g) (hg : BoundedVariationOn g univ)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ t ∈ U, g t ∈ ({0, 1} : Set ℝ)) :
    ∀ᵐ t ∂μ.restrict U, oneDimensionalJump g t ≠ 0 := by
  filter_upwards [ae_restrict_of_ae (Measure.support_mem_ae (μ := μ)),
    ae_restrict_mem hU.measurableSet] with t ht htU
  intro hz
  have hcont := (oneDimensionalJump_eq_zero_iff hg (hc t)).mp hz
  exact h.notMem_support_of_continuousAt_binary hU hfg hb htU hcont ht

lemma locallyIntegrable_of_boundedVariationOn_real {g : ℝ → ℝ}
    (hg : BoundedVariationOn g univ) : LocallyIntegrable g volume := by
  have hm := measurable_of_countable_not_continuousAt hg.countable_not_continuousAt
  have hb (t : ℝ) : ‖g t‖ ≤ ‖g 0‖ + (eVariationOn g univ).toReal := by
    have hd := hg.dist_le (mem_univ t) (mem_univ 0)
    calc
      ‖g t‖ ≤ ‖g 0‖ + dist (g t) (g 0) := by
        simpa only [dist_zero_right, add_comm] using dist_triangle (g t) (g 0) 0
      _ ≤ _ := add_le_add le_rfl hd
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply Integrable.mono (integrableOn_const (C := ‖g 0‖ + (eVariationOn g univ).toReal)
    hK.measure_ne_top) hm.aestronglyMeasurable.restrict
  exact ae_of_all _ fun t => (hb t).trans (le_abs_self _)

/-- On an interval, the weak derivative determines the cumulative primitive up to a constant. -/
lemma IsRealBVPolar.exists_cumulative_ae_eq_Ioo {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (a b : ℝ) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo a b)]
      fun t => (∫ s in Iio t, σ s ∂μ.restrict (Icc a b)) + c := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (Icc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hw : Integrable σ (μ.restrict (Icc a b)) :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun s hs => by simpa only [Real.norm_eq_abs] using hs.le)
  let F : ℝ → ℝ := fun t => ∫ s in Iio t, σ s ∂μ.restrict (Icc a b)
  have hF : BoundedVariationOn F univ := boundedVariationOn_integral_sublevel hw measurable_id
  have hFi := locallyIntegrable_of_boundedVariationOn_real hF
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
    ((h.locallyIntegrable.sub hFi).locallyIntegrableOn (Ioo a b)) (by
      intro ψ hψ hcψ hsψ
      have hif : Integrable (fun t => f t * deriv ψ t) volume := by
        simpa only [smul_eq_mul] using
          h.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
          (hψ.continuous_deriv le_rfl) hcψ.deriv
      have hiF : Integrable (fun t => F t * deriv ψ t) volume := by
        simpa only [smul_eq_mul] using hFi.integrable_smul_right_of_hasCompactSupport
          (hψ.continuous_deriv le_rfl) hcψ.deriv
      have hd (t : ℝ) (ht : t ∉ Ioo a b) : deriv ψ t = 0 :=
        deriv_of_notMem_tsupport (fun hs => ht (hsψ hs))
      have heq (u : ℝ → ℝ) : (∫ t in Ioo a b, u t * deriv ψ t) = ∫ t, u t * deriv ψ t :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by rw [hd t ht, mul_zero]
      have hr : (∫ t, ψ t * σ t ∂μ.restrict (Icc a b)) = ∫ t, ψ t * σ t ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
          have hn : t ∉ tsupport ψ := fun hs => ht (Ioo_subset_Icc_self (hsψ hs))
          rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
      have hp := h.test_eq ψ hψ hcψ
      have hcum := integral_cumulative_mul_deriv (μ.restrict (Icc a b)) hw measurable_id hψ hcψ
      change (∫ t, F t * deriv ψ t) = -(∫ t, ψ t * σ t ∂μ.restrict (Icc a b)) at hcum
      rw [hr] at hcum
      change (∫ t in Ioo a b, (f t - F t) * deriv ψ t) = 0
      simp only [sub_mul]
      rw [integral_sub hif.integrableOn hiF.integrableOn, heq f, heq F]
      linarith)
  refine ⟨c, ?_⟩
  change (fun t => f t - F t) =ᵐ[volume.restrict (Ioo a b)] fun _ => c at hc
  exact hc.mono fun t ht => by dsimp only [F] at ht ⊢; linarith

lemma IsRealBVPolar.exists_cumulative_eqOn_Ioo {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (a b : ℝ)
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t) :
    ∃ c : ℝ, EqOn g (fun t => (∫ s in Iio t, σ s ∂μ.restrict (Icc a b)) + c) (Ioo a b) := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (Icc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hw : Integrable σ (μ.restrict (Icc a b)) :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun s hs => by simpa only [Real.norm_eq_abs] using hs.le)
  obtain ⟨c, hcF⟩ := h.exists_cumulative_ae_eq_Ioo a b
  refine ⟨c, eqOn_Ioo_of_left_continuous_ae_eq (fun t _ => hc t) ?_ (hfg.symm.trans hcF)⟩
  intro t _
  exact (continuousWithinAt_integral_sublevel_left hw measurable_id t).add_const c

/-- Every atom of the scalar derivative has exactly the right-minus-left jump weight. -/
theorem IsRealBVPolar.oneDimensionalJump_eq_atom {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {a b t : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g)
    (hc : ∀ s, ContinuousWithinAt g (Iic s) s) (ht : t ∈ Ioo a b) :
    oneDimensionalJump g t = μ.real {t} * σ t := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (Icc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hw : Integrable σ (μ.restrict (Icc a b)) :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun s hs => by simpa only [Real.norm_eq_abs] using hs.le)
  obtain ⟨c, heq⟩ := h.exists_cumulative_eqOn_Ioo a b hfg hc
  let F : ℝ → ℝ := fun r => (∫ s in Iio r, σ s ∂μ.restrict (Icc a b)) + c
  have hnear : F =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (heq hs).symm
  have hFlim : Tendsto F (𝓝[>] t)
      (𝓝 ((∫ s in Iic t, σ s ∂μ.restrict (Icc a b)) + c)) :=
    (tendsto_integral_sublevel_right hw measurable_id t).add_const c
  have hglim := hFlim.congr' (hnear.filter_mono nhdsWithin_le_nhds)
  have hjump : oneDimensionalJump g t = oneDimensionalJump F t := by
    rw [oneDimensionalJump, oneDimensionalJump,
      rightLim_eq_of_tendsto hglim, rightLim_eq_of_tendsto hFlim, heq ht]
  rw [hjump]
  have hJF := oneDimensionalJump_integral_sublevel hw measurable_id t c
  change oneDimensionalJump F t = ∫ s in {t}, σ s ∂μ.restrict (Icc a b) at hJF
  rw [hJF, integral_singleton, smul_eq_mul]
  congr 1
  rw [measureReal_def, measureReal_def, Measure.restrict_apply (measurableSet_singleton t),
    singleton_inter_of_mem (Ioo_subset_Icc_self ht)]

/-- Every integrable weight supported on a compact set integrates against the signed
polar measure as the finite sum of its values times the actual jumps. -/
theorem IsRealBVPolar.integral_eq_finsum_jumps_of_support {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {a b : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) (hg : BoundedVariationOn g univ)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ))
    {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ Ioo a b)
    {ψ : ℝ → ℝ} (hsψ : Function.support ψ ⊆ K)
    (hq : IntegrableOn (fun t => ψ t * σ t) K μ) :
    (∫ t, ψ t * σ t ∂μ) = ∑ᶠ t : ℝ, ψ t * oneDimensionalJump g t := by
  classical
  let := h.finiteOnCompacts
  have hJ := finite_oneDimensionalJump_of_binary_ae hg hc
    (ae_restrict_of_forall_mem measurableSet_Ioo hb) hK hKU
  let J := hJ.toFinset
  have hJK {t : ℝ} (ht : t ∈ J) : t ∈ K := (hJ.mem_toFinset.mp ht).1
  have hJae : ∀ᵐ t ∂μ.restrict K, t ∈ (J : Set ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU
      (h.ae_mem_jumps_on_binary_region isOpen_Ioo hfg hg hc hb),
      ae_restrict_mem hK.measurableSet] with t ht htK
    exact hJ.mem_toFinset.mpr ⟨htK, ht⟩
  have hsupp : Function.support (fun t : ℝ => ψ t * oneDimensionalJump g t) ⊆ J := by
    intro t ht
    have hn : ψ t * oneDimensionalJump g t ≠ 0 := ht
    have hψn : ψ t ≠ 0 := left_ne_zero_of_mul hn
    have hjn : oneDimensionalJump g t ≠ 0 := right_ne_zero_of_mul hn
    exact hJ.mem_toFinset.mpr ⟨hsψ hψn, hjn⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hrestrict : (∫ t in K, ψ t * σ t ∂μ) = ∫ t, ψ t * σ t ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [(show ψ t = 0 from by_contra fun hn => ht (hsψ hn)), zero_mul]
  rw [← hrestrict, integral_eq_setIntegral hJae (fun t => ψ t * σ t),
    setIntegral_finset J hq.integrableOn]
  apply Finset.sum_congr rfl
  intro t ht
  have hm : (μ.restrict K).real {t} = μ.real {t} := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (measurableSet_singleton t),
      singleton_inter_of_mem (hJK ht)]
  rw [hm, h.oneDimensionalJump_eq_atom hfg hc (hKU (hJK ht)), smul_eq_mul]
  ring

/-- Every compactly supported continuous test is exactly the weighted jump sum. -/
theorem IsRealBVPolar.integral_eq_finsum_jumps {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {a b : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) (hg : BoundedVariationOn g univ)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Ioo a b) :
    (∫ t, ψ t * σ t ∂μ) = ∑ᶠ t : ℝ, ψ t * oneDimensionalJump g t := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (tsupport ψ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hcψ.measure_lt_top⟩
  have hσ : IntegrableOn σ (tsupport ψ) μ :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun s hs => by simpa only [Real.norm_eq_abs] using hs.le)
  apply h.integral_eq_finsum_jumps_of_support hfg hg hc hb hcψ hsψ (subset_tsupport ψ)
  simpa only [mul_comm] using hσ.mul_continuousOn hψ.continuousOn hcψ

/-- On every Borel subset of a compact subinterval, the actual signed derivative
measure equals the sum of the canonical jumps in that set. -/
theorem IsRealBVPolar.setIntegral_eq_finsum_jumps {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {a b : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) (hg : BoundedVariationOn g univ)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ))
    {K A : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ Ioo a b)
    (hA : MeasurableSet A) (hAK : A ⊆ K) :
    (∫ t in A, σ t ∂μ) = ∑ᶠ t : ℝ, A.indicator (oneDimensionalJump g) t := by
  classical
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hσ : IntegrableOn σ K μ :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun s hs => by simpa only [Real.norm_eq_abs] using hs.le)
  have hs : Function.support (A.indicator (fun _ => (1 : ℝ))) ⊆ K :=
    support_indicator_subset.trans hAK
  have hi : IntegrableOn (fun t => A.indicator (fun _ => (1 : ℝ)) t * σ t) K μ := by
    simpa only [← indicator_mul_left, one_mul] using hσ.indicator hA
  have he := h.integral_eq_finsum_jumps_of_support hfg hg hc hb hK hKU hs hi
  simpa only [← indicator_mul_left, one_mul, integral_indicator hA] using he

/-- The distributional derivative on an interval is exactly the signed jump sum. -/
theorem IsRealBVPolar.test_eq_finsum_jumps {f σ g : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {a b : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) (hg : BoundedVariationOn g univ)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Ioo a b) :
    -(∫ t, f t * deriv ψ t) = ∑ᶠ t : ℝ, ψ t * oneDimensionalJump g t := by
  rw [h.test_eq ψ hψ hcψ]
  exact h.integral_eq_finsum_jumps hfg hg hc hb hψ.continuous hcψ hsψ

end LiquidDrop
