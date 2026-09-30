module

public import NoCompromise.BV.GluingGlobal

@[expose] public section

/-!
# Gluing inside an open domain

The BV hypotheses hold only in the specified open set. Each compact test is
localized jointly with the gluing interface; locality of the genuine traces
makes the resulting boundary mismatch independent of that localization.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The raw BV gluing estimate on an open set, with no regularity assumption
outside that set. -/
theorem HasC1Boundary.variation_gluing_on_open_le {A U : Set AmbientSpace}
    (h : HasC1Boundary A) (hA : IsOpen A) (hbA : Bornology.IsBounded A)
    (hU : IsOpen U) (hAU : closure A ⊆ U)
    {f g : AmbientSpace → ℝ} (hf : IsLocallyBVOn f U) (hg : IsLocallyBVOn g U)
    {Tin Tout : AmbientSpace → ℝ}
    (hTi : Integrable Tin ((hausdorffMeasure2 3).restrict (frontier A)))
    (hTo : Integrable Tout ((hausdorffMeasure2 3).restrict (frontier A)))
    (hTic : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tin z = c.lowerBVTrace g z)
    (hToc : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tout z = c.upperBVTrace f z) :
    variation (fun z => A.indicator g z + (U \ closure A).indicator f z) U ≤
      variation g A + variation f (U \ closure A) +
        ENNReal.ofReal (∫ z in frontier A, |Tin z - Tout z| ∂hausdorffMeasure2 3) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  let K := closure A ∪ tsupport X
  have hK : IsCompact K := hbA.isCompact_closure.union hX.2.1
  have hKU : K ⊆ U := union_subset hAU hX.2.2.1
  obtain ⟨f', hf', hff'⟩ := hf.exists_globalBV_eq_near_compact hU hK hKU
  obtain ⟨g', hg', hgg'⟩ := hg.exists_globalBV_eq_near_compact hU hK hKU
  have heU : ∀ᶠ z in 𝓝ˢ K, z ∈ U := hU.mem_nhdsSet.mpr hKU
  obtain ⟨V, hV, hKV, hVgood⟩ := mem_nhdsSet_iff_exists.mp (hff'.and (hgg'.and heU))
  have hVU : V ⊆ U := fun z hz => (hVgood hz).2.2
  have hAV : A ⊆ V := fun z hz => hKV (Or.inl (subset_closure hz))
  have htr {q q' : AmbientSpace → ℝ} (heq : q =ᶠ[𝓝ˢ K] q')
      (c : C1BoundaryChart) (hc : c.IsChartFor A) :
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        c.lowerBVTrace q z = c.lowerBVTrace q' z ∧
          c.upperBVTrace q z = c.upperBVTrace q' z := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
    intro hzc
    have hzs : z ∈ c.graphSurface := by
      have ht : z ∈ frontier A ∩ c.region := ⟨hz, hzc⟩
      rw [hc.frontier_inter_eq] at ht
      exact ht.1
    exact c.bvTraces_congr_nhds hzs
      (heq.filter_mono (nhds_le_nhdsSet (Or.inl (frontier_subset_closure hz))))
  have hTig : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tin z = c.lowerBVTrace g' z := by
    intro c hc
    filter_upwards [hTic c hc, htr hgg' c hc] with z hz hez
    exact fun hzc => (hz hzc).trans (hez hzc).1
  have hTof : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tout z = c.upperBVTrace f' z := by
    intro c hc
    filter_upwards [hToc c hc, htr hff' c hc] with z hz hez
    exact fun hzc => (hz hzc).trans (hez hzc).2
  have hbound := h.variation_gluing_le hA hbA
    (isLocallyBVOn_of_variation_lt_top isOpen_univ hf'.1.locallyIntegrableOn hf'.2)
    (isLocallyBVOn_of_variation_lt_top isOpen_univ hg'.1.locallyIntegrableOn hg'.2)
    hTi hTo hTig hTof hV
  have hgeq : variation g' (V ∩ A) = variation g A := by
    rw [inter_eq_right.mpr hAV]
    apply variation_congr_ae
    filter_upwards [ae_restrict_mem hA.measurableSet] with z hz
    exact (hVgood (hAV hz)).2.1.symm
  have hfeq : variation f' (V ∩ (closure A)ᶜ) = variation f (V ∩ (closure A)ᶜ) := by
    apply variation_congr_ae
    filter_upwards [ae_restrict_mem (hV.inter isClosed_closure.isOpen_compl).measurableSet]
      with z hz
    exact (hVgood hz.1).1.symm
  have hw : (fun z => A.indicator g z + (U \ closure A).indicator f z) =ᵐ[volume.restrict V]
      (fun z => A.indicator g' z + (closure A)ᶜ.indicator f' z) := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    obtain ⟨hfe, hge, hzu⟩ := hVgood hz
    by_cases hza : z ∈ A
    · have hzc := subset_closure hza
      simp [hza, hzc, hge]
    · by_cases hzc : z ∈ closure A <;> simp [hza, hzc, hzu, hfe]
  have hXV : IsVariationTestField V X :=
    ⟨hX.1, hX.2.1, fun z hz => hKV (Or.inr hz), hX.2.2.2⟩
  have hint : (∫ z in U, (A.indicator g z + (U \ closure A).indicator f z) * divergenceN X z) =
      ∫ z in V, (A.indicator g z + (U \ closure A).indicator f z) * divergenceN X z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU
    intro z hz
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun hzs => hz.2 (hXV.2.2.1 hzs)), mul_zero]
  calc
    _ = ENNReal.ofReal (∫ z in V,
        (A.indicator g z + (U \ closure A).indicator f z) * divergenceN X z) :=
      congrArg ENNReal.ofReal hint
    _ ≤ variation (fun z => A.indicator g z + (U \ closure A).indicator f z) V :=
      le_iSup_of_le X (le_iSup_of_le hXV le_rfl)
    _ = variation (fun z => A.indicator g' z + (closure A)ᶜ.indicator f' z) V :=
      variation_congr_ae V hw
    _ ≤ _ := hbound
    _ ≤ _ := by
      rw [hgeq, hfeq]
      apply add_le_add _ le_rfl
      apply add_le_add le_rfl
      apply variation_mono (hU.inter isClosed_closure.isOpen_compl).measurableSet
      exact fun z hz => ⟨hVU hz.1, hz.2⟩

/-- Blueprint `prop:gluing`. The two indicator functions need only be locally
BV in `U`, and the returned traces are the genuine essential boundary traces. -/
theorem bv_gluing_on_open {A U E F : Set AmbientSpace}
    (h : HasC1Boundary A) (hA : IsOpen A) (hbA : Bornology.IsBounded A)
    (hU : IsOpen U) (hAU : closure A ⊆ U)
    (hE : IsLocallyBVOn (E.indicator (fun _ => (1 : ℝ))) U)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U) :
    ∃ Tin Tout : AmbientSpace → ℝ,
      Integrable Tin ((hausdorffMeasure2 3).restrict (frontier A)) ∧
      Integrable Tout ((hausdorffMeasure2 3).restrict (frontier A)) ∧
      (∀ c : C1BoundaryChart, c.IsChartFor A →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
          Tin z = c.lowerBVTrace (F.indicator (fun _ => (1 : ℝ))) z ∧
          Tout z = c.upperBVTrace (E.indicator (fun _ => (1 : ℝ))) z) ∧
      perimeterIn ((F ∩ A) ∪ (E ∩ (U \ A))) U ≤
        perimeterIn F A + perimeterIn E (U \ closure A) +
          ENNReal.ofReal (∫ z in frontier A, |Tin z - Tout z| ∂hausdorffMeasure2 3) := by
  obtain ⟨Tin, _, _, hTi, _, _, _, hTcF⟩ :=
    h.exists_integrable_traces_of_locallyBVOn hA hbA hU hAU hF
  obtain ⟨_, Tout, _, _, hTo, _, _, hTcE⟩ :=
    h.exists_integrable_traces_of_locallyBVOn hA hbA hU hAU hE
  have hTic : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tin z = c.lowerBVTrace (F.indicator (fun _ => (1 : ℝ))) z :=
    fun c hc => (hTcF c hc).mono fun z hz hzc => (hz hzc).1
  have hToc : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tout z = c.upperBVTrace (E.indicator (fun _ => (1 : ℝ))) z :=
    fun c hc => (hTcE c hc).mono fun z hz hzc => (hz hzc).2.1
  refine ⟨Tin, Tout, hTi, hTo, ?_, ?_⟩
  · intro c hc
    filter_upwards [hTic c hc, hToc c hc] with z hi ho
    exact fun hz => ⟨hi hz, ho hz⟩
  · have hv := h.variation_gluing_on_open_le hA hbA hU hAU hE hF hTi hTo hTic hToc
    have hnull := h.volume_frontier_eq_zero
      (hbA.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    have he : ((F ∩ A) ∪ (E ∩ (U \ A))).indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U]
        (fun z => A.indicator (F.indicator (fun _ => (1 : ℝ))) z +
          (U \ closure A).indicator (E.indicator (fun _ => (1 : ℝ))) z) := by
      filter_upwards [ae_restrict_mem hU.measurableSet,
        ae_restrict_of_ae ((measure_eq_zero_iff_ae_notMem).mp hnull)] with z hzU hzA
      by_cases hza : z ∈ A
      · have hzc := subset_closure hza
        by_cases hzf : z ∈ F <;> simp [hza, hzc, hzf]
      · have hzc : z ∉ closure A := by
          intro hzcl
          apply hzA
          exact ⟨hzcl, by simpa only [hA.interior_eq] using hza⟩
        by_cases hze : z ∈ E <;> simp [hza, hzc, hzU, hze]
    exact (variation_congr_ae U he).le.trans hv

/-- The global set-gluing formula, valid even when a bulk perimeter is infinite. -/
theorem bv_gluing_global {A E F : Set AmbientSpace}
    (h : HasC1Boundary A) (hA : IsOpen A) (hbA : Bornology.IsBounded A)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume) :
    ∃ Tin Tout : AmbientSpace → ℝ,
      Integrable Tin ((hausdorffMeasure2 3).restrict (frontier A)) ∧
      Integrable Tout ((hausdorffMeasure2 3).restrict (frontier A)) ∧
      (∀ c : C1BoundaryChart, c.IsChartFor A →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
          Tin z = c.lowerBVTrace (F.indicator (fun _ => (1 : ℝ))) z ∧
          Tout z = c.upperBVTrace (E.indicator (fun _ => (1 : ℝ))) z) ∧
      perimeter ((F ∩ A) ∪ (E \ A)) ≤
        perimeterIn F A + perimeterIn E (closure A)ᶜ +
          ENNReal.ofReal (∫ z in frontier A, |Tin z - Tout z| ∂hausdorffMeasure2 3) := by
  obtain ⟨Tin, Tout, hi, ho, hc, hv⟩ := bv_gluing_on_open h hA hbA isOpen_univ
    (subset_univ _) (hE.isLocallyBVOn_indicator hmE univ) (hF.isLocallyBVOn_indicator hmF univ)
  refine ⟨Tin, Tout, hi, ho, hc, ?_⟩
  have hmH := (hmF.inter hA.measurableSet.nullMeasurableSet).union
    (hmE.diff hA.measurableSet.nullMeasurableSet)
  rw [← perimeterN_eq_perimeter _ hmH]
  simpa only [perimeterN, sdiff_eq, univ_inter] using hv

end LiquidDrop
