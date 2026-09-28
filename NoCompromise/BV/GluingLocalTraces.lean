import NoCompromise.BV.BoundaryTraces
import NoCompromise.BV.GraphCutPerimeter

/-!
# Traces for functions which are BV only near the gluing boundary

Compact localization preserves the actual essential chart traces. In particular
BV regularity on the given open domain suffices for the boundary mismatch term;
no global BV hypothesis is imposed on the original functions.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma bvTraces_congr_nhds {f g : ℝ → ℝ} {a : ℝ} (he : f =ᶠ[𝓝 a] g) :
    bvLeftTrace f a = bvLeftTrace g a ∧ bvRightTrace f a = bvRightTrace g a := by
  classical
  have hl : f =ᶠ[bvTraceLeftFilter a] g :=
    he.filter_mono (inf_le_left.trans (nhdsWithin_le_nhds (s := Iio a)))
  have hr : f =ᶠ[bvTraceRightFilter a] g :=
    he.filter_mono (inf_le_left.trans (nhdsWithin_le_nhds (s := Ioi a)))
  constructor
  · by_cases hf : ∃ L, HasBVLeftTrace f a L
    · obtain ⟨L, hL⟩ := hf
      exact hL.eq_bvLeftTrace.trans
        ((show HasBVLeftTrace g a L from hL.congr' hl).eq_bvLeftTrace.symm)
    · have hg : ¬∃ L, HasBVLeftTrace g a L := by
        rintro ⟨L, hL⟩
        exact hf ⟨L, hL.congr' hl.symm⟩
      simp only [bvLeftTrace, dite_eq_right hf, dite_eq_right hg]
  · by_cases hf : ∃ L, HasBVRightTrace f a L
    · obtain ⟨L, hL⟩ := hf
      exact hL.eq_bvRightTrace.trans
        ((show HasBVRightTrace g a L from hL.congr' hr).eq_bvRightTrace.symm)
    · have hg : ¬∃ L, HasBVRightTrace g a L := by
        rintro ⟨L, hL⟩
        exact hf ⟨L, hL.congr' hr.symm⟩
      simp only [bvRightTrace, dite_eq_right hf, dite_eq_right hg]

/-- A chart trace depends only on values in any neighborhood of its boundary point. -/
lemma C1BoundaryChart.bvTraces_congr_nhds (c : C1BoundaryChart)
    {f g : AmbientSpace → ℝ} {z : AmbientSpace} (hz : z ∈ c.graphSurface)
    (he : f =ᶠ[𝓝 z] g) :
    c.lowerBVTrace f z = c.lowerBVTrace g z ∧
      c.upperBVTrace f z = c.upperBVTrace g z := by
  obtain ⟨w, ⟨x, rfl⟩, rfl⟩ := hz
  have ht : Tendsto (fun t : ℝ => c.placement (graphAppendN x (t + c.height x)))
      (𝓝 0) (𝓝 (c.placement (graphMapN c.height x))) := by
    have hc : Continuous (fun t : ℝ =>
        c.placement (realLineCoordinates 2 (x, t + c.height x))) :=
      c.placement.continuous.comp ((realLineCoordinates 2).continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)))
    simpa only [realLineCoordinates_apply, zero_add] using! hc.tendsto 0
  have hh := LiquidDrop.bvTraces_congr_nhds (he.comp_tendsto ht)
  simpa only [C1BoundaryChart.lowerBVTrace, C1BoundaryChart.upperBVTrace,
    graphBVLowerTrace, graphBVUpperTrace, Function.comp_def,
    c.placement.symm_apply_apply,
    show graphMapN c.height x = graphAppendN x (c.height x) from rfl,
    graphProjectionN_append] using! hh

/-- A locally BV function on an open domain has a global BV realization agreeing
with it on a neighborhood of any prescribed compact subset. -/
theorem IsLocallyBVOn.exists_globalBV_eq_near_compact {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn g univ ∧ f =ᶠ[𝓝ˢ K] g := by
  obtain ⟨ζ, hζ, hcζ, hsζ, hζone, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  refine ⟨fun z => ζ z * f z,
    hf.isBVOn_mul_compact_factor hU (hζ.of_le (by simp)) hcζ hsζ, ?_⟩
  filter_upwards [hζone] with z hz
  simp only [hz, one_mul]

/-- The two actual traces exist and are integrable under BV regularity only in
an open neighborhood of the compact closure of the gluing domain. -/
theorem HasC1Boundary.exists_integrable_traces_of_locallyBVOn
    {A U : Set AmbientSpace} (h : HasC1Boundary A) (hA : IsOpen A)
    (hbA : Bornology.IsBounded A) (hU : IsOpen U) (hAU : closure A ⊆ U)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ Tin Tout : AmbientSpace → ℝ, ∃ ν : AmbientSpace → AmbientSpace,
      Integrable Tin ((hausdorffMeasure2 3).restrict (frontier A)) ∧
      Integrable Tout ((hausdorffMeasure2 3).restrict (frontier A)) ∧ Measurable ν ∧
      (∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), ‖ν z‖ = 1) ∧
      ∀ c : C1BoundaryChart, c.IsChartFor A →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
          Tin z = c.lowerBVTrace f z ∧ Tout z = c.upperBVTrace f z ∧
            ν z = c.outwardNormal z := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_globalBV_eq_near_compact hU hbA.isCompact_closure hAU
  have hgl := isLocallyBVOn_of_variation_lt_top isOpen_univ hg.1.locallyIntegrableOn hg.2
  obtain ⟨μ, σ, _, _, _, _, _, _, _, Tin, Tout, ν,
    hTi, hTo, hνm, hn, hchart, _, _⟩ := bv_traces_on_bounded_C1_domain h hA hbA hgl
  refine ⟨Tin, Tout, ν, hTi, hTo, hνm, hn, fun c hc => ?_⟩
  filter_upwards [hchart c hc, ae_restrict_mem isClosed_frontier.measurableSet] with z hz hzA
  intro hzc
  have hzs : z ∈ c.graphSurface := by
    have hx : z ∈ frontier A ∩ c.region := ⟨hzA, hzc⟩
    rw [hc.frontier_inter_eq] at hx
    exact hx.1
  have he := c.bvTraces_congr_nhds hzs
    (hfg.filter_mono (nhds_le_nhdsSet (frontier_subset_closure hzA)))
  exact ⟨(hz hzc).1.trans he.1.symm, (hz hzc).2.1.trans he.2.symm, (hz hzc).2.2⟩

/-- A compact C¹ boundary is null for ambient volume. -/
lemma HasC1Boundary.volume_frontier_eq_zero {A : Set AmbientSpace}
    (h : HasC1Boundary A) (hK : IsCompact (frontier A)) : volume (frontier A) = 0 := by
  obtain ⟨l, hl, hcover⟩ := h.exists_finite_chart_list hK
  have hs : frontier A ⊆ ⋃ c ∈ l, c.graphSurface := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    have ht : z ∈ frontier A ∩ c.region := ⟨hz, hzc⟩
    rw [(hl c hc).frontier_inter_eq] at ht
    exact mem_iUnion₂.mpr ⟨c, hc, ht.1⟩
  apply measure_mono_null hs
  apply measure_biUnion_null_iff (l.finite_toSet.countable) |>.mpr
  intro c _
  exact c.volume_graphSurface

/-- Agreement with the same actual chart traces determines a boundary function
up to surface-area null sets. -/
lemma HasC1Boundary.trace_eq_ae_of_chart_agreement {A : Set AmbientSpace}
    (h : HasC1Boundary A) (hK : IsCompact (frontier A))
    {T S : AmbientSpace → ℝ} {L : C1BoundaryChart → AmbientSpace → ℝ}
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region → T z = L c z)
    (hS : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region → S z = L c z) :
    T =ᵐ[(hausdorffMeasure2 3).restrict (frontier A)] S := by
  apply h.ae_of_chartwise hK
  intro c hc
  filter_upwards [hT c hc, hS c hc] with z hz hz'
  exact fun hzc => (hz hzc).trans (hz' hzc).symm

end LiquidDrop
