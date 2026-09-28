import NoCompromise.BV.BoundaryCut
import NoCompromise.BV.TraceReflection
import NoCompromise.BV.ExteriorGeometry

/-!
# Interior and exterior BV traces on a compact C¹ boundary

Reflected graph charts identify the exterior's interior trace with the original
upper trace. Both global cut formulas use the same geometric outward normal.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma C1BoundaryChart.exteriorChart_lowerBVTrace (c : C1BoundaryChart)
    (f : AmbientSpace → ℝ) (z : AmbientSpace) :
    c.exteriorChart.lowerBVTrace f z = c.upperBVTrace f z := by
  unfold lowerBVTrace upperBVTrace
  rw [c.exteriorChart_symm_apply]
  change graphBVLowerTrace ((f ∘ c.placement) ∘ coordinateReflection (Fin.last 2))
    (fun x => -c.height x) (coordinateReflection (Fin.last 2) (c.placement.symm z)) = _
  exact graphBVLowerTrace_reflect (f ∘ c.placement) c.height (c.placement.symm z)

lemma C1BoundaryChart.exteriorChart_upperBVTrace (c : C1BoundaryChart)
    (f : AmbientSpace → ℝ) (z : AmbientSpace) :
    c.exteriorChart.upperBVTrace f z = c.lowerBVTrace f z := by
  unfold lowerBVTrace upperBVTrace
  rw [c.exteriorChart_symm_apply]
  change graphBVUpperTrace ((f ∘ c.placement) ∘ coordinateReflection (Fin.last 2))
    (fun x => -c.height x) (coordinateReflection (Fin.last 2) (c.placement.symm z)) = _
  exact graphBVUpperTrace_reflect (f ∘ c.placement) c.height (c.placement.symm z)

/-- Geometric normal agreement in all charts determines one boundary field up
to surface-area null sets. -/
lemma HasC1Boundary.normal_eq_ae_of_chart_agreement {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hK : IsCompact (frontier E))
    {ν τ : AmbientSpace → AmbientSpace}
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        ν z = c.outwardNormal z)
    (hτ : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        τ z = c.outwardNormal z) :
    ν =ᵐ[(hausdorffMeasure2 3).restrict (frontier E)] τ := by
  classical
  obtain ⟨l, hl, hcover⟩ := h.exists_finite_chart_list hK
  have hc : ∀ c : l.toFinset,
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.val.region → ν z = τ z := by
    intro c
    have hh := hl c.val (List.mem_toFinset.mp c.property)
    filter_upwards [hν c.val hh, hτ c.val hh] with z hz hz'
    intro hzc
    exact (hz hzc).trans (hz' hzc).symm
  filter_upwards [ae_all_iff.mpr hc,
    ae_restrict_mem isClosed_frontier.measurableSet] with z hz hzf
  obtain ⟨c, hcl, hzc⟩ := hcover z hzf
  exact hz ⟨c, List.mem_toFinset.mpr hcl⟩ hzc

/-- Interior and exterior traces, identified with the essential chart traces,
satisfy both exact distributional product formulas with one outward normal. -/
theorem HasC1Boundary.exists_integrable_traces_cut_pairings {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hK : IsCompact (frontier E))
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure AmbientSpace} [SigmaFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ) :
    ∃ Tin Tout : AmbientSpace → ℝ, ∃ ν : AmbientSpace → AmbientSpace,
      Integrable Tin ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      Integrable Tout ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      Measurable ν ∧
      (∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ = 1) ∧
      (∀ c : C1BoundaryChart, c.IsChartFor E →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
          Tin z = c.lowerBVTrace f z ∧ Tout z = c.upperBVTrace f z ∧
            ν z = c.outwardNormal z) ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z in E, f z * divergenceN X z) =
          -(∫ z in E, inner ℝ (X z) (σ z) ∂μ) +
            ∫ z, Tin z * inner ℝ (X z) (ν z)
              ∂(hausdorffMeasure2 3).restrict (frontier E)) ∧
      ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z in (closure E)ᶜ, f z * divergenceN X z) =
          -(∫ z in (closure E)ᶜ, inner ℝ (X z) (σ z) ∂μ) -
            ∫ z, Tout z * inner ℝ (X z) (ν z)
              ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  obtain ⟨Tin, ν, hi, hνm, hn, hiC, hνC, hinside⟩ :=
    h.exists_integrable_trace_cut_pairing hE hK hf hσ hpair
  have hKe : IsCompact (frontier (closure E)ᶜ) := h.frontier_exterior.symm ▸ hK
  obtain ⟨Tout, τ, ho, _, _, hoC, hτC, houtside⟩ :=
    h.exterior.exists_integrable_trace_cut_pairing isClosed_closure.isOpen_compl
      hKe hf hσ hpair
  rw [h.frontier_exterior] at ho hoC hτC houtside
  have houtC (c : C1BoundaryChart) (hc : c.IsChartFor E) :
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        Tout z = c.upperBVTrace f z := by
    simpa only [C1BoundaryChart.exteriorChart_lowerBVTrace] using! hoC c.exteriorChart hc.exterior
  have heq : ν =ᵐ[(hausdorffMeasure2 3).restrict (frontier E)] (fun z => -τ z) :=
    h.normal_eq_ae_of_chart_agreement hK hνC (by
      intro c hc
      filter_upwards [hτC c.exteriorChart hc.exterior] with z hz
      intro hzc
      rw [hz hzc, c.exteriorChart_outwardNormal, neg_neg])
  refine ⟨Tin, Tout, ν, hi, ho, hνm, hn, ?_, hinside, ?_⟩
  · intro c hc
    filter_upwards [hiC c hc, houtC c hc, hνC c hc] with z hiZ hoZ hνZ
    intro hzc
    exact ⟨hiZ hzc, hoZ hzc, hνZ hzc⟩
  · intro X hX hcX
    rw [houtside X hX hcX]
    have he : (∫ z, Tout z * inner ℝ (X z) (τ z)
        ∂(hausdorffMeasure2 3).restrict (frontier E)) =
        -(∫ z, Tout z * inner ℝ (X z) (ν z)
          ∂(hausdorffMeasure2 3).restrict (frontier E)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      rw [hz, inner_neg_right, mul_neg, neg_neg]
    rw [he, sub_eq_add_neg]

/-- Blueprint `thm:traces`: bounded open C¹ domains have genuine integrable
interior and exterior traces, and both distributional cut identities hold.
The ambient derivative representation is constructed from local BV regularity. -/
theorem bv_traces_on_bounded_C1_domain {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hbE : Bornology.IsBounded E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ μ : Measure AmbientSpace, ∃ σ : AmbientSpace → AmbientSpace,
      μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧ Measurable σ ∧
      (∀ᵐ z ∂μ, ‖σ z‖ = 1) ∧ LocallyIntegrable σ μ ∧
      (∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
        ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
          ∫ z, φ z * σ z i ∂μ) ∧
      (∀ U : Set AmbientSpace, IsOpen U → variation f U = μ U) ∧
      ∃ Tin Tout : AmbientSpace → ℝ, ∃ ν : AmbientSpace → AmbientSpace,
        Integrable Tin ((hausdorffMeasure2 3).restrict (frontier E)) ∧
        Integrable Tout ((hausdorffMeasure2 3).restrict (frontier E)) ∧
        Measurable ν ∧
        (∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ = 1) ∧
        (∀ c : C1BoundaryChart, c.IsChartFor E →
          ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
            Tin z = c.lowerBVTrace f z ∧ Tout z = c.upperBVTrace f z ∧
              ν z = c.outwardNormal z) ∧
        (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
          (∫ z in E, f z * divergenceN X z) =
            -(∫ z in E, inner ℝ (X z) (σ z) ∂μ) +
              ∫ z, Tin z * inner ℝ (X z) (ν z)
                ∂(hausdorffMeasure2 3).restrict (frontier E)) ∧
        ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
          (∫ z in (closure E)ᶜ, f z * divergenceN X z) =
            -(∫ z in (closure E)ᶜ, inner ℝ (X z) (σ z) ∂μ) -
              ∫ z, Tout z * inner ℝ (X z) (ν z)
                ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  obtain ⟨μ, σ, hμ, hμfin, hσm, hσn, hσ, hpair, hvar⟩ := hf.exists_ambient_scalar_polar
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  refine ⟨μ, σ, hμ, hμfin, hσm, hσn, hσ, hpair, hvar, ?_⟩
  exact h.exists_integrable_traces_cut_pairings hE
    (hbE.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    hf hσ hpair

end LiquidDrop
