import NoCompromise.BV.TraceAgreement

/-!
# A single integrable trace on a compact C¹ boundary

A finite chart list covers the compact boundary. Choosing the first chart that
contains a point gives one trace, and the proved overlap agreement identifies
it almost everywhere with every valid local chart trace.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasC1Boundary.exists_finite_chart_list {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hK : IsCompact (frontier E)) :
    ∃ l : List C1BoundaryChart, (∀ c ∈ l, c.IsChartFor E) ∧
      ∀ z ∈ frontier E, ∃ c ∈ l, z ∈ c.region := by
  classical
  let I := {c : C1BoundaryChart // c.IsChartFor E}
  let V : I → Set AmbientSpace := fun c => c.val.region
  have hcover : frontier E ⊆ ⋃ c : I, V c := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := h z hz
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hzc⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V (fun c => c.val.isOpen_region) hcover
  refine ⟨s.toList.map Subtype.val, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
    exact d.property
  · intro z hz
    obtain ⟨c, hcs, hzc⟩ := mem_iUnion₂.mp (hs hz)
    exact ⟨c.val, List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hcs, rfl⟩, hzc⟩

/-- The first available chart supplies the trace; zero is used off the atlas. -/
def lowerBoundaryAtlasTrace (f : AmbientSpace → ℝ) : List C1BoundaryChart → AmbientSpace → ℝ
  | [], _ => 0
  | c :: l, z => @ite ℝ (z ∈ c.region) (Classical.propDecidable _)
      (c.lowerBVTrace f z) (lowerBoundaryAtlasTrace f l z)

lemma integrable_lowerBoundaryAtlasTrace {E : Set AmbientSpace}
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) (l : List C1BoundaryChart)
    (hl : ∀ c ∈ l, c.IsChartFor E) :
    Integrable (lowerBoundaryAtlasTrace f l) ((hausdorffMeasure2 3).restrict (frontier E)) := by
  classical
  induction l with
  | nil => exact integrable_zero _ _ _
  | cons c l ih =>
      have hc : c.IsChartFor E := hl c (by simp)
      have hit := ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      have hic : Integrable (c.region.indicator (c.lowerBVTrace f))
          ((hausdorffMeasure2 3).restrict (frontier E)) :=
        (integrable_indicator_iff c.isOpen_region.measurableSet).mpr
          (hc.integrableOn_BVTraces hf).1
      have he : lowerBoundaryAtlasTrace f (c :: l) = fun z =>
          c.region.indicator (c.lowerBVTrace f) z +
            c.regionᶜ.indicator (lowerBoundaryAtlasTrace f l) z := by
        funext z
        by_cases hz : z ∈ c.region <;> simp [lowerBoundaryAtlasTrace, hz]
      rw [he]
      exact hic.add (hit.indicator c.isOpen_region.measurableSet.compl)

lemma lowerBoundaryAtlasTrace_agree_ae {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    (l : List C1BoundaryChart) (hl : ∀ c ∈ l, c.IsChartFor E)
    (c : C1BoundaryChart) (hc : c.IsChartFor E) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
      (∃ d ∈ l, z ∈ d.region) → lowerBoundaryAtlasTrace f l z = c.lowerBVTrace f z := by
  induction l with
  | nil =>
      exact ae_of_all _ fun z _ hz => by
        obtain ⟨d, hd, _⟩ := hz
        simp at hd
  | cons d l ih =>
      have hd : d.IsChartFor E := hl d (by simp)
      have ht := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
      filter_upwards [hd.lowerBVTrace_agree_ae hc h hE hf, ht] with z hz htZ
      intro hzc hcover
      by_cases hzd : z ∈ d.region
      · simpa only [lowerBoundaryAtlasTrace, ite_eq_left hzd] using hz ⟨hzd, hzc⟩
      · simp only [lowerBoundaryAtlasTrace, ite_eq_right hzd]
        apply htZ hzc
        obtain ⟨e, he, hze⟩ := hcover
        rcases List.mem_cons.mp he with rfl | he
        · exact (hzd hze).elim
        · exact ⟨e, he, hze⟩

/-- A compact C¹ boundary carries one genuine L¹ interior trace, agreeing with
all the constructed local chart traces on their respective boundary patches. -/
theorem HasC1Boundary.exists_integrable_lowerTrace {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hK : IsCompact (frontier E))
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ T : AmbientSpace → ℝ, Integrable T ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      ∀ c : C1BoundaryChart, c.IsChartFor E →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E),
          z ∈ c.region → T z = c.lowerBVTrace f z := by
  obtain ⟨l, hl, hcover⟩ := h.exists_finite_chart_list hK
  refine ⟨lowerBoundaryAtlasTrace f l, integrable_lowerBoundaryAtlasTrace hf l hl, ?_⟩
  intro c hc
  filter_upwards [lowerBoundaryAtlasTrace_agree_ae h hE hf l hl c hc,
    ae_restrict_mem (isClosed_frontier : IsClosed (frontier E)).measurableSet] with z hz hzf
  intro hzc
  exact hz hzc (hcover z hzf)

theorem HasC1Boundary.exists_integrable_lowerTrace_of_bounded {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hbE : Bornology.IsBounded E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ T : AmbientSpace → ℝ, Integrable T ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      ∀ c : C1BoundaryChart, c.IsChartFor E →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E),
          z ∈ c.region → T z = c.lowerBVTrace f z :=
  h.exists_integrable_lowerTrace hE
    (hbE.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure) hf

end LiquidDrop
