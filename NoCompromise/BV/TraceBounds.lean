import NoCompromise.BV.BoundaryTraces

/-!
# Closed-set bounds for genuine boundary traces

Canonical traces retain closed value constraints that contain the default zero.
Finite boundary atlases transfer these pointwise chart bounds to the actual
integrable interior and exterior traces.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma bvLeftTrace_mem_closed {f : ℝ → ℝ} {S : Set ℝ} (hS : IsClosed S)
    (h0 : (0 : ℝ) ∈ S) (hf : ∀ᵐ t : ℝ, f t ∈ S) (a : ℝ) : bvLeftTrace f a ∈ S := by
  classical
  by_cases hh : ∃ L, HasBVLeftTrace f a L
  · rw [hh.choose_spec.eq_bvLeftTrace]
    exact hh.choose_spec.mem_closed hS hf
  · rw [bvLeftTrace, dite_eq_right hh]
    exact h0

lemma bvRightTrace_mem_closed {f : ℝ → ℝ} {S : Set ℝ} (hS : IsClosed S)
    (h0 : (0 : ℝ) ∈ S) (hf : ∀ᵐ t : ℝ, f t ∈ S) (a : ℝ) : bvRightTrace f a ∈ S := by
  classical
  by_cases hh : ∃ L, HasBVRightTrace f a L
  · rw [hh.choose_spec.eq_bvRightTrace]
    exact hh.choose_spec.mem_closed hS hf
  · rw [bvRightTrace, dite_eq_right hh]
    exact h0

lemma C1BoundaryChart.lowerBVTrace_mem_closed (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} {S : Set ℝ} (hS : IsClosed S) (h0 : (0 : ℝ) ∈ S)
    (hf : ∀ x, f x ∈ S) (z : AmbientSpace) : c.lowerBVTrace f z ∈ S := by
  apply bvLeftTrace_mem_closed hS h0
  exact ae_of_all _ fun _ => hf _

lemma C1BoundaryChart.upperBVTrace_mem_closed (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} {S : Set ℝ} (hS : IsClosed S) (h0 : (0 : ℝ) ∈ S)
    (hf : ∀ x, f x ∈ S) (z : AmbientSpace) : c.upperBVTrace f z ∈ S := by
  apply bvRightTrace_mem_closed hS h0
  exact ae_of_all _ fun _ => hf _

/-- Local almost-everywhere boundary assertions patch across a compact C¹ atlas. -/
lemma HasC1Boundary.ae_of_chartwise {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hK : IsCompact (frontier E)) {P : AmbientSpace → Prop}
    (hP : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region → P z) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), P z := by
  classical
  obtain ⟨l, hl, hcover⟩ := h.exists_finite_chart_list hK
  have hc : ∀ c : l.toFinset,
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.val.region → P z :=
    fun c => hP c.val (hl c.val (List.mem_toFinset.mp c.property))
  filter_upwards [ae_all_iff.mpr hc,
    ae_restrict_mem isClosed_frontier.measurableSet] with z hz hzf
  obtain ⟨c, hcl, hzc⟩ := hcover z hzf
  exact hz ⟨c, List.mem_toFinset.mpr hcl⟩ hzc

lemma HasC1Boundary.lowerTrace_mem_closed_ae {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hK : IsCompact (frontier E))
    {f T : AmbientSpace → ℝ} {S : Set ℝ} (hS : IsClosed S) (h0 : (0 : ℝ) ∈ S)
    (hf : ∀ x, f x ∈ S)
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        T z = c.lowerBVTrace f z) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), T z ∈ S := by
  apply h.ae_of_chartwise hK
  intro c hc
  filter_upwards [hT c hc] with z hz
  intro hzc
  rw [hz hzc]
  exact c.lowerBVTrace_mem_closed hS h0 hf z

lemma HasC1Boundary.upperTrace_mem_closed_ae {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hK : IsCompact (frontier E))
    {f T : AmbientSpace → ℝ} {S : Set ℝ} (hS : IsClosed S) (h0 : (0 : ℝ) ∈ S)
    (hf : ∀ x, f x ∈ S)
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        T z = c.upperBVTrace f z) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), T z ∈ S := by
  apply h.ae_of_chartwise hK
  intro c hc
  filter_upwards [hT c hc] with z hz
  intro hzc
  rw [hz hzc]
  exact c.upperBVTrace_mem_closed hS h0 hf z

end LiquidDrop
