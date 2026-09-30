module

public import NoCompromise.Elliptic.ClassicalNormalGeometry

@[expose] public section

/-!
# The classical outward normal of a C¹ domain

The normal is chosen from a boundary chart and is zero away from the frontier.
Pointwise geometric chart compatibility makes the boundary restriction
continuous and independent of the chosen chart.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The classical outward unit normal on the topological boundary, extended by
zero off the boundary. Its definition uses only one-sided C¹ graph charts. -/
def HasC1Boundary.outwardNormal {D : Set AmbientSpace} (h : HasC1Boundary D)
    (z : AmbientSpace) : AmbientSpace := by
  classical
  exact if hz : z ∈ frontier D then (h z hz).choose.outwardNormal z else 0

lemma HasC1Boundary.outwardNormal_eq_zero {D : Set AmbientSpace} (h : HasC1Boundary D)
    {z : AmbientSpace} (hz : z ∉ frontier D) : h.outwardNormal z = 0 := by
  simp only [HasC1Boundary.outwardNormal, dite_eq_right hz]

/-- On every valid boundary chart the chosen normal equals the graph normal
at every boundary point, rather than merely almost everywhere. -/
theorem HasC1Boundary.outwardNormal_eq_chart {D : Set AmbientSpace} (h : HasC1Boundary D)
    {c : C1BoundaryChart} (hc : c.IsChartFor D) {z : AmbientSpace}
    (hz : z ∈ frontier D) (hzc : z ∈ c.region) : h.outwardNormal z = c.outwardNormal z := by
  rw [HasC1Boundary.outwardNormal, dite_eq_left hz]
  exact (h z hz).choose_spec.1.outwardNormal_agree hc hz (h z hz).choose_spec.2 hzc

lemma HasC1Boundary.norm_outwardNormal {D : Set AmbientSpace} (h : HasC1Boundary D)
    {z : AmbientSpace} (hz : z ∈ frontier D) : ‖h.outwardNormal z‖ = 1 := by
  rw [HasC1Boundary.outwardNormal, dite_eq_left hz]
  exact C1BoundaryChart.norm_outwardNormal _ _

lemma HasC1Boundary.norm_outwardNormal_le {D : Set AmbientSpace} (h : HasC1Boundary D)
    (z : AmbientSpace) : ‖h.outwardNormal z‖ ≤ 1 := by
  by_cases hz : z ∈ frontier D
  · exact (h.norm_outwardNormal hz).le
  · simp [h.outwardNormal_eq_zero hz]

theorem HasC1Boundary.continuousOn_outwardNormal {D : Set AmbientSpace}
    (h : HasC1Boundary D) : ContinuousOn h.outwardNormal (frontier D) := by
  intro z hz
  obtain ⟨c, hc, hzc⟩ := h z hz
  apply c.continuous_outwardNormal.continuousAt.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (c.isOpen_region.mem_nhds hzc),
      self_mem_nhdsWithin] with y hyc hy
    exact h.outwardNormal_eq_chart hc hy hyc
  · exact h.outwardNormal_eq_chart hc hz hzc

/-- The zero extension of the classical boundary normal is Borel measurable. -/
theorem HasC1Boundary.measurable_outwardNormal {D : Set AmbientSpace}
    (h : HasC1Boundary D) : Measurable h.outwardNormal := by
  classical
  have hm := h.continuousOn_outwardNormal.measurable_piecewise
    (continuousOn_const (c := (0 : AmbientSpace))) isClosed_frontier.measurableSet
  have heq : (frontier D).piecewise h.outwardNormal (fun _ => 0) = h.outwardNormal := by
    funext z
    by_cases hz : z ∈ frontier D
    · simp only [piecewise_eq_of_mem _ _ _ hz]
    · simp only [piecewise_eq_of_notMem _ _ _ hz, h.outwardNormal_eq_zero hz]
  rwa [heq] at hm

lemma HasC1Boundary.aestronglyMeasurable_outwardNormal {D : Set AmbientSpace}
    (h : HasC1Boundary D) (μ : Measure AmbientSpace) : AEStronglyMeasurable h.outwardNormal μ :=
  h.measurable_outwardNormal.aestronglyMeasurable

lemma HasC1Boundary.outwardNormal_eq_chart_ae {D : Set AmbientSpace} (h : HasC1Boundary D)
    {c : C1BoundaryChart} (hc : c.IsChartFor D) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier D),
      z ∈ c.region → h.outwardNormal z = c.outwardNormal z := by
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz hzc
  exact h.outwardNormal_eq_chart hc hz hzc

end LiquidDrop
