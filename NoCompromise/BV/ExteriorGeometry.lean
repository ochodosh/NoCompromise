module

public import NoCompromise.DeGiorgi.SmoothBoundary
public import NoCompromise.Sobolev.Extension

@[expose] public section

/-!
# Exterior charts for C¹ domains

Reflecting the final coordinate and negating the graph height gives a genuine
chart for the complement of the closure. The exterior has the same frontier.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient
namespace LiquidDrop

lemma mem_closure_smoothSubgraph_iff {k : ℕ}
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g)
    (z : EuclideanSpace ℝ (Fin (k + 1))) :
    z ∈ closure (smoothSubgraph g) ↔ z (Fin.last k) ≤ g (graphProjectionN k z) := by
  rw [closure_eq_self_union_frontier, frontier_smoothSubgraph hg]
  constructor
  · rintro (hz | ⟨x, rfl⟩)
    · exact hz.le
    · rw [graphMapN_last]
      change g x ≤ g (graphProjectionN k (graphAppendN x (g x)))
      simp
  · intro hz
    rcases hz.lt_or_eq with hz | hz
    · exact Or.inl hz
    · right
      refine ⟨graphProjectionN k z, ?_⟩
      change graphAppendN (graphProjectionN k z) (g (graphProjectionN k z)) = z
      rw [← hz, graphAppendN_projection]

lemma graphProjectionN_reflect_last {k : ℕ}
    (z : EuclideanSpace ℝ (Fin (k + 1))) :
    graphProjectionN k (coordinateReflection (Fin.last k) z) = graphProjectionN k z := by
  ext i
  simp [graphProjectionN_apply, coordinateReflection_apply, Fin.castSucc_ne_last]

/-- Reflection of the normal coordinate changes a graph into the negated graph. -/
lemma coordinateReflection_graphMapN_neg {k : ℕ}
    (g : EuclideanSpace ℝ (Fin k) → ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    coordinateReflection (Fin.last k) (graphMapN (fun y => -g y) x) = graphMapN g x := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [coordinateReflection_apply, Fin.castSucc_ne_last]

/-- The same ambient neighborhood, with the graph's two sides exchanged. -/
def C1BoundaryChart.exteriorChart (c : C1BoundaryChart) : C1BoundaryChart where
  height := fun x => -c.height x
  height_contDiff := c.height_contDiff.neg
  placement := (coordinateReflection (Fin.last 2)).toAffineIsometryEquiv.trans c.placement
  region := c.region
  isOpen_region := c.isOpen_region
  bounded_region := c.bounded_region

lemma C1BoundaryChart.exteriorChart_symm_apply (c : C1BoundaryChart) (z : AmbientSpace) :
    c.exteriorChart.placement.symm z = coordinateReflection (Fin.last 2) (c.placement.symm z) := by
  apply c.exteriorChart.placement.injective
  rw [c.exteriorChart.placement.apply_symm_apply]
  change z = c.placement (coordinateReflection (Fin.last 2)
    (coordinateReflection (Fin.last 2) (c.placement.symm z)))
  rw [coordinateReflection_involutive, c.placement.apply_symm_apply]

lemma C1BoundaryChart.exteriorChart_graphSurface (c : C1BoundaryChart) :
    c.exteriorChart.graphSurface = c.graphSurface := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨graphMapN c.height x, mem_range_self x, ?_⟩
    change c.placement (graphMapN c.height x) = c.placement
      (coordinateReflection (Fin.last 2) (graphMapN (fun y => -c.height y) x))
    rw [coordinateReflection_graphMapN_neg]
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨graphMapN (fun y => -c.height y) x, mem_range_self x, ?_⟩
    change c.placement
      (coordinateReflection (Fin.last 2) (graphMapN (fun y => -c.height y) x)) = _
    rw [coordinateReflection_graphMapN_neg]

lemma C1BoundaryChart.mem_closure_graphDomain_iff (c : C1BoundaryChart) (z : AmbientSpace) :
    z ∈ closure c.graphDomain ↔
      c.placement.symm z (Fin.last 2) ≤ c.height (graphProjectionN 2 (c.placement.symm z)) := by
  change z ∈ closure (c.placement.toHomeomorph '' smoothSubgraph c.height) ↔ _
  rw [← c.placement.toHomeomorph.image_closure]
  have hmem : z ∈ c.placement.toHomeomorph '' closure (smoothSubgraph c.height) ↔
      c.placement.symm z ∈ closure (smoothSubgraph c.height) := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨c.placement.symm z, hz, c.placement.apply_symm_apply z⟩
  rw [hmem, mem_closure_smoothSubgraph_iff c.height_contDiff.continuous]

lemma C1BoundaryChart.IsChartFor.closure_inter_eq {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) :
    closure E ∩ c.region = closure c.graphDomain ∩ c.region := by
  rw [closure_eq_self_union_frontier, closure_eq_self_union_frontier,
    union_inter_distrib_right, union_inter_distrib_right,
    hc.inter_eq, hc.frontier_inter_eq, c.frontier_graphDomain]

/-- A valid graph chart gives a reflected chart of the open exterior. -/
theorem C1BoundaryChart.IsChartFor.exterior {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) :
    c.exteriorChart.IsChartFor (closure E)ᶜ := by
  intro z hz
  have hcl : z ∈ closure E ↔ z ∈ closure c.graphDomain := by
    exact ⟨fun h => (hc.closure_inter_eq ▸ (show z ∈ closure E ∩ c.region from ⟨h, hz⟩)).1,
      fun h => (hc.closure_inter_eq.symm ▸
        (show z ∈ closure c.graphDomain ∩ c.region from ⟨h, hz⟩)).1⟩
  rw [mem_compl_iff, hcl, c.mem_closure_graphDomain_iff, not_le]
  change _ ↔ c.exteriorChart.placement.symm z (Fin.last 2) <
    -c.height (graphProjectionN 2 (c.exteriorChart.placement.symm z))
  rw [c.exteriorChart_symm_apply, graphProjectionN_reflect_last]
  simp only [coordinateReflection_apply, ite_true, neg_lt_neg_iff]

/-- Every C¹ boundary is also the boundary of its open exterior. -/
theorem HasC1Boundary.frontier_exterior {E : Set AmbientSpace} (hE : HasC1Boundary E) :
    frontier (closure E)ᶜ = frontier E := by
  apply Subset.antisymm
  · rw [frontier_compl]
    exact frontier_closure_subset
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := hE x hx
    have hgraph : x ∈ c.graphSurface ∩ c.region :=
      hc.frontier_inter_eq ▸ (show x ∈ frontier E ∩ c.region from ⟨hx, hxc⟩)
    have hext := hc.exterior.frontier_inter_eq
    rw [c.exteriorChart_graphSurface] at hext
    exact (hext.symm ▸ hgraph).1

/-- Exterior regularity follows from the original charts without a global bound. -/
theorem HasC1Boundary.exterior {E : Set AmbientSpace} (hE : HasC1Boundary E) :
    HasC1Boundary (closure E)ᶜ := by
  intro x hx
  rw [hE.frontier_exterior] at hx
  obtain ⟨c, hc, hxc⟩ := hE x hx
  exact ⟨c.exteriorChart, hc.exterior, hxc⟩

/-- The reflected graph has the opposite geometric normal after placement. -/
lemma smoothSubgraphNormal_neg_reflect {k : ℕ}
    (g : EuclideanSpace ℝ (Fin k) → ℝ) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    coordinateReflection (Fin.last k)
      (smoothSubgraphNormal (fun x => -g x) (coordinateReflection (Fin.last k) z)) =
      -smoothSubgraphNormal g z := by
  have hgrad (x : EuclideanSpace ℝ (Fin k)) :
      gradient (fun y => -g y) x = -gradient g x := by
    ext i
    simp only [PiLp.neg_apply, gradient_apply_eq_fderiv_single, fderiv_fun_neg,
      neg_apply]
  simp only [smoothSubgraphNormal, graphProjectionN_reflect_last, hgrad,
    smoothGraphUnitNormal, norm_neg, neg_neg, map_smul]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [coordinateReflection_apply, PiLp.smul_apply, PiLp.neg_apply,
      Fin.castSucc_ne_last]

lemma C1BoundaryChart.exteriorChart_outwardNormal (c : C1BoundaryChart) (z : AmbientSpace) :
    c.exteriorChart.outwardNormal z = -c.outwardNormal z := by
  unfold outwardNormal
  rw [c.exteriorChart_symm_apply]
  change c.placement.linearIsometryEquiv
    (coordinateReflection (Fin.last 2)
      (smoothSubgraphNormal (fun x => -c.height x)
        (coordinateReflection (Fin.last 2) (c.placement.symm z)))) = _
  rw [smoothSubgraphNormal_neg_reflect, map_neg]

end LiquidDrop
