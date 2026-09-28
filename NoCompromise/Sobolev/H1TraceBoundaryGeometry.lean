import NoCompromise.Sobolev.H1TraceChart
import NoCompromise.BV.CoareaIsometry

/-!
# Finite boundary-plane covers for trace estimates

A valid one-sided graph chart sends its central coordinate plane onto the domain
boundary inside the chart region. Compactness supplies a finite surface cover.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Inside a valid chart, a boundary point has zero normal coordinate. -/
lemma LipschitzGraphChart.normal_eq_zero_of_mem_frontier {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (c : LipschitzGraphChart n) (hc : c.IsChartFor D)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ frontier D) (hxr : x ∈ c.region) :
    c.homeomorph.symm x c.normal = 0 := by
  have hxcl : x ∈ closure (D ∩ c.region) := c.isOpen_region.closure_inter ⟨hx.1, hxr⟩
  have hclosed : IsClosed {z | 0 ≤ c.homeomorph.symm z c.normal} :=
    isClosed_le continuous_const ((EuclideanSpace.proj c.normal).continuous.comp
      c.homeomorph.symm.continuous)
  have hsub : D ∩ c.region ⊆ {z | 0 ≤ c.homeomorph.symm z c.normal} := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hc.symm ▸ hz
    simpa only [mem_ofPred_eq, c.homeomorph.symm_apply_apply] using hy.2.le
  have hnonneg : 0 ≤ c.homeomorph.symm x c.normal := closure_minimal hsub hclosed hxcl
  have hxnot : x ∉ D := by
    simpa only [hD.interior_eq] using hx.2
  have hyn : ¬0 < c.homeomorph.symm x c.normal := by
    intro hypos
    have hycube : c.homeomorph.symm x ∈ coordinateCube n c.radius := by
      obtain ⟨y, hy, rfl⟩ := hxr
      simpa only [c.homeomorph.symm_apply_apply] using hy
    have hxup : x ∈ c.upperRegion :=
      ⟨c.homeomorph.symm x, ⟨hycube, hypos⟩, c.homeomorph.apply_symm_apply x⟩
    exact hxnot ((hc ▸ hxup).1)
  exact le_antisymm (le_of_not_gt hyn) hnonneg

/-- Place the final-coordinate plane into the chart's chosen normal coordinates. -/
def LipschitzGraphChart.boundaryPlaneChart {k : ℕ} (c : LipschitzGraphChart (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)) :=
  (coareaSwap c.normal).toHomeomorph.trans c.homeomorph

lemma LipschitzGraphChart.lipschitz_boundaryPlaneChart {k : ℕ}
    (c : LipschitzGraphChart (k + 1)) :
    LipschitzWith (1 + c.lip) c.boundaryPlaneChart := by
  change LipschitzWith (1 + c.lip) (c.homeomorph ∘ coareaSwap c.normal)
  simpa only [mul_one] using c.lipschitz.comp (coareaSwap c.normal).isometry.lipschitzWith

lemma LipschitzGraphChart.lipschitz_boundaryPlaneChart_symm {k : ℕ}
    (c : LipschitzGraphChart (k + 1)) :
    LipschitzWith (1 + c.lip) c.boundaryPlaneChart.symm := by
  change LipschitzWith (1 + c.lip) ((coareaSwap c.normal).symm ∘ c.homeomorph.symm)
  simpa only [one_mul] using
    (coareaSwap c.normal).symm.isometry.lipschitzWith.comp c.lipschitz_symm

lemma LipschitzGraphChart.frontier_inter_region_subset_plane {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D) :
    frontier D ∩ c.region ⊆ range (fun x => c.boundaryPlaneChart (graphAppendN x 0)) := by
  rintro x ⟨hx, hxr⟩
  let z := (coareaSwap c.normal).symm (c.homeomorph.symm x)
  have hz : z (Fin.last k) = 0 := by
    simpa only [z, coareaSwap_symm_apply, Equiv.swap_apply_right] using
      c.normal_eq_zero_of_mem_frontier hD hc hx hxr
  have happ : graphAppendN (graphProjectionN k z) 0 = z := by
    rw [← hz]
    exact graphAppendN_projection z
  refine ⟨graphProjectionN k z, ?_⟩
  change c.boundaryPlaneChart (graphAppendN (graphProjectionN k z) 0) = x
  rw [happ]
  change c.homeomorph (coareaSwap c.normal
    ((coareaSwap c.normal).symm (c.homeomorph.symm x))) = x
  rw [LinearIsometryEquiv.apply_symm_apply, c.homeomorph.apply_symm_apply]

/-- The boundary of a bounded Lipschitz domain is contained in finitely many
complete bi-Lipschitz images of coordinate planes. -/
theorem exists_finite_boundary_plane_cover {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ s : Finset {c : LipschitzGraphChart (k + 1) // c.IsChartFor D},
      frontier D ⊆ ⋃ c ∈ s, range (fun x => c.val.boundaryPlaneChart (graphAppendN x 0)) := by
  have hc : IsCompact (frontier D) :=
    hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let V := fun c : {c : LipschitzGraphChart (k + 1) // c.IsChartFor D} => c.val.region
  have hcover : frontier D ⊆ ⋃ c, V c := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hL x hx
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover V (fun c => c.val.isOpen_region) hcover
  refine ⟨s, fun x hx => ?_⟩
  obtain ⟨c, hcs, hxc⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion₂.mpr ⟨c, hcs,
    c.val.frontier_inter_region_subset_plane hD c.property ⟨hx, hxc⟩⟩

end LiquidDrop
