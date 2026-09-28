import NoCompromise.DeGiorgi.SmoothBoundary
import NoCompromise.Sobolev.ExtensionPartition

/-!
# Finite C¹ boundary charts for classical calculus

The compact closure has a finite cover by the interior domain and genuine
one-sided rigid C¹ graph charts. This is purely a topological cover argument;
no perimeter, reduced-boundary, or transport theorem is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- The interior patch together with all valid boundary chart regions. -/
def classicalBoundaryRegion (D : Set AmbientSpace) :
    Option {c : C1BoundaryChart // c.IsChartFor D} → Set AmbientSpace
  | none => D
  | some c => c.val.region

/-- A bounded domain with C¹ boundary has a finite bounded open chart cover
of its closure, selected from the interior patch and boundary chart regions. -/
theorem exists_finite_c1_boundary_cover
    {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasC1Boundary D) :
    ∃ s : Finset (Option {c : C1BoundaryChart // c.IsChartFor D}),
      (∀ i, IsOpen (classicalBoundaryRegion D i)) ∧
      (∀ i, Bornology.IsBounded (classicalBoundaryRegion D i)) ∧
      closure D ⊆ ⋃ i ∈ s, classicalBoundaryRegion D i := by
  have hopen : ∀ i, IsOpen (classicalBoundaryRegion D i) := by
    rintro (_ | c)
    · exact hD
    · exact c.val.isOpen_region
  have hbounded : ∀ i, Bornology.IsBounded (classicalBoundaryRegion D i) := by
    rintro (_ | c)
    · exact hbD
    · exact c.val.bounded_region
  have hcover : closure D ⊆ ⋃ i, classicalBoundaryRegion D i := by
    rw [closure_eq_self_union_frontier]
    rintro x (hx | hx)
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨c, hc, hxc⟩ := hL x hx
      exact mem_iUnion.mpr ⟨some ⟨c, hc⟩, hxc⟩
  obtain ⟨s, hs⟩ := hbD.isCompact_closure.elim_finite_subcover
    (classicalBoundaryRegion D) hopen hcover
  exact ⟨s, hopen, hbounded, hs⟩


end LiquidDrop
