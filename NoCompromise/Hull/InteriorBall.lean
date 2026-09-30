module

public import NoCompromise.Elliptic.HopfC2Boundary

@[expose] public section

/-!
# Interior tangent balls for regular closed sets

Reflecting a C² boundary chart preserves its regularity. Applying the exterior
tangent-ball theorem to the complement of a regular closed set then gives a
ball in its interior touching each boundary point.
-/

noncomputable section
open Set Metric
open scoped Topology
namespace LiquidDrop

/-- Reflecting the graph charts preserves C² regularity of the open exterior. -/
theorem HasC2Boundary.exterior {D : Set AmbientSpace} (hD : HasC2Boundary D) :
    HasC2Boundary (closure D)ᶜ := by
  intro p hp
  rw [hD.hasC1Boundary.frontier_exterior] at hp
  obtain ⟨c, hc, hpr, hC2⟩ := hD p hp
  exact ⟨c.exteriorChart, hc.exterior, hpr, hC2.neg⟩

/-- Every boundary point of a regular closed set with C² interior boundary
admits an interior tangent ball. -/
theorem exists_interior_tangent_ball_of_hasC2Boundary {K : Set AmbientSpace}
    (hreg : K = closure (interior K)) (hC2 : HasC2Boundary (interior K)) :
    ∀ p ∈ frontier K, ∃ q : AmbientSpace, ∃ ρ > 0, ball q ρ ⊆ K ∧ ‖p - q‖ = ρ := by
  have hcompl : HasC2Boundary Kᶜ := by
    simpa only [← hreg] using hC2.exterior
  intro p hp
  have hpcompl : p ∈ frontier Kᶜ := by
    simpa only [frontier_compl] using hp
  obtain ⟨c, hc, hpr, hc2⟩ := hcompl p hpcompl
  obtain ⟨ρ, hρ, hball, hsp⟩ := hc.exists_exterior_tangent_ball hc2 hpcompl hpr
  refine ⟨p + ρ • c.outwardNormal p, ρ, hρ, ?_, ?_⟩
  · rw [← interior_eq_compl_closure_compl] at hball
    exact hball.trans interior_subset
  · simpa only [mem_sphere, dist_eq_norm] using hsp

end LiquidDrop
