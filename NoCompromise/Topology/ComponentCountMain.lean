import NoCompromise.Topology.ComponentCount
import NoCompromise.Topology.OrientationParity

/-!
# Component count for a disjoint union of surfaces (`thm:component-count`)

The intersection parity of `ParityPath.lean` discharges the parity hypothesis of
`card_connectedComponents_compl_eq_card_add_one_of_parity`. The final statement has exactly the
shape of `ComponentCountStatement` in `Capacity/Levels.lean`.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace LiquidDrop

/-- `thm:component-count`: the complement of a compact smooth embedded surface with finitely
many components `Σ₁, …, Σₖ` has exactly `k + 1` connected components. -/
theorem card_connectedComponents_compl_eq_card_add_one {S : Set E₃} (hc : IsCompact S)
    (hS : IsSmoothEmbeddedSurface S) (hfin : Finite (ConnectedComponents S)) :
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = Nat.card (ConnectedComponents S) + 1 := by
  refine card_connectedComponents_compl_eq_card_add_one_of_parity ?_ hc hS hfin
  intro T hT hTc _
  obtain ⟨z, hz⟩ := exists_not_mem_of_isCompact hTc
  exact ⟨SurfaceOddParity T z, surfaceOddParity_locally_constant hT hTc hz,
    surfaceOddParity_crossing hT hTc hz⟩

/-- `thm:component-count` in the form of `ComponentCountStatement` (`Capacity/Levels.lean`). -/
theorem componentCountStatement_holds :
    ∀ S : Set E₃, IsCompact S → IsSmoothEmbeddedSurface S →
      Finite (ConnectedComponents S) →
      Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = Nat.card (ConnectedComponents S) + 1 :=
  fun _ hc hS hfin => card_connectedComponents_compl_eq_card_add_one hc hS hfin

end LiquidDrop
