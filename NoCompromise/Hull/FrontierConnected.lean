module

public import NoCompromise.Hull.Properties
public import NoCompromise.Topology.Unicoherence

@[expose] public section

/-! # The boundary of the filled hull is connected (blueprint `lem:hull-properties`)

`∂K = K ∩ closure (ℝ³ ∖ K)` is the intersection of two closed connected sets covering `ℝ³`, so it
is connected by the unicoherence of `ℝ³` (`ambient_isPreconnected_inter_of_isClosed`).  Only
boundedness and connectedness of `Ω` are used; no regularity of `∂Ω` and no component count. -/

noncomputable section
open Set

namespace LiquidDrop

/-- `lem:hull-properties` (`∂K` connected): for a bounded connected `Ω ⊆ ℝ³`, the boundary of the
filled hull `K` is connected. -/
theorem filledHull_frontier_isConnected {Ω : Set AmbientSpace} (hc : IsConnected Ω)
    (hb : Bornology.IsBounded Ω) : IsConnected (frontier (filledHull Ω)) := by
  have hK := filledHull_isConnected hc hb
  have hKc := filledHull_isConnected_compl hb
  have hcl := filledHull_isClosed Ω
  have heq : frontier (filledHull Ω) = closure (filledHull Ω)ᶜ ∩ filledHull Ω := by
    rw [frontier_eq_closure_inter_closure, hcl.closure_eq, inter_comm]
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hfe : frontier (filledHull Ω) = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hclopen : IsClopen (filledHull Ω) := isClopen_iff_frontier_eq_empty.mpr hfe
    rcases isClopen_iff.mp hclopen with h | h
    · exact hK.nonempty.ne_empty h
    · obtain ⟨x, hx⟩ := hKc.nonempty
      exact hx (h ▸ mem_univ x)
  · rw [heq]
    refine ambient_isPreconnected_inter_of_isClosed isClosed_closure hcl hKc.2.closure hK.2 ?_
    rw [eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ filledHull Ω
    · exact Or.inr hx
    · exact Or.inl (subset_closure hx)

/-- `lem:hull-properties` (`∂K` connected) for a stationary domain (`not:stationary`). -/
theorem IsStationaryDomain.filledHull_frontier_isConnected {V lam : ℝ} {Ω : Set AmbientSpace}
    (h : IsStationaryDomain V lam Ω) : IsConnected (frontier (filledHull Ω)) :=
  LiquidDrop.filledHull_frontier_isConnected h.isConnected h.isBounded

/-- The topological hull properties of blueprint `lem:hull-properties` together with the
connectedness of `∂K`. -/
theorem filledHull_properties_frontier_isConnected {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h1 : HasC1Boundary Ω) :
    IsCompact (filledHull Ω) ∧
    closure Ω ⊆ filledHull Ω ∧
    IsConnected (filledHull Ω)ᶜ ∧
    frontier (filledHull Ω) ⊆ frontier Ω ∧
    IsConnected (filledHull Ω) ∧
    Ω ⊆ interior (filledHull Ω) ∧
    filledHull Ω = closure (interior (filledHull Ω)) ∧
    frontier (interior (filledHull Ω)) = frontier (filledHull Ω) ∧
    IsConnected (interior (filledHull Ω)) ∧
    perimeter (interior (filledHull Ω)) ≤ perimeter Ω ∧
    HasC1Boundary (interior (filledHull Ω)) ∧
    IsConnected (frontier (filledHull Ω)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := filledHull_properties ho hb hc h1
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, filledHull_frontier_isConnected hc hb⟩

end LiquidDrop
