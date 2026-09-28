import NoCompromise.Capacity.AnnularBarrier
import NoCompromise.Capacity.HullPotential

/-!
# Existence of the capacitary potential of the filled hull

Blueprint `thm:capacitary-potential`, existence, for the filled hull `K` of a bounded open
`Ω ∋ 0` with `C²` boundary (the blueprint's normalisation "translate so that `0 ∈ int K`"):
`C²` charts of `Ω` at points of `∂K` are `C²` charts of `int K` (`lem:hull-properties`), so the
annular construction with exterior-ball barriers applies. Regularity up to `∂K`
(`C^{2,α}`, `thm:boundary-C2a`) is not claimed here.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace LiquidDrop

variable {Ω : Set AmbientSpace}

/-- `lem:hull-properties`: `C²` charts of `Ω` at points of `∂K` restrict to `C²` charts of
`int K`. -/
theorem filledHull_hasC2Boundary_interior (ho : IsOpen Ω) (h2 : HasC2Boundary Ω) :
    HasC2Boundary (interior (filledHull Ω)) := by
  intro p hp
  rw [filledHull_frontier_interior ho] at hp
  obtain ⟨c, hc, hpc, hC2⟩ := h2 p (filledHull_frontier_subset ho hp)
  obtain ⟨c', hhe, -, -, hpc', hc'⟩ := hull_chart_of_chart ho h2.hasC1Boundary hc hp hpc
  exact ⟨c', hc', hpc', hhe ▸ hC2⟩

/-- Blueprint `thm:capacitary-potential`, existence, for the filled hull of a bounded open
`Ω ∋ 0` with `C²` boundary: a continuous `u`, harmonic and smooth off `K`, equal to `1` on `K`,
tending to `0` at infinity, with `0 < u < 1` off `K` (`eq:capacitary-signs`, first half). -/
theorem exists_filledHull_capacitary_potential (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h2 : HasC2Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u (filledHull Ω)ᶜ ∧
      (∀ x ∈ filledHull Ω, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      ∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1 := by
  have hK := filledHull_isCompact hbd
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : AmbientSpace)
  obtain ⟨u, hc, hh, hs, h1, hd, -, -⟩ := exists_capacitary_potential_of_hasC2Boundary hK
    (filledHull_eq_closure_interior ho) (filledHull_hasC2Boundary_interior ho h2)
    (filledHull_subset_interior ho h0) hR₀
  exact ⟨u, hc, hh, hs, h1, hd, (filledHull_capacitary_properties ho hbd h0 hc hh h1 hd).1⟩

end LiquidDrop
