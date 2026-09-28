import NoCompromise.Capacity.HullExistence
import NoCompromise.Capacity.FiniteEnergy

/-!
# The filled-hull capacitary potential: locally H¹ extension and finite energy

Blueprint `thm:capacitary-potential` for the filled hull `K` of a bounded open `Ω ∋ 0` with `C²`
boundary: the potential of `exists_filledHull_capacitary_potential` (already equal to `1` on `K`,
i.e. "extended by the constant `1`"), and, under the named boundary-regularity input used across
chapters 30/31 (a global `C²` function `g` with `u = g` on `closure Kᶜ`, the stand-in for
`thm:boundary-C2a` up to `∂K`), it is globally Lipschitz, `H¹` on every bounded open set, and has
finite exterior energy (`eq:capacity-finite-energy`).
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal Gradient
namespace LiquidDrop

variable {Ω : Set AmbientSpace}

/-- Blueprint `thm:capacitary-potential` (existence, locally H¹ extension by `1`, and
`eq:capacity-finite-energy`) for the filled hull of a bounded open `Ω ∋ 0` with `C²` boundary; the
last three clauses are conditional on the named `C²` boundary-extension hypothesis. -/
theorem exists_filledHull_capacitary_potential_energy (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h2 : HasC2Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u (filledHull Ω)ᶜ ∧
      (∀ x ∈ filledHull Ω, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1) ∧
      ((∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ)) →
        (∃ L : ℝ≥0, LipschitzWith L u) ∧
        (∀ U : Set AmbientSpace, IsOpen U → Bornology.IsBounded U → IsH1On u U) ∧
        IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (filledHull Ω)ᶜ) := by
  obtain ⟨u, hc, hh, hs, h1, hd, h01⟩ := exists_filledHull_capacitary_potential ho hbd h2 h0
  refine ⟨u, hc, hh, hs, h1, hd, h01, ?_⟩
  rintro ⟨g, hg, hug⟩
  have hK := filledHull_isCompact hbd
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  have hzero : (0 : AmbientSpace) ∈ interior (filledHull Ω) := filledHull_subset_interior ho h0
  have hR₀ : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : filledHull Ω ⊆ closedBall 0 (max R 1) :=
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  obtain ⟨hL, hH, hE, -⟩ :=
    capacitary_potential_h1_energy_of_c2_extension hK hR₀ hKR hzero hc hh h1 hd hg1 hug
  exact ⟨hL, hH, hE⟩

end LiquidDrop
