import NoCompromise.Green.SecondIdentity
import NoCompromise.Capacity.HullPotentialBoundaryC2

/-!
# `thm:green-identity` for the filled hull, unconditionally

For `K = filledHull Ω`, `Ω` a bounded open set with `C³` boundary containing `0`, and `u` any
capacitary potential of `K`, `hullPotentialBoundaryC2` (`thm:boundary-C2a` for the hull
potential) supplies the `C²` extension `g` of `u` across `∂K` that
`filledHull_green_identity_of_boundary_C2` takes as an argument; `w = |∇g|` on `∂K` is the
one-sided `|∇u|` there.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- Blueprint `thm:green-identity` (`eq:green-identity`) for the capacitary potential of the
filled hull `K` of a bounded open `Ω ∋ 0` with `C³` boundary: some `C²` function `g` with
`u = g` on `closure Kᶜ` satisfies `(4π)⁻¹ ∫_{∂K} v_Ω |∇g| dH² = |Ω|`. The conclusion after the
extension is that of `filledHull_green_identity_of_boundary_C2`. -/
theorem filledHull_green_identity_unconditional {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      (4 * Real.pi)⁻¹ * (∫ x in frontier (filledHull Ω),
        coulombPotentialReal Ω x * ‖gradient g x‖ ∂hausdorffMeasure2 3) = (volume Ω).toReal := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  exact ⟨g, hg, hug, filledHull_green_identity_of_boundary_C2 ho hbd h3.hasC1Boundary h0
    hu hh hb hinf hg hug⟩

end LiquidDrop
