module

public import NoCompromise.Cones.LinkGreatCircle
public import NoCompromise.Cones.LinkNonempty

@[expose] public section

/-!
# `thm:cone-3d` from the Euler equation on each connected component of the link

Blueprint `lem:cone-link-great-circle` (chapter 25): the link `Γ = ∂C ∩ S²` is a compact embedded
one-manifold, each component of which is parametrised by a unit-speed curve with `γ'' = -γ`.
Taking that description, stated per connected component (`connectedComponentIn Γ x`), as the
hypothesis, this file discharges the remaining bookkeeping hypotheses of
`cone3d_halfspace_of_link_components` (nonemptiness via `IsNontrivialMinimizingCone.link_nonempty`,
disjointness of distinct components automatically) and proves

* `link_eq_greatCircle_of_components` : `Γ` is one great circle;
* `cone3d_halfspace_of_component_curves` : `thm:cone-3d` under this hypothesis.

The per-component description itself (smoothness of the link, `lem:cone-smooth`, and its first
variation) is not proved here.
-/

noncomputable section
open Set Metric

namespace LiquidDrop

/-- **Last paragraph of `lem:cone-link-great-circle`, per component.** If every connected
component of the link of a nontrivial cone is the image of a unit-speed curve on `S²` solving
`γ'' = -γ`, then the link is a single great circle. -/
theorem link_eq_greatCircle_of_components {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C)
    (hcomp : ∀ x ∈ frontier (densityOne C) ∩ sphere 0 1, ∃ γ γ' : ℝ → AmbientSpace,
      (∀ t, HasDerivAt γ (γ' t) t) ∧ (∀ t, HasDerivAt γ' (-γ t) t) ∧
      (∀ t, ‖γ t‖ = 1) ∧ (∀ t, ‖γ' t‖ = 1) ∧
      connectedComponentIn (frontier (densityOne C) ∩ sphere 0 1) x = range γ) :
    ∃ ν : AmbientSpace, ν ≠ 0 ∧
      frontier (densityOne C) ∩ sphere 0 1 = {x | inner ℝ ν x = 0} ∩ sphere 0 1 := by
  set Γ := frontier (densityOne C) ∩ sphere 0 1 with hΓ
  have hcirc : ∀ x ∈ Γ, ∃ ν : AmbientSpace, ν ≠ 0 ∧
      connectedComponentIn Γ x = {y | inner ℝ ν y = 0} ∩ sphere 0 1 := by
    intro x hx
    obtain ⟨γ, γ', hγ, hγ', hn, hs, hc⟩ := hcomp x hx
    obtain ⟨ν, hν, hr⟩ := range_eq_greatCircle_of_hasDerivAt_neg hγ hγ' (hn 0) (hs 0)
      (inner_eq_zero_of_norm_eq_one hγ hn 0)
    exact ⟨ν, hν, hc.trans hr⟩
  obtain ⟨x₀, hx₀⟩ := hC.link_nonempty
  obtain ⟨ν₀, hν₀, hc₀⟩ := hcirc x₀ hx₀
  refine ⟨ν₀, hν₀, ?_⟩
  rw [← hc₀]
  apply Subset.antisymm _ (connectedComponentIn_subset Γ x₀)
  intro x hx
  obtain ⟨ν, _, hc⟩ := hcirc x hx
  obtain ⟨y, hy1, hyν₀, hyν⟩ := greatCircles_meet ν₀ ν
  have hys : y ∈ sphere (0 : AmbientSpace) 1 := by simpa using hy1
  have hy₀ : y ∈ connectedComponentIn Γ x₀ := by rw [hc₀]; exact ⟨hyν₀, hys⟩
  have hyx : y ∈ connectedComponentIn Γ x := by rw [hc]; exact ⟨hyν, hys⟩
  rw [connectedComponentIn_eq hy₀, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn hx

/-- **`thm:cone-3d` from the Euler equation on each component of the link.** -/
theorem cone3d_halfspace_of_component_curves {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C)
    (hcomp : ∀ x ∈ frontier (densityOne C) ∩ sphere 0 1, ∃ γ γ' : ℝ → AmbientSpace,
      (∀ t, HasDerivAt γ (γ' t) t) ∧ (∀ t, HasDerivAt γ' (-γ t) t) ∧
      (∀ t, ‖γ t‖ = 1) ∧ (∀ t, ‖γ' t‖ = 1) ∧
      connectedComponentIn (frontier (densityOne C) ∩ sphere 0 1) x = range γ) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  obtain ⟨ν, hν, hlink⟩ := link_eq_greatCircle_of_components hC hcomp
  exact cone3d_halfspace_of_link_eq hC hν hlink

end LiquidDrop
