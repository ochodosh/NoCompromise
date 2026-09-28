import NoCompromise.Cones.ThreeDimMain
import NoCompromise.Cones.MinimalGraphPointwise

/-!
# `thm:cone-3d`: three-dimensional minimising cones are halfspaces

Blueprint `thm:cone-3d` (chapter 25), unconditionally: `MinimalGraphPointwiseStatement` is
`minimal_graph_pointwise_of_weak`, so `cone3d_halfspace_of_pointwise` applies.

Route (all proved): halfspace tangents at nonzero boundary points (`lem:cone-2d`,
`lem:cone-descent`), vanishing excess and `thm:eps-regularity` (`C^{1,1/2}` graph,
`lem:cone-smooth`), the weak minimal-surface equation (`eq:bounded-H`, `ω = 0`), interior
`C^{2,1/2}` (quasilinear Schauder), the pointwise equation, degree-one homogeneity about the vertex
forcing a zero Hessian (the link is a geodesic), local flatness, and the local-to-global
great-circle argument of `lem:cone-link-great-circle`.
-/

noncomputable section

namespace LiquidDrop

/-- The pointwise minimal-surface equation from the weak one, in the form used by
`cone3d_halfspace_of_pointwise`. -/
theorem minimalGraphPointwiseStatement_holds : MinimalGraphPointwiseStatement :=
  fun _U hU _f hf he => minimal_graph_pointwise_of_weak hU hf he

/-- **Blueprint `thm:cone-3d`.**  The density-one representative of every nontrivial locally
perimeter-minimising cone in `ℝ³` is an open halfspace. -/
theorem cone3d_halfspace {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} :=
  cone3d_halfspace_of_pointwise minimalGraphPointwiseStatement_holds hC

/-- **Blueprint `lem:cone-link-great-circle`.**  The link `∂C ∩ S²` of a nontrivial locally
perimeter-minimising cone in `ℝ³` is a single great circle.  (Obtained here from
`cone3d_halfspace`, whose proof runs through the local great-circle argument
`eq_greatCircle_of_locally_greatCircle`.) -/
theorem cone_link_eq_greatCircle {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C) :
    ∃ ν : AmbientSpace, ν ≠ 0 ∧
      frontier (densityOne C) ∩ Metric.sphere 0 1 = {x | inner ℝ ν x = 0} ∩ Metric.sphere 0 1 := by
  obtain ⟨μ, hμ, hC'⟩ := cone3d_halfspace hC
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact zero_ne_one hμ
  refine ⟨μ, hμ0, ?_⟩
  let L : AmbientSpace →L[ℝ] ℝ := innerSL ℝ μ
  have hsurj : Function.Surjective L := by
    intro t
    refine ⟨(t / ‖μ‖ ^ 2) • μ, ?_⟩
    simp only [L, innerSL_apply_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hopen : IsOpenMap L := L.isOpenMap hsurj
  have hfr : frontier {x : AmbientSpace | 0 < inner ℝ μ x} = {x | inner ℝ μ x = 0} := by
    have h := hopen.preimage_frontier_eq_frontier_preimage L.continuous (Set.Ioi (0 : ℝ))
    rw [show {x : AmbientSpace | 0 < inner ℝ μ x} = L ⁻¹' Set.Ioi 0 from rfl, ← h, frontier_Ioi]
    ext x
    simp [L]
  rw [hC', hfr]

end LiquidDrop
