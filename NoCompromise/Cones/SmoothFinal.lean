module

public import NoCompromise.Cones.ThreeDimFinal

@[expose] public section

/-!
# `lem:cone-smooth`: the punctured boundary of a 3-d minimising cone is smooth and minimal

Blueprint `lem:cone-smooth` (chapter 25): for a nontrivial locally perimeter-minimising cone
`C ⊂ ℝ³`, `∂C \ {0}` is a smooth embedded surface with zero mean curvature.

The blueprint derives the `C^∞` statement from `thm:eps-regularity` and the Campanato/Schauder
package.  In this formalization `thm:cone-3d` (`cone3d_halfspace`) is proved using only the
`C^{2,1/2}` part of that route (`cone_C1half_graph_of_ne_zero`, the weak and pointwise minimal
surface equations, interior `C^{2,1/2}` regularity); it does not use the `C^∞` statement or the
named hypothesis `MinimalGraphSmoothStatement`.  Hence the full lemma follows without circularity
from `cone3d_halfspace`: `densityOne C` is an open halfspace `{0 < ⟪μ, x⟫}`, so `∂(densityOne C)`
is the plane `μ^⊥`, which near every nonzero boundary point `p` is, in the rotated and rescaled
cylinder `p + s • Q (standardCylinder (1/4))` (`Q = verticalAxisIsometry μ`), the graph of the
zero function: smooth and with vanishing mean-curvature operator `div (∇f / √(1 + |∇f|²))`.

* `cone_smooth` : the unconditional form of `cone_smooth_graph_of_ne_zero`
  (Cones/SmoothMain.lean), with the zero-mean-curvature clause added.
-/

noncomputable section
open Set Metric
open scoped ContDiff
namespace LiquidDrop

/-- The boundary of an open halfspace `{0 < ⟪μ, x⟫}` is the plane `μ^⊥`. -/
lemma frontier_openHalfspace {μ : AmbientSpace} (hμ : μ ≠ 0) :
    frontier {x : AmbientSpace | 0 < inner ℝ μ x} = {x | inner ℝ μ x = 0} := by
  let L : AmbientSpace →L[ℝ] ℝ := innerSL ℝ μ
  have hsurj : Function.Surjective L := by
    intro t
    refine ⟨(t / ‖μ‖ ^ 2) • μ, ?_⟩
    have hn : ‖μ‖ ≠ 0 := norm_ne_zero_iff.mpr hμ
    simp only [L, innerSL_apply_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hopen : IsOpenMap L := L.isOpenMap hsurj
  have h := hopen.preimage_frontier_eq_frontier_preimage L.continuous (Set.Ioi (0 : ℝ))
  rw [show {x : AmbientSpace | 0 < inner ℝ μ x} = L ⁻¹' Set.Ioi 0 from rfl, ← h, frontier_Ioi]
  ext x
  simp [L]

/-- **Blueprint `lem:cone-smooth`.**  Near every nonzero boundary point `p` of a nontrivial
locally perimeter-minimising cone `C ⊂ ℝ³`, at every small scale `s`, the boundary of
`densityOne C` in the rotated and rescaled cylinder `p + s • Q (standardCylinder (1/4))`
(`Q = verticalAxisIsometry ν`, `ν ⊥ p` a unit normal) is exactly the graph of a function `f` on
the disk of radius `1/4` which is smooth (`C^∞`, i.e. `(⊤ : ℕ∞)`) and has zero mean curvature:
`div (∇f / √(1 + |∇f|²)) = 0` at every point of the disk. -/
theorem cone_smooth {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C)
    {p : AmbientSpace} (hp : p ∈ frontier (densityOne C)) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
    ∀ {s₀ : ℝ}, 0 < s₀ →
    ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        (∀ y ∈ standardCylinder (1 / 4),
          (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
            ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), graphAppendN x' (f x') = y)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        ContDiffOn ℝ ∞ f (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) ∧
        ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
            ((fderiv ℝ (fun y => mcFlux (gradient f y)) x' :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
              EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0 := by
  obtain ⟨μ, hμ, hΩ⟩ := cone3d_halfspace hC
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact zero_ne_one hμ
  have hfr : frontier (densityOne C) = {x | inner ℝ μ x = 0} := by
    rw [hΩ, frontier_openHalfspace hμ0]
  have hpμ : inner ℝ μ p = 0 := by
    have := hp
    rw [hfr] at this
    exact this
  refine ⟨μ, hμ, hpμ, fun {s₀} hs₀ => ⟨s₀, hs₀, le_rfl, fun _ => 0, ?_, ?_, ?_, ?_⟩⟩
  · intro y hy
    have hQ : inner ℝ μ (verticalAxisIsometry μ y) = y 2 := by
      have h1 : inner ℝ μ (verticalAxisIsometry μ y) =
          inner ℝ (verticalAxisIsometry μ (EuclideanSpace.single 2 1))
            (verticalAxisIsometry μ y) := by
        rw [verticalAxisIsometry_apply_vertical hμ]
      rw [h1, LinearIsometryEquiv.inner_map_map, EuclideanSpace.inner_single_left]
      simp
    rw [hfr, mem_ofPred_eq, inner_add_right, hpμ, zero_add, real_inner_smul_right, hQ,
      mul_eq_zero, or_iff_right hs₀.ne']
    constructor
    · intro hy0
      refine ⟨graphProjectionN 2 y, ?_, ?_⟩
      · simpa only [mem_ball, dist_zero_right] using hy.1
      · ext i
        fin_cases i
        · simp [graphAppendN, graphBaseN]
        · simp [graphAppendN, graphBaseN]
        · simpa [graphAppendN, graphBaseN] using hy0.symm
    · rintro ⟨x', _, rfl⟩
      simp [graphAppendN, graphBaseN]
  · intro x' _
    norm_num
  · exact contDiffOn_const
  · intro x' _
    have hg : gradient (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) = fun _ => 0 := by
      funext y
      simp [gradient]
    simp [hg]

end LiquidDrop
