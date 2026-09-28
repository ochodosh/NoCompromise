import NoCompromise.Cones.Halfspace
import NoCompromise.Cones.ThreeDim
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometric endgames of `lem:cone-2d` and `thm:cone-3d` (chapter 25)

Conditional reductions, stated for the density-one representative:

* `cone3d_halfspace_of_link_eq` : a nontrivial minimising cone in `ℝ³` whose link
  `∂C ∩ S²` is a great circle `ν^⊥ ∩ S²` is an open halfspace (last line of the proof of
  `thm:cone-3d`; the great-circle property itself is `lem:cone-link-great-circle`, open).
* `cone2d_halfplane_of_link_subset_antipodal` : a nontrivial planar cone whose link lies in a pair
  of antipodal points is an open halfplane (last line of the proof of `lem:cone-2d`; the fact that
  exactly two antipodal rays occur is the open competitor argument).
-/

noncomputable section
open Set MeasureTheory Metric

namespace LiquidDrop

/-- **`thm:cone-3d`, endgame.**  If the link of the boundary of the density-one representative of a
nontrivial locally perimeter-minimising cone in `ℝ³` is the great circle `ν^⊥ ∩ S²`, then that
representative is an open halfspace. -/
theorem cone3d_halfspace_of_link_eq {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C)
    {ν : AmbientSpace} (hν : ν ≠ 0)
    (hlink : frontier (densityOne C) ∩ sphere 0 1 = {x | inner ℝ ν x = 0} ∩ sphere 0 1) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} :=
  densityOne_eq_halfspace_of_link_eq (by norm_num) hC.measurable hC.dilation hν hlink
    hC.nontrivial

/-- Every vector of the plane has a nonzero orthogonal vector. -/
lemma exists_ne_zero_inner_eq_zero_fin2 (u : EuclideanSpace ℝ (Fin 2)) :
    ∃ ν : EuclideanSpace ℝ (Fin 2), ν ≠ 0 ∧ inner ℝ ν u = 0 := by
  have hlt : Module.finrank ℝ ℝ < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  obtain ⟨ν, hνK, hν0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := innerₛₗ ℝ u) hlt)
  have h : inner ℝ u ν = 0 := by
    simpa [innerₛₗ_apply_apply] using LinearMap.mem_ker.mp hνK
  exact ⟨ν, hν0, by rw [real_inner_comm]; exact h⟩

/-- **`lem:cone-2d`, endgame.**  A nontrivial planar set with dilation-invariant density-one
representative whose boundary link lies in an antipodal pair `{u, -u}` has an open halfplane as
density-one representative. -/
theorem cone2d_halfplane_of_link_subset_antipodal {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hm : MeasurableSet C) (hcone : IsDilationInvariant (densityOne C))
    (hnt : 0 < volume C ∧ 0 < volume Cᶜ) (u : EuclideanSpace ℝ (Fin 2))
    (hlink : frontier (densityOne C) ∩ sphere 0 1 ⊆ {u, -u}) :
    ∃ μ : EuclideanSpace ℝ (Fin 2), ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  obtain ⟨ν, hν0, hνu⟩ := exists_ne_zero_inner_eq_zero_fin2 u
  refine densityOne_eq_halfspace_of_link (by norm_num) hm hcone hν0 ?_ hnt
  intro x hx
  have hx' := hlink hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx'
  show inner ℝ ν x = 0
  rcases hx' with rfl | rfl
  · exact hνu
  · rw [inner_neg_right, hνu, neg_zero]

end LiquidDrop
