module

public import NoCompromise.Cones.ThreeDim
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-!
# Nonemptiness of the link of a nontrivial three-dimensional cone
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Topology ENNReal

namespace LiquidDrop

/-- The frontier of the density-one representative of a cone is invariant
under positive dilations. -/
theorem IsNontrivialMinimizingCone.smul_mem_frontier {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {x : AmbientSpace}
    (hx : x ∈ frontier (densityOne C)) {t : ℝ} (ht : 0 < t) :
    t • x ∈ frontier (densityOne C) := by
  have himage := (Homeomorph.smulOfNeZero t ht.ne').image_frontier (densityOne C)
  simp only [Homeomorph.smulOfNeZero_apply] at himage
  rw [show (fun y : AmbientSpace => t • y) = (t • ·) from rfl, hC.dilation t ht]
    at himage
  rw [← himage]
  exact ⟨x, hx, rfl⟩

/-- The frontier of a nontrivial cone contains a nonzero point. -/
theorem IsNontrivialMinimizingCone.exists_ne_zero_mem_frontier {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) :
    ∃ x ∈ frontier (densityOne C), x ≠ 0 := by
  let D : Set AmbientSpace := densityOne C
  have hDC : D =ᵐ[volume] C :=
    densityOne_ae_eq (by norm_num : 0 < 3) hC.measurable.nullMeasurableSet
  by_contra h
  have hfr : frontier D ⊆ {0} := by
    intro x hx
    simp only [mem_singleton_iff]
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  have hconn : IsPreconnected ({0}ᶜ : Set AmbientSpace) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simp [AmbientSpace])) 0).isPreconnected
  have hcover : ({0}ᶜ : Set AmbientSpace) ⊆ interior D ∪ interior Dᶜ := by
    intro x hx
    have hxfr : x ∉ frontier D := by
      intro hxf
      exact hx (hfr hxf)
    change x ∈ (frontier D)ᶜ at hxfr
    simpa only [compl_frontier_eq_union_interior] using hxfr
  have hdisj : ({0}ᶜ : Set AmbientSpace) ∩ (interior D ∩ interior Dᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (interior_subset hx.2.2) (interior_subset hx.2.1)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn)
    (interior D) (interior Dᶜ) isOpen_interior isOpen_interior hcover hdisj with hD | hDc
  · have hsub : Dᶜ ⊆ ({0} : Set AmbientSpace) := by
      intro x hx
      by_contra hx0
      have hxi : x ∈ interior D := hD (by simpa using hx0)
      exact hx (interior_subset hxi)
    have hz : volume Dᶜ = 0 := measure_mono_null hsub (measure_singleton 0)
    have : volume Cᶜ = 0 := by rw [← measure_congr hDC.compl]; exact hz
    exact hC.nontrivial.2.ne' this
  · have hsub : D ⊆ ({0} : Set AmbientSpace) := by
      intro x hx
      by_contra hx0
      have hxi : x ∈ interior Dᶜ := hDc (by simpa using hx0)
      exact (interior_subset hxi) hx
    have hz : volume D = 0 := measure_mono_null hsub (measure_singleton 0)
    have : volume C = 0 := by rw [← measure_congr hDC]; exact hz
    exact hC.nontrivial.1.ne' this

/-- The link `Γ = ∂C ∩ S²` of a nontrivial cone is nonempty. -/
theorem IsNontrivialMinimizingCone.link_nonempty {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) :
    (frontier (densityOne C) ∩ Metric.sphere 0 1).Nonempty := by
  obtain ⟨x, hx, hx0⟩ := hC.exists_ne_zero_mem_frontier
  have hn : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
  refine ⟨‖x‖⁻¹ • x, hC.smul_mem_frontier hx hn, ?_⟩
  rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hn,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]

end LiquidDrop
