module

public import NoCompromise.Elliptic.ClassicalCalculus

@[expose] public section

/-! # Finite classical boundary area and distance from an interior point -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop

theorem finite_boundary_area {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    IsFiniteMeasure ((hausdorffMeasure2 3).restrict (frontier D)) := by
  have hw : HasW11GradientOn (fun _ : AmbientSpace => (1 : ℝ)) (fun _ => 0) D := by
    refine ⟨?_, integrableOn_const hbD.measure_lt_top.ne, integrable_zero _ _ _⟩
    simpa using hasWeakGradientOn_of_contDiffOn hD (contDiff_const (c := (1 : ℝ))).contDiffOn
  obtain ⟨_, _, ht⟩ := exists_w11_boundary_restriction_bound hD hbD hC1.hasLipschitzBoundary
  have hi := memLp_one_iff_integrable.mp (ht _ _ hw continuous_const).1
  have hi' : Integrable (fun _ : AmbientSpace => (1 : ℝ))
      ((hausdorffMeasure2 3).restrict (frontier D)) := by
    simpa only [hausdorffMeasure2] using hi
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hi'

lemma exists_pos_boundary_distance {D : Set AmbientSpace} (hD : IsOpen D)
    {y : AmbientSpace} (hy : y ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ frontier D, δ ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hD y hy
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_contra hn
  have hxy : x ∈ ball y δ := by simpa only [mem_ball, dist_eq_norm, not_le] using hn
  rw [frontier, hD.interior_eq] at hx
  exact hx.2 (hsub hxy)

end LiquidDrop
