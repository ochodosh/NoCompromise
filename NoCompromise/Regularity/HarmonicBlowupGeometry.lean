module

public import NoCompromise.Regularity.GraphApproxHeight

@[expose] public section

/-!
# Genuine geometric hypotheses for harmonic graph blowups

One fixed smallness threshold supplies the actual cap phases, reduced-boundary
height clearance and bounded unit excess used in the compact-test residual.
These properties follow from quasiminimality and are not extra input data.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Small actual excess and quasiminimality clear the test-cutoff transition
from the reduced boundary and determine the oriented cap phases. -/
theorem harmonicBlowup_geometry : ∃ ε > 0, ε ≤ 1 ∧
    ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasGraphCapPhases E ∧
      (∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
        standardCylinder (1 / 2), |z 2| ≤ 1 / 4) ∧
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) ≤ 1 := by
  obtain ⟨εp, hεp, hp⟩ := graph_phase_caps_phases
  obtain ⟨εh, hεh, hh⟩ := height_bound (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨min 1 (min εp εh), lt_min zero_lt_one (lt_min hεp hεh),
    min_le_left _ _, fun E ω hE h0 he => ?_⟩
  have hep := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heh := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have he1 := he.trans (min_le_left _ _)
  have hheight := hh E ω hE h0 1 zero_lt_one le_rfl (by simpa only [mul_one] using heh)
  refine ⟨hp E ω hE h0 hep, ?_, by linarith [hE.nonneg]⟩
  intro z hz
  have hsub : standardCylinder (1 / 2) ⊆ standardCylinder (3 / 4) := by
    rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
    exact cylinder_mono (by norm_num)
  have hb := hheight z ⟨hE.reducedBoundary_subset_frontier hz.1, by
    simpa only [mul_one] using hsub hz.2⟩
  simpa only [mul_one] using hb.le

end LiquidDrop
