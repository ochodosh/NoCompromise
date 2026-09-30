module

public import NoCompromise.Regularity.GraphSlicesFibers
public import NoCompromise.Regularity.GraphSlicesCapBridge
public import NoCompromise.Regularity.GraphPhaseCaps

@[expose] public section

/-! # Actual almost-everywhere coverage of the graph-approximation base -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Genuine oriented cap phases force an actual reduced-boundary point above
almost every point of the half-radius base disk. -/
theorem HasGraphCapPhases.ae_vertical_fiber
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 2) ∂volume.restrict (ball 0 (1 / 2)),
      ∃ z ∈ reducedBoundary E hE hmE ∩ standardCylinder (1 / 2), graphProjectionN 2 z = p := by
  have hL := h.1
  have hU := h.2
  rw [graphLowerCapRegion_eq_vertical_band] at hL
  rw [graphUpperCapRegion_eq_vertical_band] at hU
  have he := hE.ae_exists_vertical_reducedBoundary_of_phases hmE measurableSet_ball hL hU
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [he] with p hp hpB
  obtain ⟨t, ht, htR⟩ := hp (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hpB)
  refine ⟨graphAppendN p t, ⟨htR, ?_⟩, graphProjectionN_append p t⟩
  change ‖graphProjectionN 2 (graphAppendN p t)‖ < 1 / 2 ∧ |graphAppendN p t 2| < 1 / 2
  rw [graphProjectionN_append, graphAppendN_height_three]
  exact ⟨mem_ball_zero_iff.mp hpB, abs_lt.mpr ht⟩

/-- The actual small-excess hypotheses give almost-everywhere base coverage,
with the threshold fixed independently of the set and coefficient. -/
theorem graph_slices_coverage :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      ∀ᵐ p : EuclideanSpace ℝ (Fin 2) ∂volume.restrict (ball 0 (1 / 2)),
        ∃ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2),
          graphProjectionN 2 z = p := by
  obtain ⟨ε, hε, hp⟩ := graph_phase_caps
  refine ⟨ε, hε, fun E ω hE h0 he => ?_⟩
  exact (hp E ω hE h0 he).1.ae_vertical_fiber hE.locallyFinite hE.nullMeasurable

end LiquidDrop
