import NoCompromise.Regularity.GraphTwoPoint
import NoCompromise.Regularity.GraphPhaseCaps

/-! # The two-point estimate together with its actual oriented cap conclusion -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Blueprint `lem:two-point-lipschitz`, strengthened to the full canonical boundary
and exact cap inclusions. Actual phase bands are retained for the slicing step. -/
theorem graph_two_point_lipschitz {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ c > 0, ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      (∀ p ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
        ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
        graphProjectionN 2 p ∈ goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ →
        |q 2 - p 2| ≤ γ * dist (graphProjectionN 2 q) (graphProjectionN 2 p)) ∧
      HasGraphCapPhases E ∧
      cylindricalCap (1 / 2) (-(1 / 2 : ℝ)) ⊆ densityOne E ∧
      cylindricalCap (1 / 2) (1 / 2) ⊆ densityZero E ∧
      IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable (1 / 2) 0 (1 / 2) := by
  obtain ⟨c, hc, εt, hεt, ht⟩ := graph_two_point_lipschitz_estimate hγ hγ8
  obtain ⟨εp, hεp, hp⟩ := graph_phase_caps
  refine ⟨c, hc, min εt εp, lt_min hεt hεp, fun E ω hE h0 he => ?_⟩
  exact ⟨ht E ω hE h0 (he.trans (min_le_left _ _)),
    hp E ω hE h0 (he.trans (min_le_right _ _))⟩

end LiquidDrop
