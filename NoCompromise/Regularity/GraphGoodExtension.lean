module

public import NoCompromise.Regularity.GraphGoodSet
public import NoCompromise.Regularity.GraphExtensionClamp

@[expose] public section

/-! # A genuine Borel Lipschitz graph selected from small excess -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

/-- Small actual excess produces the Borel projected good set and a globally
Lipschitz extension, preserving its exact graph and a fixed interior height bound. -/
theorem exists_good_graph_extension {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ c > 0, ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      MeasurableSet (graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ) ∧
      graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ ⊆
        goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        LipschitzWith ⟨γ, hγ.le⟩ f ∧ (∀ x, |f x| ≤ 1 / 16) ∧
        (∀ p ∈ graphGoodBoundary E hE.locallyFinite hE.nullMeasurable c γ,
          f (graphProjectionN 2 p) = p 2) ∧
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
            graphProjectionN 2 ⁻¹' graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ =
          (fun x => graphAppendN x (f x)) ''
            graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ := by
  obtain ⟨c, hc, εt, hεt, ht⟩ := graph_two_point_lipschitz_estimate hγ hγ8
  obtain ⟨εh, hεh, hh⟩ := height_bound (by norm_num : (0 : ℝ) < 1 / 16)
  refine ⟨c, hc, min εt εh, lt_min hεt hεh, fun E ω hE h0 he => ?_⟩
  have htwo := graphGoodBoundary_two_point hE
    (ht E ω hE h0 (he.trans (min_le_left _ _)))
  have hm : MeasurableSet (graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ) :=
    measurableSet_projected_graph (measurableSet_graphGoodBoundary _ _ _ _ _) htwo
  have hheight (p : AmbientSpace)
      (hp : p ∈ graphGoodBoundary E hE.locallyFinite hE.nullMeasurable c γ) :
      |p 2| ≤ 1 / 16 := by
    have hsub : standardCylinder (1 / 2) ⊆ standardCylinder (3 * (1 : ℝ) / 4) := by
      rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
      exact cylinder_mono (by norm_num)
    have hp' := hh E ω hE h0 1 (by norm_num) le_rfl
      (by simpa only [mul_one] using he.trans (min_le_right _ _)) p
      ⟨hE.reducedBoundary_subset_frontier hp.1.1, hsub hp.1.2⟩
    simpa only [mul_one] using hp'.le
  obtain ⟨f, hf, hb, hv, hg⟩ := exists_clamped_lipschitz_graph_extension
    (γ := ⟨γ, hγ.le⟩) htwo (by norm_num : (0 : ℝ) ≤ 1 / 16) hheight
  refine ⟨hm, graphGoodBase_subset_goodExcessBase _ _ _ _ _, f, hf, hb, hv, ?_⟩
  rw [← graphGoodBoundary_eq_restrict_graphGoodBase]
  exact hg

end LiquidDrop
