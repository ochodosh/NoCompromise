module

public import NoCompromise.Regularity.GraphExtension

@[expose] public section

/-! # The Borel good boundary and its genuine projected graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

lemma measurableSet_goodExcessBase (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    MeasurableSet (goodExcessBase E hE hmE c γ) :=
  (measurableSet_le (measurable_truncatedMaximalMeasure _ _) measurable_const).inter
    measurableSet_ball

def graphGoodBoundary (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) : Set AmbientSpace :=
  (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) ∩
    graphProjectionN 2 ⁻¹' goodExcessBase E hE hmE c γ

def graphGoodBase (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  graphProjectionN 2 '' graphGoodBoundary E hE hmE c γ

lemma measurableSet_graphGoodBoundary (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    MeasurableSet (graphGoodBoundary E hE hmE c γ) :=
  ((measurableSet_reducedBoundary E hE hmE).inter
    (isOpen_standardCylinder (1 / 2)).measurableSet).inter
      ((measurableSet_goodExcessBase E hE hmE c γ).preimage (graphProjectionN 2).measurable)

lemma graphGoodBase_subset_goodExcessBase (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    graphGoodBase E hE hmE c γ ⊆ goodExcessBase E hE hmE c γ := by
  rintro x ⟨p, hp, rfl⟩
  exact hp.2

lemma graphGoodBase_subset_ball (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    graphGoodBase E hE hmE c γ ⊆ ball 0 (1 / 2) :=
  (graphGoodBase_subset_goodExcessBase E hE hmE c γ).trans inter_subset_right

lemma graphGoodBoundary_eq_restrict_graphGoodBase (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    graphGoodBoundary E hE hmE c γ =
      (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) ∩
        graphProjectionN 2 ⁻¹' graphGoodBase E hE hmE c γ := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1, mem_image_of_mem _ hp⟩
  · intro hp
    exact ⟨hp.1, graphGoodBase_subset_goodExcessBase E hE hmE c γ hp.2⟩

lemma IsOmegaMinimal.reducedBoundary_subset_frontier {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) :
    reducedBoundary E hE.locallyFinite hE.nullMeasurable ⊆ frontier (densityOne E) := by
  rw [hE.frontier_densityOne]
  exact reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable

lemma graphGoodBoundary_two_point {E : Set AmbientSpace} {ω c γ : ℝ}
    (hE : IsOmegaMinimal E ω)
    (htwo : ∀ p ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
      ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
      graphProjectionN 2 p ∈ goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ →
      |q 2 - p 2| ≤ γ * dist (graphProjectionN 2 q) (graphProjectionN 2 p)) :
    ∀ p ∈ graphGoodBoundary E hE.locallyFinite hE.nullMeasurable c γ,
      ∀ q ∈ graphGoodBoundary E hE.locallyFinite hE.nullMeasurable c γ,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q) := by
  intro p hp q hq
  exact htwo q ⟨hE.reducedBoundary_subset_frontier hq.1.1, hq.1.2⟩
    p ⟨hE.reducedBoundary_subset_frontier hp.1.1, hp.1.2⟩ hq.2

end LiquidDrop
