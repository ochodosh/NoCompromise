module

public import NoCompromise.Regularity.GraphGoodSet
public import NoCompromise.Regularity.GraphGoodBase

@[expose] public section

/-! # Passing the maximal-function bound to the actual projected good graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma graphGoodBase_ae_eq_goodExcessBase_of_fibers
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ)
    (hfib : ∀ᵐ x ∂volume, x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) →
      ∃ p ∈ reducedBoundary E hE hmE ∩ standardCylinder (1 / 2), graphProjectionN 2 p = x) :
    (graphGoodBase E hE hmE c γ : Set (EuclideanSpace ℝ (Fin 2))) =ᵐ[volume]
      (goodExcessBase E hE hmE c γ : Set (EuclideanSpace ℝ (Fin 2))) := by
  filter_upwards [hfib] with x hx
  apply propext
  constructor
  · exact fun h => graphGoodBase_subset_goodExcessBase E hE hmE c γ h
  · intro hg
    obtain ⟨p, hp, he⟩ := hx hg.2
    refine ⟨p, ⟨hp, ?_⟩, he⟩
    change graphProjectionN 2 p ∈ goodExcessBase E hE hmE c γ
    rw [he]
    exact hg

lemma graphGoodBase_complement_measure_of_fibers
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ)
    (hfib : ∀ᵐ x ∂volume, x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) →
      ∃ p ∈ reducedBoundary E hE hmE ∩ standardCylinder (1 / 2), graphProjectionN 2 p = x) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ) =
      volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ goodExcessBase E hE hmE c γ) := by
  apply measure_congr
  filter_upwards [graphGoodBase_ae_eq_goodExcessBase_of_fibers E hE hmE c γ hfib] with x hx
  change (x ∈ graphGoodBase E hE hmE c γ) = (x ∈ goodExcessBase E hE hmE c γ) at hx
  change (x ∈ ball 0 (1 / 2) ∧ x ∉ graphGoodBase E hE hmE c γ) =
    (x ∈ ball 0 (1 / 2) ∧ x ∉ goodExcessBase E hE hmE c γ)
  rw [hx]

lemma graphGoodBase_measure_bound_of_fibers
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hfib : ∀ᵐ x ∂volume, x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) →
      ∃ p ∈ reducedBoundary E hE hmE ∩ standardCylinder (1 / 2), graphProjectionN 2 p = x) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ) ≤
      ENNReal.ofReal (25 / (c * γ ^ 2)) *
        ENNReal.ofReal (cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1)) := by
  rw [graphGoodBase_complement_measure_of_fibers E hE hmE c γ hfib]
  exact good_base_measure_bound E hE hmE hc hγ

lemma reducedBoundary_sdiff_graph_subset_badBase
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c γ : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hfix : ∀ p ∈ graphGoodBoundary E hE hmE c γ, f (graphProjectionN 2 p) = p 2) :
    (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) \
        ((fun x => graphAppendN x (f x)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ⊆
      (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) ∩
        graphProjectionN 2 ⁻¹' (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \
          graphGoodBase E hE hmE c γ) := by
  intro p hp
  refine ⟨hp.1, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using hp.1.2.1
  · intro hg
    have hpG : p ∈ graphGoodBoundary E hE hmE c γ := by
      rw [graphGoodBoundary_eq_restrict_graphGoodBase]
      exact ⟨hp.1, hg⟩
    apply hp.2
    refine ⟨graphProjectionN 2 p, graphGoodBase_subset_ball E hE hmE c γ hg, ?_⟩
    dsimp only
    rw [hfix p hpG]
    exact graphAppendN_projection p

end LiquidDrop
