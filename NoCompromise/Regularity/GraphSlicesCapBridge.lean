module

public import NoCompromise.Regularity.GraphSlicesPhases
public import NoCompromise.Regularity.GraphPhaseCapsGeometry

@[expose] public section

/-! # The established graph cap phases feed the actual BV slice theorem -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma graphLowerCapRegion_eq_vertical_band : graphLowerCapRegion =
    {z : AmbientSpace | graphProjectionN 2 z ∈ ball 0 (3 / 4) ∧
      z 2 ∈ Ioo (-(3 / 4)) (-(1 / 4))} := by
  ext z
  simp only [graphLowerCapRegion, lowerSlabRegion, mem_inter_iff, mem_preimage,
    mem_ofPred_eq, mem_Ioo]
  change (_ ∧ -(3 / 4 : ℝ) < z 2 ∧ z 2 < 0 - 1 / 3 * (3 / 4)) ↔ _
  norm_num

lemma graphUpperCapRegion_eq_vertical_band : graphUpperCapRegion =
    {z : AmbientSpace | graphProjectionN 2 z ∈ ball 0 (3 / 4) ∧
      z 2 ∈ Ioo (1 / 4) (3 / 4)} := by
  ext z
  simp only [graphUpperCapRegion, upperSlabRegion, mem_inter_iff, mem_preimage,
    mem_ofPred_eq, mem_Ioo]
  change (_ ∧ 0 + 1 / 3 * (3 / 4 : ℝ) < z 2 ∧ z 2 < 3 / 4) ↔ _
  norm_num

/-- The actual cap theorem supplies all hypotheses of the signed slice theorem. -/
theorem HasGraphCapPhases.exists_oriented_slices
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∃ τ s κ σ g,
      IsDirectionalJumpDisintegration (E.indicator (fun _ => (1 : ℝ)))
        (LinearIsometryEquiv.refl ℝ AmbientSpace) τ s κ σ g ∧
      ∀ᵐ p : EuclideanSpace ℝ (Fin 2), p ∈ ball 0 (3 / 4) →
        IsBinaryBVRepresentativeOn
          (fun t => E.indicator (fun _ => (1 : ℝ)) (graphAppendN p t))
          (g p (-(3 / 4)) (3 / 4)) (-(3 / 4)) (3 / 4) ∧
        {t ∈ Ioo (-(1 / 2)) (1 / 2) |
          oneDimensionalJump (g p (-(3 / 4)) (3 / 4)) t ≠ 0}.Finite ∧
        (∫ t in Ioo (-(1 / 2)) (1 / 2), σ p t ∂κ p) = -1 ∧
        -(∑ᶠ t : ℝ, (Ioo (-(1 / 2)) (1 / 2)).indicator
          (oneDimensionalJump (g p (-(3 / 4)) (3 / 4))) t) = 1 := by
  apply hE.exists_oriented_vertical_slices hmE measurableSet_ball
  · simpa only [graphLowerCapRegion_eq_vertical_band] using h.1
  · simpa only [graphUpperCapRegion_eq_vertical_band] using h.2

end LiquidDrop
