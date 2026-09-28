import NoCompromise.Regularity.CompressionMap
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Bi-Lipschitz bounds for vertical compression on bounded regions -/

noncomputable section
open Set Metric
open scoped NNReal
namespace LiquidDrop

/-- A nonvanishing C¹ compression factor gives a C¹ inverse and both Lipschitz
bounds on every bounded region, in particular every bounded cylindrical annulus. -/
theorem verticalCompression_bilipschitz_on_bounded
    {β : EuclideanSpace ℝ (Fin 2) → ℝ} (hβ : ContDiff ℝ 1 β)
    (hne : ∀ x, β x ≠ 0) (c : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : Bornology.IsBounded S) :
    ∃ L M : ℝ≥0, LipschitzOnWith L (verticalCompression β c) S ∧
      ∀ x ∈ S, ∀ y ∈ S,
        dist x y ≤ M * dist (verticalCompression β c x) (verticalCompression β c y) := by
  have hT := contDiff_verticalCompression hβ c
  have hI := contDiff_verticalCompression (hβ.inv hne) c
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨L, hL⟩ := (hT.contDiffOn (s := closedBall 0 R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨R', hR'⟩ := ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).image
    hT.continuous).isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨M, hM⟩ := (hI.contDiffOn (s := closedBall 0 R')).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨L, M, hL.mono hR, ?_⟩
  intro x hx y hy
  have hh := hM.dist_le_mul _ (hR' ⟨x, hR hx, rfl⟩) _ (hR' ⟨y, hR hy, rfl⟩)
  change dist (verticalCompression (fun y => (β y)⁻¹) c (verticalCompression β c x))
    (verticalCompression (fun y => (β y)⁻¹) c (verticalCompression β c y)) ≤ _ at hh
  simpa only [verticalCompression_inverse β hne c] using hh

end LiquidDrop
