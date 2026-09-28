import NoCompromise.Surface.TotalCurvatureIndex
import NoCompromise.Surface.SublevelClosure

/-!
# The total curvature bound with thm:total-curvature-index discharged

`total_curvature_le_of_merge_disjoint_of_index` is thm:total-curvature-bound for a compact
connected smooth embedded surface with the named hypotheses `h_total_curvature_index`
(thm:total-curvature-index, `total_curvature_index_integrable_and_eq`) and `h_sard_charts`
(`ae_isSurfaceRegularValue_gaussMap_of_areaFormula`) of `total_curvature_le_of_merge_disjoint`
discharged. The remaining named hypothesis is `h_merge_disjoint` (lem:merge-disjoint), exactly as
in `total_curvature_le_of_merge_disjoint`.
-/

noncomputable section
open MeasureTheory Set
namespace LiquidDrop

variable {S : Set E₃}

/-- thm:total-curvature-bound, PARTIAL: `∫_Σ κ dH² ≤ 4π` for a compact connected smooth embedded
surface, modulo only `h_merge_disjoint` (lem:merge-disjoint). -/
theorem total_curvature_le_of_merge_disjoint_of_index {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_merge_disjoint : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} →
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_merge_disjoint hS hc hconn hn
    (ae_isSurfaceRegularValue_gaussMap_of_areaFormula hS hc hn) h_merge_disjoint
    (total_curvature_index_integrable_and_eq hS hc hn)

end LiquidDrop
