module

public import NoCompromise.Surface.GaussSard
public import NoCompromise.Surface.GaussSardChart
public import NoCompromise.Surface.MergeDisjoint

@[expose] public section

/-!
# `cor:sard-charts` for the Gauss map, and its consequences in chapter 14

`H²`-almost every point of `S²` is a regular value of the unit normal of a compact embedded
surface; this discharges `h_sard_charts` in lem:morse-height and thm:total-curvature-bound.
-/

noncomputable section

open Set MeasureTheory

namespace LiquidDrop

variable {S : Set E₃}

/-- `cor:sard-charts` for the Gauss map (proved): `H²`-almost every point of `S²` is a regular
value of the unit normal `n` of a compact embedded surface. -/
theorem ae_isSurfaceRegularValue_gaussMap {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y :=
  ae_isSurfaceRegularValue_gaussMap_of_chart hS hc
    (fun e P q he hψ _ _ hB => hausdorffMeasure2_gaussMap_critical_chart hS hn e P q he hψ hB)

/-- lem:morse-height (proved): for almost every `v ∈ S²`, `±v` are regular values of the Gauss
map and the height `⟪·, v⟫` is Morse with finitely many critical points, all in `n⁻¹{±v}`. -/
theorem ae_morse_height {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    (hn : IsUnitNormalField S n) :
    ∀ᵐ v ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v ∧
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v) ∧
      IsSurfaceMorse S n (fun x => inner ℝ x v) ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p}.Finite ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p} ⊆ n ⁻¹' {v} ∪ n ⁻¹' {-v} :=
  ae_morse_height_of_sard_charts hS hc hn (ae_isSurfaceRegularValue_gaussMap hS hc hn)

/-- thm:total-curvature-bound, PARTIAL, for a compact connected surface: `∫_Σ κ dH² ≤ 4π`; the
only remaining named hypothesis is `h_total_curvature_index` (thm:total-curvature-index). -/
theorem total_curvature_le_of_index {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_sard_index hS hc hconn hn (ae_isSurfaceRegularValue_gaussMap hS hc hn)
    h_total_curvature_index

end LiquidDrop
