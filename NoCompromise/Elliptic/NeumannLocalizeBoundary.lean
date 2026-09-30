module

public import NoCompromise.Elliptic.NeumannLocalizeTests
public import NoCompromise.DeGiorgi.SmoothBoundary

@[expose] public section

/-!
# The boundary integral in a rigid graph chart

The existing C¹ graph area theorem applies without a global Lipschitz bound.
The local frontier identity identifies the two surface measures on the chart.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient

namespace LiquidDrop

/-- The boundary integral in graph coordinates for a function supported in the
chart region. The identity holds for totalized integrals, so no additional
continuity, compactness, or integrability premise is needed. -/
theorem C1BoundaryChart.IsChartFor.boundary_integral_eq
    {D : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor D)
    {g : AmbientSpace → ℝ} (hg : tsupport g ⊆ c.region) :
    (∫ z, g z ∂(hausdorffMeasure2 3).restrict (frontier D)) =
      ∫ y : EuclideanSpace ℝ (Fin 2),
        g (c.placement (graphMapN c.height y)) * Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) := by
  have hz (z : AmbientSpace) (hz : z ∉ c.region) : g z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hg h))
  calc
    _ = ∫ z, g z ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero
          (μ := (hausdorffMeasure2 3).restrict c.graphSurface) hz,
        hc.boundaryArea_restrict]
    _ = ∫ z, g (c.placement z) ∂smoothGraphArea c.height := by
      have ha : MeasurableEmbedding (c.placement : AmbientSpace → AmbientSpace) :=
        c.placement.toHomeomorph.measurableEmbedding
      rw [C1BoundaryChart.graphSurface, hausdorffMeasure2_restrict_affineIsometry_image,
        ha.integral_map]
      rfl
    _ = _ := by
      rw [integral_smoothGraphArea c.height_contDiff]
      simp only [mul_comm]

/-- The ambient weak identity with its boundary term expressed in a chart.
Continuous representatives of the forcing and flux are immediate instances. -/
theorem IsWeakNeumannSolution.ambient_test_eq_chart
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ c.region) :
    (∫ x in D, inner ℝ (z.gradientLp x) (gradient φ x)) =
      -(∫ x in D, f₀ x * φ x) +
        ∫ y : EuclideanSpace ℝ (Fin 2),
          h₀ (c.placement (graphMapN c.height y)) *
            φ (c.placement (graphMapN c.height y)) *
              Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) := by
  rw [hz.ambient_test_eq hf hh hφ hcφ]
  congr 1
  exact hc.boundary_integral_eq (tsupport_mul_subset_right.trans hsφ)

end LiquidDrop
