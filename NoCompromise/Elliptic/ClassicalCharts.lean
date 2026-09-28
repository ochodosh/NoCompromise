import NoCompromise.DeGiorgi.SmoothBoundary

/-!
# Classical directional integration in one boundary chart

The graph FTC formula is expressed using the topological boundary measure.
A prescribed normal field only needs to agree with the actual chart normal on
the chart. These identities use classical graph calculus and measure locality.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop

lemma C1BoundaryChart.IsChartFor.directional_pairing_boundary
    {c : C1BoundaryChart} {D : Set AmbientSpace} (hc : c.IsChartFor D)
    (hD : MeasurableSet D) {ν : AmbientSpace → AmbientSpace}
    (hν : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
      x ∈ c.region → ν x = c.outwardNormal x)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ c.region) (v : AmbientSpace) :
    (∫ x in D, fderiv ℝ φ x v) =
      ∫ x, φ x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  rw [hc.directional_pairing hD hφ hcφ hsφ v]
  have hzero (w : AmbientSpace → AmbientSpace) (x : AmbientSpace) (hx : x ∉ c.region) :
      φ x * inner ℝ v (w x) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), zero_mul]
  calc
    _ = ∫ x in c.region, φ x * inner ℝ v (c.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict c.graphSurface :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero c.outwardNormal)).symm
    _ = ∫ x in c.region, φ x * inner ℝ v (c.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
      rw [hc.boundaryArea_restrict]
    _ = ∫ x in c.region, φ x * inner ℝ v (ν x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hν, ae_restrict_mem c.isOpen_region.measurableSet]
        with x hx hxr
      rw [hx hxr]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ν)

lemma integral_directional_derivative_interior {D : Set AmbientSpace}
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : AmbientSpace) :
    (∫ x in D, fderiv ℝ φ x v) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_compact_scalar_fderiv_eq_zero hφ hcφ v
  · intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hsφ h)), zero_apply]

lemma boundary_pairing_eq_zero_of_interior_support {D : Set AmbientSpace} (hD : IsOpen D)
    {φ : AmbientSpace → ℝ} (hsφ : tsupport φ ⊆ D)
    (ν : AmbientSpace → AmbientSpace) (v : AmbientSpace) :
    (∫ x, φ x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D)) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
  have hnot : x ∉ D := by
    rw [frontier, hD.interior_eq] at hx
    exact hx.2
  simp only [image_eq_zero_of_notMem_tsupport (fun h => hnot (hsφ h)), zero_mul, Pi.zero_apply]

end LiquidDrop
