import NoCompromise.Regularity.DeformationOuterWall

/-! # Genuine regular horizontal radii for reverse Poincaré comparison -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma ae_horizontal_wall_zero (μ : Measure AmbientSpace) [SFinite μ] (r : ℝ) :
    ∀ᵐ s : ℝ, μ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ)
    (g := fun x : AmbientSpace => ‖graphProjectionN 2 x‖) (by fun_prop)
  have hn := hc.measure_zero (μ := (volume : Measure ℝ))
  have hae : ∀ᵐ s : ℝ, ¬ 0 < μ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s} := by
    apply ae_iff.mpr
    simpa only [not_not] using hn
  filter_upwards [hae] with s hs
  exact measure_mono_null (fun _ hx => hx.1) (nonpos_iff_eq_zero.mp (le_of_not_gt hs))

lemma exists_regular_horizontal_radius (μ : Measure AmbientSpace) [SFinite μ]
    (r : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ s : ℝ, s ∈ Ioo a b ∧
      μ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0 := by
  exact Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by
      rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero]; linarith)
    (ae_restrict_of_ae (ae_horizontal_wall_zero μ r))

/-- Both regular radii have the fixed separation required by the deformation
estimate, at the original geometric scale. -/
theorem exists_reversePoincare_radii (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r : ℝ} (hr : 0 < r) :
    ∃ σ τ : ℝ, r / 2 < σ ∧ σ < 5 * r / 8 ∧ 7 * r / 8 < τ ∧ τ < r ∧
      canonicalPerimeterMeasure E hE hmE
        {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ |x 2| < r} = 0 ∧
      canonicalPerimeterMeasure E hE hmE
        {x : AmbientSpace | ‖graphProjectionN 2 x‖ = τ ∧ |x 2| < r} = 0 := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  obtain ⟨σ, hσ, hzσ⟩ := exists_regular_horizontal_radius μ r
    (a := r / 2) (b := 5 * r / 8) (by linarith)
  obtain ⟨τ, hτ, hzτ⟩ := exists_regular_horizontal_radius μ r
    (a := 7 * r / 8) (b := r) (by linarith)
  exact ⟨σ, τ, hσ.1, hσ.2, hτ.1, hτ.2, hzσ, hzτ⟩

end LiquidDrop
