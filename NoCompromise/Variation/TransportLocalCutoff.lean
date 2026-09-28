import NoCompromise.BV.StrictApprox
import NoCompromise.BV.Coarea
import NoCompromise.BV.CompactnessIndicators

/-!
# Cutting off a set of locally finite perimeter in an open domain

If `E` has locally finite perimeter in `U` and `closedBall x₀ (2 r) ⊆ U`, some set with
globally locally finite perimeter agrees with `E` on `ball x₀ r`: a superlevel set
`{t < ζ 1_E}` of a C¹ bump times the indicator, for a coarea-generic `t ∈ (0, 1)`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Blueprint cutoff step for `thm:transport-perimeter`. -/
theorem exists_globalPerimeter_eq_on_ball {E U : Set AmbientSpace} (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {x₀ : AmbientSpace} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ (2 * r) ⊆ U) :
    ∃ E' : Set AmbientSpace, HasLocallyFinitePerimeter E' ∧ NullMeasurableSet E' volume ∧
      E' ∩ ball x₀ r = E ∩ ball x₀ r := by
  let ζ : ContDiffBump x₀ := ⟨r, 2 * r, hr, by linarith⟩
  let g : AmbientSpace → ℝ := E.indicator (fun _ => (1 : ℝ))
  let f : AmbientSpace → ℝ := fun x => ζ x * g x
  have hg : IsLocallyBVOn g U := hE.isLocallyBVOn_indicator hmE
  obtain ⟨ρ, σ, hρ, hpolar, -⟩ := exists_polar_representation_with_variation hU hg
  have hζ1 : ContDiff ℝ 1 ζ := ζ.contDiff
  have hsζ : tsupport ζ ⊆ U := by rw [ζ.tsupport_eq]; exact hsub
  have hvar : variation f univ < ∞ :=
    (hpolar.variation_mul_le hg.1 hζ1 ζ.hasCompactSupport hsζ).trans_lt ENNReal.ofReal_lt_top
  have hfloc : LocallyIntegrable f :=
    (locallyIntegrable_indicator_one hmE).continuous_mul ζ.continuous
  have hf : IsLocallyBVOn f univ :=
    ⟨hfloc.locallyIntegrableOn univ, fun A _ _ _ =>
      (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt hvar⟩
  have hae := ae_perimeter_superlevel_lt_top isOpen_univ hf hvar
  have : NeBot (ae (volume.restrict (Ioo (0 : ℝ) 1))) := ae_neBot.2 (by simp)
  obtain ⟨t, ht, htI⟩ := ((ae_restrict_of_ae (s := Ioo (0 : ℝ) 1) hae).and
    (ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)))).exists
  have hgm : AEMeasurable g volume := aemeasurable_const.indicator₀ hmE
  have hfm : AEMeasurable f volume := ζ.continuous.aemeasurable.mul hgm
  refine ⟨{x | t < f x}, fun A hA _ =>
      (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt ht,
    nullMeasurableSet_lt aemeasurable_const hfm, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxB⟩
    refine ⟨?_, hxB⟩
    by_contra hxE
    have : f x = 0 := by simp [f, g, hxE]
    linarith [htI.1]
  · rintro ⟨hxE, hxB⟩
    refine ⟨?_, hxB⟩
    have h1 : ζ x = 1 := ζ.one_of_mem_closedBall (ball_subset_closedBall hxB)
    have : f x = 1 := by simp [f, g, hxE, h1]
    change t < f x
    rw [this]
    exact htI.2

end LiquidDrop
