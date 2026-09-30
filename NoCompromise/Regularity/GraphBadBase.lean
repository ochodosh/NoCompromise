module

public import NoCompromise.Regularity.GraphBadBaseFlux
public import NoCompromise.Regularity.GraphPhaseCaps

@[expose] public section

/-! # Localized bad-base area from actual signed slicing and normal excess -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The squared deviation from the upward normal is twice its signed vertical
defect, with all integrals taken against actual reduced-boundary area. -/
lemma vertical_defect_eq_half_normalExcess
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {A : Set AmbientSpace}
    (hA : MeasurableSet A) :
    (∫ z in reducedBoundary E hE hmE ∩ A,
      (1 - reducedNormal E hE hmE z 2) ∂hausdorffMeasure2 3) =
      (1 / 2 : ℝ) * normalExcessIntegral E hE hmE A (EuclideanSpace.single 2 1) := by
  rw [normalExcessIntegral_eq_area E hE hmE hA, ← integral_const_mul]
  apply setIntegral_congr_fun ((measurableSet_reducedBoundary E hE hmE).inter hA)
  intro z hz
  dsimp only
  rw [norm_sub_sq_real, norm_reducedNormal E hE hmE hz.1]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- Exact area equals base area plus half of the localized normal excess.
This retains the signed cancellation even over bases with multiple jumps. -/
theorem HasGraphCapPhases.area_on_base_eq
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B)
    (hBB : B ⊆ ball 0 (1 / 2)) :
    (hausdorffMeasure2 3).real (reducedBoundary E hE hmE ∩ graphBaseRegion B) =
      volume.real B + (1 / 2 : ℝ) *
        normalExcessIntegral E hE hmE (graphBaseRegion B) (EuclideanSpace.single 2 1) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let A := graphBaseRegion B
  have hA : MeasurableSet A := measurableSet_graphBaseRegion hB
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (isBounded_graphBaseRegion B).measure_lt_top⟩
  have hi : IntegrableOn (fun x => reducedNormal E hE hmE x 2) A μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (((EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).measurable.comp
        (measurable_reducedNormal E hE hmE)).aestronglyMeasurable)
    filter_upwards [ae_restrict_of_ae (ae_mem_reducedBoundary E hE hmE)] with x hx
    exact (PiLp.norm_apply_le (reducedNormal E hE hmE x) 2).trans
      (le_of_eq (norm_reducedNormal E hE hmE hx))
  have he : (fun x => ‖reducedNormal E hE hmE x - EuclideanSpace.single 2 1‖ ^ 2)
      =ᵐ[μ.restrict A] (fun x => 2 - 2 * reducedNormal E hE hmE x 2) := by
    filter_upwards [ae_restrict_of_ae (ae_mem_reducedBoundary E hE hmE)] with x hx
    rw [norm_sub_sq_real, norm_reducedNormal E hE hmE hx]
    simp [EuclideanSpace.inner_single_right]
    ring
  have hf := h.vertical_flux_on_base hE hmE hB hBB
  have hn : normalExcessIntegral E hE hmE A (EuclideanSpace.single 2 1) =
      2 * μ.real A - 2 * volume.real B := by
    rw [normalExcessIntegral, ← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
      integral_congr_ae he, integral_sub (integrable_const (2 : ℝ)) (hi.const_mul 2),
      integral_const_mul, integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
    change μ.real A * 2 - 2 * ∫ x in A, reducedNormal E hE hmE x 2 ∂μ = _
    rw [hf]
    ring
  have hm : μ.real A =
      (hausdorffMeasure2 3).real (reducedBoundary E hE hmE ∩ A) := by
    rw [Measure.real, canonicalPerimeterMeasure_apply_eq_reducedBoundary_area E hE hmE hA,
      inter_comm]
    rfl
  rw [hm] at hn
  change _ = volume.real B + (1 / 2 : ℝ) *
    normalExcessIntegral E hE hmE A (EuclideanSpace.single 2 1)
  linarith

/-- Both inequalities of the bad-base-area lemma, for every Borel base subset
of the half disk. The exceptional graph base is one such choice. -/
theorem HasGraphCapPhases.bad_base_area
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B)
    (hBB : B ⊆ ball 0 (1 / 2)) :
    (hausdorffMeasure2 3).real (reducedBoundary E hE hmE ∩ graphBaseRegion B) ≤
      volume.real B + 3 * (∫ z in reducedBoundary E hE hmE ∩ graphBaseRegion B,
        (1 - reducedNormal E hE hmE z 2) ∂hausdorffMeasure2 3) ∧
    volume.real B + 3 * (∫ z in reducedBoundary E hE hmE ∩ graphBaseRegion B,
        (1 - reducedNormal E hE hmE z 2) ∂hausdorffMeasure2 3) ≤
      volume.real B + (3 / 2 : ℝ) *
        cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  rw [h.area_on_base_eq hE hmE hB hBB,
    vertical_defect_eq_half_normalExcess E hE hmE (measurableSet_graphBaseRegion hB)]
  have hn := normalExcessIntegral_nonneg E hE hmE (graphBaseRegion B)
    (EuclideanSpace.single 2 1)
  have hsub : graphBaseRegion B ⊆ standardCylinder 1 := by
    apply inter_subset_left.trans
    rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
    exact cylinder_mono (by norm_num)
  have hm := normalExcessIntegral_mono E hE hmE (isBounded_standardCylinder 1)
    hsub (EuclideanSpace.single 2 1)
  rw [standardCylinder_eq_cylinder] at hm
  simp only [cylindricalExcess, one_pow, div_one]
  constructor <;> linarith

/-- Full localized bad-base estimate from the actual small-excess hypotheses. -/
theorem bad_base_area :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      ∀ B : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet B → B ⊆ ball 0 (1 / 2) →
      (hausdorffMeasure2 3).real
          (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ graphBaseRegion B) ≤
        volume.real B + 3 * (∫ z in
          reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ graphBaseRegion B,
          (1 - reducedNormal E hE.locallyFinite hE.nullMeasurable z 2) ∂hausdorffMeasure2 3) ∧
      volume.real B + 3 * (∫ z in
          reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ graphBaseRegion B,
          (1 - reducedNormal E hE.locallyFinite hE.nullMeasurable z 2) ∂hausdorffMeasure2 3) ≤
        volume.real B + (3 / 2 : ℝ) *
          cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) := by
  obtain ⟨ε, hε, hp⟩ := graph_phase_caps
  exact ⟨ε, hε, fun E ω hE h0 he B hB hBB =>
    (hp E ω hE h0 he).1.bad_base_area hE.locallyFinite hE.nullMeasurable hB hBB⟩

end LiquidDrop
