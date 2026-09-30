module

public import NoCompromise.Regularity.FluxDefectPairing
public import NoCompromise.Regularity.FluxDefectApprox
public import NoCompromise.Regularity.Excess

@[expose] public section

/-! # Exact signed vertical flux and the normal-excess defect -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The signed vertical flux equals the base-disk area at every smaller radius.
The cap phases fix the sign; no regular-radius assumption is needed. -/
theorem IsSlabCapConfiguration.vertical_flux_core
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    (∫ x in cylindricalCore r s, reducedNormal E hE hmE x 2
      ∂canonicalPerimeterMeasure E hE hmE) = Real.pi * s ^ 2 := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (standardCylinder r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (isBounded_standardCylinder r).measure_lt_top⟩
  have hn : ∀ᵐ x ∂μ.restrict (standardCylinder r), ‖reducedNormal E hE hmE x 2‖ ≤ 1 := by
    filter_upwards [ae_restrict_of_ae (ae_mem_reducedBoundary E hE hmE)] with x hx
    exact (PiLp.norm_apply_le (reducedNormal E hE hmE x) 2).trans
      (le_of_eq (norm_reducedNormal E hE hmE hx))
  have hm : Measurable (fun x => reducedNormal E hE hmE x 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).measurable.comp
      (measurable_reducedNormal E hE hmE)
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict (standardCylinder r))
    (fun _ => (1 : ℝ))
    (fun j => (((contDiff_fluxDiskCutoff s j).continuous.comp
      (graphProjectionN 2).continuous).measurable.mul hm).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun j => hn.mono fun x hx => by
      change ‖fluxDiskCutoff s j (graphProjectionN 2 x) * reducedNormal E hE hmE x 2‖ ≤ 1
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fluxDiskCutoff_mem_Icc s j _).1]
      exact ((mul_le_mul_of_nonneg_right (fluxDiskCutoff_mem_Icc s j _).2
        (norm_nonneg _))).trans (by simpa only [one_mul] using hx))
    (Eventually.of_forall fun x => (tendsto_fluxDiskCutoff hs (graphProjectionN 2 x)).mul_const
      (reducedNormal E hE hmE x 2))
  have he : (fun x : AmbientSpace =>
      (ball (0 : EuclideanSpace ℝ (Fin 2)) s).indicator (fun _ => (1 : ℝ))
        (graphProjectionN 2 x) * reducedNormal E hE hmE x 2) =
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ < s}.indicator
        (fun x => reducedNormal E hE hmE x 2) := by
    funext x
    by_cases hx : ‖graphProjectionN 2 x‖ < s <;> simp [Set.indicator, mem_ball, hx]
  rw [he, integral_indicator (isOpen_lt (graphProjectionN 2).continuous.norm
    continuous_const).measurableSet, Measure.restrict_restrict
      (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).measurableSet] at ht
  have ht' : Tendsto (fun j => ∫ x in standardCylinder r,
      fluxDiskCutoff s j (graphProjectionN 2 x) * reducedNormal E hE hmE x 2 ∂μ)
      atTop (𝓝 (Real.pi * s ^ 2)) := by
    have heq (j : ℕ) := h.vertical_flux_test (contDiff_fluxDiskCutoff s j)
      (hasCompactSupport_fluxDiskCutoff hs.le j)
      ((tsupport_fluxDiskCutoff hs.le j).trans (closedBall_subset_ball hsr))
    exact (tendsto_integral_fluxDiskCutoff hs).congr'
      (Eventually.of_forall fun j => (heq j).symm)
  exact tendsto_nhds_unique ht ht'

/-- The exact excess defect equals twice the excess perimeter over a flat disk. -/
theorem IsSlabCapConfiguration.normalExcess_core_eq_perimeter_defect
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    (1 / 2 : ℝ) * normalExcessIntegral E hE hmE (cylindricalCore r s)
      (EuclideanSpace.single 2 1) =
        (perimeterIn E (cylindricalCore r s)).toReal - Real.pi * s ^ 2 := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let A := cylindricalCore r s
  have hA : IsOpen A := isOpen_cylindricalCore r s
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ, A, cylindricalCore] using
      ((isBounded_standardCylinder r).subset
        (show cylindricalCore r s ⊆ standardCylinder r from inter_subset_right)).measure_lt_top⟩
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
  have hflux := h.vertical_flux_core hs hsr
  change (1 / 2 : ℝ) * normalExcessIntegral E hE hmE A (EuclideanSpace.single 2 1) = _
  rw [normalExcessIntegral, ← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    integral_congr_ae he, integral_sub (integrable_const (2 : ℝ)) (hi.const_mul 2),
    integral_const_mul, integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  change (1 / 2 : ℝ) * (μ.real A * 2 - 2 * ∫ x in A, reducedNormal E hE hmE x 2 ∂μ) = _
  rw [hflux]
  have hm : μ.real A = (perimeterIn E A).toReal := by
    rw [Measure.real, canonicalPerimeterMeasure_open E hE hmE hA]
  rw [hm]
  ring

/-- Both clauses of blueprint `lem:flux-defect`, at arbitrary scale and every
strictly smaller positive base radius. The flux uses reduced-boundary area. -/
theorem IsSlabCapConfiguration.flux_defect
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    (∫ x in cylindricalCore r s,
      inner ℝ (reducedNormal E hE hmE x) (EuclideanSpace.single 2 1)
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) = Real.pi * s ^ 2 ∧
    (1 / 2 : ℝ) * normalExcessIntegral E hE hmE (cylindricalCore r s)
      (EuclideanSpace.single 2 1) =
        (perimeterIn E (cylindricalCore r s)).toReal - Real.pi * s ^ 2 := by
  refine ⟨?_, h.normalExcess_core_eq_perimeter_defect hs hsr⟩
  have hf := h.vertical_flux_core hs hsr
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE] at hf
  simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hf

end LiquidDrop
