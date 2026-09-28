import NoCompromise.DeGiorgi.RadialTests
import NoCompromise.DeGiorgi.NoAtoms
import NoCompromise.Measure.RadialCumulative

/-!
# Radial flux of the perimeter derivative

The radial test identity and the cumulative-measure test identity show that
ball derivatives and density-one spherical fluxes differ by a constant. Both
have vanishing means at the origin, so the constant vanishes. This gives the
exact surface integral and its area bound for almost every positive radius,
simultaneously in all three coordinates, without a Gauss--Green premise.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma tendsto_sphericalSectionFlux_zero (E : Set AmbientSpace) (c : AmbientSpace)
    (i : Fin 3) : Tendsto (sphericalSectionFlux E c i) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (norm_sphericalSectionFlux_le E c i)
  simpa using (show ContinuousAt (fun r : ℝ => 4 * Real.pi * r ^ 2) 0 by fun_prop).tendsto

/-- The distributional derivative on a ball equals its density-one spherical flux
for almost every positive radius. -/
theorem IsAmbientOutwardPerimeterPolar.ae_integral_ball_eq_sphericalSectionFlux
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) (i : Fin 3) :
    (fun r : ℝ => ∫ x in ball c r, -ν x i ∂μ) =ᵐ[volume.restrict (Ioi 0)]
      sphericalSectionFlux E c i := by
  let := h.finiteOnCompacts
  have hfm : Measurable (fun x => -ν x i) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp h.measurable).neg
  have hfi : LocallyIntegrable (fun x => -ν x i) μ :=
    locallyIntegrable_of_ae_norm_le (C := 1) μ hfm.aestronglyMeasurable
      (h.norm_ae.mono fun x hx => by
        simpa only [norm_neg, hx] using PiLp.norm_apply_le (ν x) i)
  let F : ℝ → ℝ := fun r => ∫ x in ball c r, -ν x i ∂μ
  let G : ℝ → ℝ := sphericalSectionFlux E c i
  have hF : LocallyIntegrable F volume := locallyIntegrable_integral_ball_real μ hfm hfi c
  have hG : LocallyIntegrable G volume := locallyIntegrable_sphericalSectionFlux hE c i
  have hF0 : Tendsto F (𝓝 0) (𝓝 0) :=
    tendsto_integral_ball_real_zero μ hfm hfi c (h.measure_singleton c)
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := tendsto_sphericalSectionFlux_zero E c i
  have hmean : Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo 0 r, F t - G t)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_mean_Ioo_zero_of_tendsto_zero
    simpa only [sub_zero] using (hF0.sub hG0).mono_left nhdsWithin_le_nhds
  have hz : (fun r => F r - G r) =ᵐ[volume.restrict (Ioi 0)] fun _ => 0 := by
    apply ae_eq_zero_of_integral_mul_deriv_eq_zero_of_average
      ((hF.sub hG).locallyIntegrableOn _) _ hmean
    intro ψ hψ hcψ hsψ
    have hFi : Integrable (fun r => F r * deriv ψ r) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport (hψ.continuous_deriv le_rfl) hcψ.deriv
    have hGi : Integrable (fun r => G r * deriv ψ r) volume := by
      simpa only [smul_eq_mul] using
        hG.integrable_smul_right_of_hasCompactSupport (hψ.continuous_deriv le_rfl) hcψ.deriv
    change (∫ r in Ioi (0 : ℝ), (F r - G r) * deriv ψ r) = 0
    simp_rw [sub_mul]
    rw [integral_sub hFi.integrableOn hGi.integrableOn]
    have hc := integral_ball_mul_deriv_Ioi μ hfi c hψ hcψ
    have ht := h.radial_test_identity hE c i hψ hcψ hsψ
    dsimp only [F, G]
    rw [hc, ht, neg_neg]
    simp only [mul_comm, sub_self]
  exact hz.mono fun r hr => sub_eq_zero.mp hr

lemma perimeterDerivativeBall_apply (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c : AmbientSpace) (r : ℝ) (i : Fin 3) :
    perimeterDerivativeBall E hE hmE c r i =
      ∫ x in ball c r, -canonicalOutwardPolarDensity E hE hmE x i
        ∂canonicalPerimeterMeasure E hE hmE := by
  have hi := (canonicalPerimeterPolar E hE hmE).locallyIntegrable.neg.integrableOn_isCompact
    (isCompact_closedBall c r)
  have hb := hi.mono_set ball_subset_closedBall
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hb).symm

/-- The radial flux identity holds simultaneously for all three coordinates. -/
theorem ae_perimeterDerivativeBall_eq_sphericalSectionFlux (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      perimeterDerivativeBall E hE hmE c r i = sphericalSectionFlux E c i r := by
  rw [ae_all_iff]
  intro i
  filter_upwards [(canonicalPerimeterPolar E hE hmE).ae_integral_ball_eq_sphericalSectionFlux
    hmE c i] with r hr
  rw [perimeterDerivativeBall_apply]
  exact hr

/-- A uniform quadratic bound for all coordinates at almost every positive radius. -/
theorem ae_abs_perimeterDerivativeBall_apply_le (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      |perimeterDerivativeBall E hE hmE c r i| ≤ 4 * Real.pi * r ^ 2 := by
  filter_upwards [ae_perimeterDerivativeBall_eq_sphericalSectionFlux E hE hmE c] with r hr
  intro i
  rw [hr i, ← Real.norm_eq_abs]
  exact norm_sphericalSectionFlux_le E c i r

/-- The coordinate ball derivative is the exact flux over the density-one section. -/
theorem ae_perimeterDerivativeBall_eq_surface_integral (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      perimeterDerivativeBall E hE hmE c r i =
        ∫ y in densityOne E ∩ sphere c r, (y - c) i / r ∂hausdorffMeasure2 3 := by
  filter_upwards [ae_perimeterDerivativeBall_eq_sphericalSectionFlux E hE hmE c] with r hr
  intro i
  rw [hr i, sphericalSectionFlux, integral_indicator (measurableSet_densityOne hmE),
    Measure.restrict_restrict (measurableSet_densityOne hmE)]

/-- The sharp absolute bound uses the area of the density-one spherical section. -/
theorem ae_abs_perimeterDerivativeBall_apply_le_sectionArea (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      |perimeterDerivativeBall E hE hmE c r i| ≤
        (hausdorffMeasure2 3 (densityOne E ∩ sphere c r)).toReal := by
  filter_upwards [ae_perimeterDerivativeBall_eq_sphericalSectionFlux E hE hmE c,
    ae_restrict_mem measurableSet_Ioi] with r hr hrp
  intro i
  rw [hr i, ← Real.norm_eq_abs]
  exact norm_sphericalSectionFlux_le_sectionArea hmE c i hrp

end LiquidDrop
