import NoCompromise.BV.RadialTestFamily
import NoCompromise.BV.TraceBounds
import NoCompromise.Sobolev.AnnulusDomain

/-!
# Good radii for locally finite-perimeter sets

Weighted radial flux identities identify the actual interior trace with the
density-one representative on almost every sphere. The original perimeter
measure gives zero mass to almost every sphere as well.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Outward unit radius on a sphere of positive radius. -/
def radialUnitVector (c : AmbientSpace) (r : ℝ) (x : AmbientSpace) : AmbientSpace :=
  r⁻¹ • (x - c)

lemma norm_radialUnitVector {c x : AmbientSpace} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ sphere c r) : ‖radialUnitVector c r x‖ = 1 := by
  rw [radialUnitVector, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
    ← dist_eq_norm, mem_sphere.mp hx, inv_mul_cancel₀ hr.ne']

/-- A good radius has no perimeter atom on its sphere, and the genuine interior
trace equals the density-one representative in every boundary chart. -/
def IsGoodRadius (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c : AmbientSpace) (r : ℝ) : Prop :=
  0 < r ∧ canonicalPerimeterMeasure E hE hmE (sphere c r) = 0 ∧
    ∀ d : C1BoundaryChart, d.IsChartFor (ball c r) →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (sphere c r), z ∈ d.region →
        d.lowerBVTrace (E.indicator (fun _ => (1 : ℝ))) z =
          (densityOne E).indicator (fun _ => (1 : ℝ)) z

/-- The full weighted radial identity determines the actual trace, without
assuming any trace value or any cut identity as a hypothesis. -/
theorem ball_lowerBVTrace_eq_densityOne_of_weighted_radial_tests
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c : AmbientSpace) {r : ℝ} (hr : 0 < r)
    (hw : ∀ (φ : CompactlySupportedContinuousMap AmbientSpace ℝ), ContDiff ℝ 1 φ →
      ∀ i : Fin 3,
        (∫ x in ball c r, φ x * (-canonicalOutwardPolarDensity E hE hmE x i)
          ∂canonicalPerimeterMeasure E hE hmE) +
        (∫ x in ball c r, (densityOne E).indicator
          (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x) =
          weightedSphericalSectionFlux E c φ i r) :
    ∀ d : C1BoundaryChart, d.IsChartFor (ball c r) →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (sphere c r), z ∈ d.region →
        d.lowerBVTrace (E.indicator (fun _ => (1 : ℝ))) z =
          (densityOne E).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let μ := canonicalPerimeterMeasure E hE hmE
  let σ := canonicalOutwardPolarDensity E hE hmE
  have hp := canonicalPerimeterPolar E hE hmE
  let : μ.Regular := hp.regular
  let : IsFiniteMeasureOnCompacts μ := hp.finiteOnCompacts
  have hB := hasC1Boundary_ball c hr
  have hK : IsCompact (frontier (ball c r)) := by
    rw [frontier_ball c hr.ne']
    exact isCompact_sphere c r
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
        -(∫ z, E.indicator (fun _ => (1 : ℝ)) z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z, φ z * (-σ z) i ∂μ := by
    intro i φ hφ
    exact hp.coordinate_eq i φ hφ
  obtain ⟨T, N, hTi, hNm, hNn, hTC, _, hcut⟩ :=
    hB.exists_integrable_trace_cut_pairing isOpen_ball hK hf hp.locallyIntegrable.neg hpair
  have hTpos : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier (ball c r)), 0 ≤ T z :=
    hB.lowerTrace_mem_closed_ae (S := Ici (0 : ℝ)) hK isClosed_Ici (by simp)
      (fun z => by by_cases hz : z ∈ E <;> simp [hz]) hTC
  rw [frontier_ball c hr.ne'] at hTi hNn hTC hcut hTpos
  let ρ := (hausdorffMeasure2 3).restrict (sphere c r)
  let : IsFiniteMeasure ρ := ⟨by
    rw [Measure.restrict_apply_univ, hausdorffMeasure2_sphere c hr]
    exact ENNReal.ofReal_lt_top⟩
  let A : AmbientSpace → AmbientSpace := fun z => T z • N z
  let B : AmbientSpace → AmbientSpace := (densityOne E).indicator (radialUnitVector c r)
  have hAi : Integrable A ρ := hTi.smul_bdd 1 hNm.aestronglyMeasurable
    (hNn.mono fun _ hz => hz.le)
  have hBm : Measurable B := ((show Continuous (radialUnitVector c r) by
    unfold radialUnitVector
    fun_prop).measurable.indicator (measurableSet_densityOne hmE))
  have hBn : ∀ᵐ z ∂ρ, ‖B z‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with z hz
    by_cases he : z ∈ densityOne E
    · simpa only [B, indicator_of_mem he, norm_radialUnitVector hr hz] using le_refl (1 : ℝ)
    · simp only [B, indicator_of_notMem he, norm_zero, zero_le_one]
  have hBi : Integrable B ρ := Integrable.of_bound hBm.aestronglyMeasurable 1 hBn
  have hAB : A =ᵐ[ρ] B := by
    have he := ae_eq_density_on_of_coordinate_pairings isOpen_univ
      hAi.locallyIntegrable hBi.locallyIntegrable (by
        intro i φ hφ _
        let X : AmbientSpace → AmbientSpace := fun z => φ z • EuclideanSpace.single i 1
        have hdiv (z : AmbientSpace) : divergenceN X z =
            fderiv ℝ φ z (EuclideanSpace.single i 1) := by
          rw [divergenceN_smul hφ contDiff_const]
          simp [divergenceN, inner_gradient_left]
        have ht := hcut X (hφ.smul contDiff_const) φ.hasCompactSupport.smul_right
        simp only [hdiv, X, real_inner_smul_left, EuclideanSpace.inner_single_left,
          one_mul, conj_trivial] at ht
        have hvol : (∫ z in ball c r, E.indicator (fun _ => (1 : ℝ)) z *
            fderiv ℝ φ z (EuclideanSpace.single i 1)) =
            ∫ z in ball c r, (densityOne E).indicator
              (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) z := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae (densityOne_ae_eq (by norm_num : 0 < 3) hmE)]
            with z hz
          by_cases he : z ∈ E
          · have hd : z ∈ densityOne E := hz.mpr he
            simp only [indicator_of_mem he, indicator_of_mem hd, one_mul]
          · have hd : z ∉ densityOne E := fun hh => he (hz.mp hh)
            simp only [indicator_of_notMem he, indicator_of_notMem hd, zero_mul]
        rw [hvol] at ht
        have hwφ := hw φ hφ i
        have hsurface : (∫ z, T z * (φ z * N z i) ∂ρ) =
            weightedSphericalSectionFlux E c φ i r := by
          simp only [Pi.neg_apply, PiLp.neg_apply] at ht
          linarith
        calc
          _ = ∫ z, T z * (φ z * N z i) ∂ρ := by
            apply integral_congr_ae
            exact ae_of_all _ fun z => by
              simp only [A, PiLp.smul_apply, smul_eq_mul]
              ring
          _ = weightedSphericalSectionFlux E c φ i r := hsurface
          _ = _ := by
            apply integral_congr_ae
            exact ae_of_all _ fun z => by
              by_cases hz : z ∈ densityOne E
              · simp only [B, indicator_of_mem hz, radialUnitVector, PiLp.smul_apply,
                  smul_eq_mul, div_eq_mul_inv]
                ring
              · simp only [B, indicator_of_notMem hz, PiLp.zero_apply, mul_zero])
    simpa only [Measure.restrict_univ] using he
  have hTeq : T =ᵐ[ρ] (densityOne E).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hAB, hTpos, hNn, ae_restrict_mem isClosed_sphere.measurableSet]
      with z hz hpos hn hzs
    have he := congrArg norm hz
    simp only [A, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hn, mul_one] at he
    by_cases hez : z ∈ densityOne E
    · simpa only [B, indicator_of_mem hez, norm_radialUnitVector hr hzs] using he
    · simpa only [B, indicator_of_notMem hez, norm_zero] using he
  intro d hd
  filter_upwards [hTeq, hTC d hd] with z hz htz
  intro hzd
  exact (htz hzd).symm.trans hz

/-- Blueprint `lem:good-radius-ae`: almost every positive radius is good. -/
theorem ae_isGoodRadius (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), IsGoodRadius E hE hmE c r := by
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  filter_upwards [hp.ae_all_weighted_radial_tests hmE c,
    ae_restrict_of_ae (ae_measure_sphere_eq_zero (canonicalPerimeterMeasure E hE hmE) c),
    ae_restrict_mem measurableSet_Ioi] with r hw hnull hr
  exact ⟨hr, hnull, ball_lowerBVTrace_eq_densityOne_of_weighted_radial_tests hE hmE c hr hw⟩

end LiquidDrop
