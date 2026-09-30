module

public import NoCompromise.BV.SphericalSlicing
public import NoCompromise.DeGiorgi.PolarDifferentiation

@[expose] public section

/-!
# Radial test fields and spherical-section flux

A compactly supported `C¹` radial test whose support lies in the positive ray is
`C¹` across its center. The coordinate derivative is computed explicitly, and
the ambient polar pairing together with the proved weighted radial disintegration
gives the signed distributional identity for spherical-section flux.

The section uses the Borel density-one representative. Its scalar flux is Borel
and locally integrable, and its absolute value is bounded both by the area of
the section and by `4 * π * r²`. No Gauss--Green or reduced-boundary structure
theorem is used.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma contDiff_radial_test {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : tsupport ψ ⊆ Ioi 0) (c : AmbientSpace) :
    ContDiff ℝ 1 (fun y => ψ (dist y c)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = c
  · subst x
    have hz : (0 : ℝ) ∉ tsupport ψ := fun h => (lt_irrefl (0 : ℝ)) (hs h)
    have he : ψ =ᶠ[𝓝 (0 : ℝ)] (0 : ℝ → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    have hd : Tendsto (fun y : AmbientSpace => dist y c) (𝓝 c) (𝓝 0) := by
      simpa only [ContinuousAt, dist_self] using
        (show ContinuousAt (fun y : AmbientSpace => dist y c) c from
          ((continuous_id : Continuous (fun y : AmbientSpace => y)).dist
            (continuous_const : Continuous (fun _ : AmbientSpace => c))).continuousAt)
    exact contDiffAt_const.congr_of_eventuallyEq (he.comp_tendsto hd)
  · exact hψ.contDiffAt.comp x (contDiffAt_id.dist ℝ contDiffAt_const hx)

lemma hasCompactSupport_radial_test {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ)
    (c : AmbientSpace) : HasCompactSupport (fun y => ψ (dist y c)) := by
  obtain ⟨R, hR⟩ := hψ.isBounded.subset_closedBall 0
  apply HasCompactSupport.intro (isCompact_closedBall c R)
  intro y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have h := hR hm
  apply hy
  simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h

lemma hasFDerivAt_distance {x c : AmbientSpace} (hx : x ≠ c) :
    HasFDerivAt (fun y => dist y c) (‖x - c‖⁻¹ • innerSL ℝ (x - c)) x := by
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hsq : HasFDerivAt (fun y : AmbientSpace => ‖y - c‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (x - c)) x := by
    convert! (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const c) using 1
    simp only [ContinuousLinearMap.comp_id, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat]
  have h := hsq.sqrt (pow_ne_zero 2 hn)
  convert! h using 1
  · funext y
    simp only [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
  · rw [Real.sqrt_sq (norm_nonneg _), smul_smul]
    congr 1
    field_simp

lemma fderiv_radial_test_coordinate {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : tsupport ψ ⊆ Ioi 0) (c x : AmbientSpace) (i : Fin 3) :
    fderiv ℝ (fun y => ψ (dist y c)) x (EuclideanSpace.single i 1) =
      deriv ψ (dist x c) * ((x - c) i / dist x c) := by
  by_cases hx : x = c
  · subst x
    have hz : (0 : ℝ) ∉ tsupport ψ := fun h => (lt_irrefl (0 : ℝ)) (hs h)
    have he : ψ =ᶠ[𝓝 (0 : ℝ)] (0 : ℝ → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    have hd : Tendsto (fun y : AmbientSpace => dist y c) (𝓝 c) (𝓝 0) := by
      simpa only [ContinuousAt, dist_self] using
        (show ContinuousAt (fun y : AmbientSpace => dist y c) c from
          ((continuous_id : Continuous (fun y : AmbientSpace => y)).dist
            (continuous_const : Continuous (fun _ : AmbientSpace => c))).continuousAt)
    have hce : (fun y : AmbientSpace => ψ (dist y c)) =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) :=
      he.comp_tendsto hd
    rw [hce.fderiv_eq]
    simp
  · have hf := (hψ.differentiable one_ne_zero (dist x c)).hasDerivAt.comp_hasFDerivAt x
      (hasFDerivAt_distance hx)
    simp only [Function.comp_def] at hf
    rw [hf.fderiv]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul, dist_eq_norm, div_eq_mul_inv]
    ring

/-- Scalar outward radial flux through a density-one spherical section. -/
def sphericalSectionFlux (E : Set AmbientSpace) (c : AmbientSpace) (i : Fin 3) (r : ℝ) : ℝ :=
  ∫ y in sphere c r, (densityOne E).indicator (fun y => (y - c) i / r) y ∂hausdorffMeasure2 3

lemma sphericalSectionFlux_eq_zero_of_nonpos (E : Set AmbientSpace) (c : AmbientSpace)
    (i : Fin 3) {r : ℝ} (hr : r ≤ 0) : sphericalSectionFlux E c i r = 0 := by
  rcases lt_or_eq_of_le hr with hr | rfl
  · simp [sphericalSectionFlux, sphere_eq_empty_of_neg hr]
  · simp [sphericalSectionFlux]

lemma sphericalSectionFlux_eq_param {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) (i : Fin 3) {r : ℝ} (hr : 0 < r) :
    sphericalSectionFlux E c i r =
      ∫ p in sphereParamDomain, (r ^ 2 * |Real.sin (p 1)|) *
        (densityOne E).indicator (fun y => (y - c) i / r) (c + r • sphereParam p) := by
  exact integral_sphere_eq_param c hr
    (((by fun_prop : Measurable (fun y : AmbientSpace => (y - c) i / r)).indicator
      (measurableSet_densityOne hE)).stronglyMeasurable)

lemma measurable_sphericalSectionFlux {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (i : Fin 3) :
    Measurable (sphericalSectionFlux E c i) := by
  classical
  have hj : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      (z.1 ^ 2 * |Real.sin (z.2 1)|) *
        (densityOne E).indicator (fun y => (y - c) i / z.1) (c + z.1 • sphereParam z.2)) := by
    have hz : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => c + z.1 • sphereParam z.2) :=
      (continuous_const.add
        (continuous_fst.smul (lipschitzWith_sphereParam.continuous.comp continuous_snd))).measurable
    apply Measurable.mul (by fun_prop)
    change Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      if c + z.1 • sphereParam z.2 ∈ densityOne E then
        (c + z.1 • sphereParam z.2 - c) i / z.1 else 0)
    apply Measurable.ite ((measurableSet_densityOne hE).preimage hz) _ measurable_const
    exact ((EuclideanSpace.proj i).measurable.comp (hz.sub_const c)).div measurable_fst
  have hf := hj.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict sphereParamDomain)
  have heq : sphericalSectionFlux E c i = fun r => if 0 < r then
      ∫ p in sphereParamDomain, (r ^ 2 * |Real.sin (p 1)|) *
        (densityOne E).indicator (fun y => (y - c) i / r) (c + r • sphereParam p) else 0 := by
    funext r
    split_ifs with hr
    · exact sphericalSectionFlux_eq_param hE c i hr
    · exact sphericalSectionFlux_eq_zero_of_nonpos E c i (le_of_not_gt hr)
  rw [heq]
  exact Measurable.ite measurableSet_Ioi hf.measurable measurable_const

lemma norm_sphericalSectionFlux_le (E : Set AmbientSpace) (c : AmbientSpace) (i : Fin 3)
    (r : ℝ) : ‖sphericalSectionFlux E c i r‖ ≤ 4 * Real.pi * r ^ 2 := by
  by_cases hr : 0 < r
  · let : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (sphere c r)) := ⟨by
      rw [Measure.restrict_apply_univ, hausdorffMeasure2_sphere c hr]
      exact ENNReal.ofReal_lt_top⟩
    have hb : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (sphere c r),
        ‖(densityOne E).indicator (fun y => (y - c) i / r) y‖ ≤ (1 : ℝ) := by
      filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with y hy
      by_cases he : y ∈ densityOne E
      · rw [indicator_of_mem he, norm_div, Real.norm_of_nonneg hr.le]
        apply (div_le_one hr).mpr
        have hc := PiLp.norm_apply_le (y - c) i
        simpa only [← dist_eq_norm, mem_sphere.mp hy] using hc
      · simp only [indicator_of_notMem he, norm_zero, zero_le_one]
    have h := norm_integral_le_of_norm_le_const hb
    have hnonneg : 0 ≤ 4 * Real.pi * r ^ 2 := by positivity
    simpa only [sphericalSectionFlux, one_mul, measureReal_def, Measure.restrict_apply_univ,
      hausdorffMeasure2_sphere c hr, ENNReal.toReal_ofReal hnonneg] using h
  · rw [sphericalSectionFlux_eq_zero_of_nonpos E c i (le_of_not_gt hr), norm_zero]
    positivity

lemma locallyIntegrable_sphericalSectionFlux {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (i : Fin 3) :
    LocallyIntegrable (sphericalSectionFlux E c i) volume := by
  have hc : Continuous (fun r : ℝ => 4 * Real.pi * r ^ 2) := by fun_prop
  apply hc.locallyIntegrable.mono (measurable_sphericalSectionFlux hE c i).aestronglyMeasurable
  exact Eventually.of_forall fun r => (norm_sphericalSectionFlux_le E c i r).trans (le_abs_self _)

/-- The coordinate radial flux satisfies the defining distributional test identity.
The measure density is `-ν`, where `ν` is the outward perimeter polar field. -/
theorem IsAmbientOutwardPerimeterPolar.radial_test_identity
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) (i : Fin 3) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ioi 0) :
    (∫ x, ψ (dist x c) * (-ν x i) ∂μ) =
      -(∫ r in Ioi (0 : ℝ), deriv ψ r * sphericalSectionFlux E c i r) := by
  let φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun y => ψ (dist y c), (contDiff_radial_test hψ hsψ c).continuous⟩,
      hasCompactSupport_radial_test hcψ c⟩
  have hφ : ContDiff ℝ 1 φ := contDiff_radial_test hψ hsψ c
  have hp := h.coordinate_eq i φ hφ
  change -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ (fun y => ψ (dist y c)) x (EuclideanSpace.single i 1)) =
    (∫ x, ψ (dist x c) * (-ν x i) ∂μ) at hp
  rw [← hp]
  congr 1
  let q : AmbientSpace → ℝ := fun x =>
    fderiv ℝ (fun y => ψ (dist y c)) x (EuclideanSpace.single i 1)
  have hqc : Continuous q :=
    ((contDiff_radial_test hψ hsψ c).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hqint : Integrable q volume := hqc.integrable_of_hasCompactSupport
    ((hasCompactSupport_radial_test hcψ c).fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hmi : Measurable ((densityOne E).indicator q) :=
    hqc.measurable.indicator (measurableSet_densityOne hE)
  have hi : Integrable ((densityOne E).indicator q) volume :=
    hqint.indicator (measurableSet_densityOne hE)
  calc
    _ = ∫ x, (densityOne E).indicator q x := by
      apply integral_congr_ae
      filter_upwards [densityOne_ae_eq (by norm_num : 0 < 3) hE] with x hx
      by_cases he : x ∈ E
      · have hd : x ∈ densityOne E := hx.mpr he
        simp only [indicator_of_mem he, indicator_of_mem hd, one_mul, q]
      · have hd : x ∉ densityOne E := fun h => he (hx.mp h)
        simp only [indicator_of_notMem he, indicator_of_notMem hd, zero_mul]
    _ = ∫ r in Ioi (0 : ℝ), ∫ y in sphere c r,
        (densityOne E).indicator q y ∂hausdorffMeasure2 3 :=
      integral_radial_disintegration c hmi.stronglyMeasurable hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      unfold sphericalSectionFlux
      rw [← integral_const_mul]
      apply setIntegral_congr_fun isClosed_sphere.measurableSet
      intro y hy
      have hd : dist y c = r := hy
      by_cases he : y ∈ densityOne E
      · simp only [indicator_of_mem he, q, fderiv_radial_test_coordinate hψ hsψ, hd]
      · simp only [indicator_of_notMem he, mul_zero]

/-- The scalar flux is bounded by the area of the actual density-one section. -/
lemma norm_sphericalSectionFlux_le_sectionArea {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (i : Fin 3)
    {r : ℝ} (hr : 0 < r) :
    ‖sphericalSectionFlux E c i r‖ ≤
      (hausdorffMeasure2 3 (densityOne E ∩ sphere c r)).toReal := by
  let : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (densityOne E ∩ sphere c r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    apply lt_of_le_of_lt (measure_mono inter_subset_right)
    rw [hausdorffMeasure2_sphere c hr]
    exact ENNReal.ofReal_lt_top⟩
  rw [sphericalSectionFlux, integral_indicator (measurableSet_densityOne hE),
    Measure.restrict_restrict (measurableSet_densityOne hE)]
  have hb : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (densityOne E ∩ sphere c r),
      ‖(y - c) i / r‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem ((measurableSet_densityOne hE).inter
      isClosed_sphere.measurableSet)] with y hy
    rw [norm_div, Real.norm_of_nonneg hr.le]
    apply (div_le_one hr).mpr
    have hc := PiLp.norm_apply_le (y - c) i
    simpa only [← dist_eq_norm, mem_sphere.mp hy.2] using hc
  simpa only [one_mul, measureReal_def, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const hb

end LiquidDrop
