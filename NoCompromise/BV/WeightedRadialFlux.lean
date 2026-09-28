import NoCompromise.DeGiorgi.RadialFlux

/-!
# Weighted radial flux for finite-perimeter sets

Compact continuous weights give measurable, locally integrable spherical
fluxes. Compact C¹ weights will identify the complete distribution on almost
every sphere, rather than only its three unweighted coordinate integrals.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The density-one spherical flux with a compact continuous scalar weight. -/
def weightedSphericalSectionFlux (E : Set AmbientSpace) (c : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3) (r : ℝ) : ℝ :=
  ∫ y in sphere c r, (densityOne E).indicator (fun y => φ y * ((y - c) i / r)) y
    ∂hausdorffMeasure2 3

lemma weightedSphericalSectionFlux_eq_zero_of_nonpos (E : Set AmbientSpace)
    (c : AmbientSpace) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (i : Fin 3) {r : ℝ} (hr : r ≤ 0) : weightedSphericalSectionFlux E c φ i r = 0 := by
  rcases lt_or_eq_of_le hr with hr | rfl
  · simp [weightedSphericalSectionFlux, sphere_eq_empty_of_neg hr]
  · simp [weightedSphericalSectionFlux]

lemma weightedSphericalSectionFlux_eq_param {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3)
    {r : ℝ} (hr : 0 < r) :
    weightedSphericalSectionFlux E c φ i r =
      ∫ p in sphereParamDomain, (r ^ 2 * |Real.sin (p 1)|) *
        (densityOne E).indicator (fun y => φ y * ((y - c) i / r))
          (c + r • sphereParam p) := by
  exact integral_sphere_eq_param c hr
    (((φ.continuous.measurable.mul (by fun_prop)).indicator
      (measurableSet_densityOne hE)).stronglyMeasurable)

lemma measurable_weightedSphericalSectionFlux {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3) :
    Measurable (weightedSphericalSectionFlux E c φ i) := by
  classical
  have hj : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      (z.1 ^ 2 * |Real.sin (z.2 1)|) *
        (densityOne E).indicator (fun y => φ y * ((y - c) i / z.1))
          (c + z.1 • sphereParam z.2)) := by
    have hz : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
        c + z.1 • sphereParam z.2) :=
      (continuous_const.add
        (continuous_fst.smul (lipschitzWith_sphereParam.continuous.comp continuous_snd))).measurable
    apply Measurable.mul (by fun_prop)
    change Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      if c + z.1 • sphereParam z.2 ∈ densityOne E then
        φ (c + z.1 • sphereParam z.2) * ((c + z.1 • sphereParam z.2 - c) i / z.1) else 0)
    apply Measurable.ite ((measurableSet_densityOne hE).preimage hz) _ measurable_const
    exact (φ.continuous.measurable.comp hz).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp (hz.sub_const c)).div measurable_fst)
  have hf := hj.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict sphereParamDomain)
  have heq : weightedSphericalSectionFlux E c φ i = fun r => if 0 < r then
      ∫ p in sphereParamDomain, (r ^ 2 * |Real.sin (p 1)|) *
        (densityOne E).indicator (fun y => φ y * ((y - c) i / r))
          (c + r • sphereParam p) else 0 := by
    funext r
    split_ifs with hr
    · exact weightedSphericalSectionFlux_eq_param hE c φ i hr
    · exact weightedSphericalSectionFlux_eq_zero_of_nonpos E c φ i (le_of_not_gt hr)
  rw [heq]
  exact Measurable.ite measurableSet_Ioi hf.measurable measurable_const

lemma norm_weightedSphericalSectionFlux_le (E : Set AmbientSpace) (c : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3) (r : ℝ) :
    ‖weightedSphericalSectionFlux E c φ i r‖ ≤
      ‖φ.toBoundedContinuousFunction‖ * (4 * Real.pi * r ^ 2) := by
  by_cases hr : 0 < r
  · let : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (sphere c r)) := ⟨by
      rw [Measure.restrict_apply_univ, hausdorffMeasure2_sphere c hr]
      exact ENNReal.ofReal_lt_top⟩
    have hb : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (sphere c r),
        ‖(densityOne E).indicator (fun y => φ y * ((y - c) i / r)) y‖ ≤
          ‖φ.toBoundedContinuousFunction‖ := by
      filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with y hy
      by_cases he : y ∈ densityOne E
      · rw [indicator_of_mem he, norm_mul]
        have hq : ‖(y - c) i / r‖ ≤ (1 : ℝ) := by
          rw [norm_div, Real.norm_of_nonneg hr.le]
          apply (div_le_one hr).mpr
          simpa only [← dist_eq_norm, mem_sphere.mp hy] using PiLp.norm_apply_le (y - c) i
        exact (mul_le_mul_of_nonneg_left hq (norm_nonneg _)).trans
          (by simpa using φ.toBoundedContinuousFunction.norm_coe_le_norm y)
      · simp only [indicator_of_notMem he, norm_zero, norm_nonneg]
    have hh := norm_integral_le_of_norm_le_const hb
    have hnonneg : 0 ≤ 4 * Real.pi * r ^ 2 := by positivity
    simpa only [weightedSphericalSectionFlux, measureReal_def, Measure.restrict_apply_univ,
      hausdorffMeasure2_sphere c hr, ENNReal.toReal_ofReal hnonneg] using hh
  · rw [weightedSphericalSectionFlux_eq_zero_of_nonpos E c φ i (le_of_not_gt hr), norm_zero]
    positivity

lemma locallyIntegrable_weightedSphericalSectionFlux {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3) :
    LocallyIntegrable (weightedSphericalSectionFlux E c φ i) volume := by
  have hc : Continuous (fun r : ℝ =>
      ‖φ.toBoundedContinuousFunction‖ * (4 * Real.pi * r ^ 2)) := by fun_prop
  apply hc.locallyIntegrable.mono
    (measurable_weightedSphericalSectionFlux hE c φ i).aestronglyMeasurable
  exact Eventually.of_forall fun r =>
    (norm_weightedSphericalSectionFlux_le E c φ i r).trans (le_abs_self _)

lemma tendsto_weightedSphericalSectionFlux_zero (E : Set AmbientSpace)
    (c : AmbientSpace) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3) :
    Tendsto (weightedSphericalSectionFlux E c φ i) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (norm_weightedSphericalSectionFlux_le E c φ i)
  simpa using (show ContinuousAt (fun r : ℝ =>
    ‖φ.toBoundedContinuousFunction‖ * (4 * Real.pi * r ^ 2)) 0 by fun_prop).tendsto

/-- Testing the original perimeter derivative with a weighted radial function
produces the radial derivative identity, including the derivative of the weight. -/
theorem IsAmbientOutwardPerimeterPolar.weighted_radial_test_identity
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (hφ : ContDiff ℝ 1 φ) (i : Fin 3) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ioi 0) :
    (∫ x, ψ (dist x c) * (φ x * (-ν x i)) ∂μ) +
      (∫ x, ψ (dist x c) *
        (E.indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x (EuclideanSpace.single i 1))) =
        -(∫ r in Ioi (0 : ℝ), deriv ψ r * weightedSphericalSectionFlux E c φ i r) := by
  let ρ : AmbientSpace → ℝ := fun x => ψ (dist x c)
  have hρ : ContDiff ℝ 1 ρ := contDiff_radial_test hψ hsψ c
  have hcρ : HasCompactSupport ρ := hasCompactSupport_radial_test hcψ c
  let Φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun x => φ x * ρ x, φ.continuous.mul hρ.continuous⟩, φ.hasCompactSupport.mul_right⟩
  have hp := h.coordinate_eq i Φ (hφ.mul hρ)
  let q₁ : AmbientSpace → ℝ := fun x => φ x * fderiv ℝ ρ x (EuclideanSpace.single i 1)
  let q₂ : AmbientSpace → ℝ := fun x => ρ x * fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hq₁ : Continuous q₁ := φ.continuous.mul
    ((hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hq₂ : Continuous q₂ := hρ.continuous.mul
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hi₁ : IntegrableOn q₁ E volume :=
    (hq₁.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right).integrableOn
  have hi₂ : IntegrableOn q₂ E volume :=
    (hq₂.integrable_of_hasCompactSupport hcρ.mul_right).integrableOn
  have heq : (fun x => E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ Φ x (EuclideanSpace.single i 1)) = E.indicator (fun x => q₁ x + q₂ x) := by
    funext x
    by_cases hx : x ∈ E
    · simp only [indicator_of_mem hx, one_mul]
      change fderiv ℝ (fun y => φ y * ρ y) x _ = _
      rw [fderiv_fun_mul (hφ.differentiable one_ne_zero x)
        (hρ.differentiable one_ne_zero x)]
      simp only [add_apply, smul_apply, smul_eq_mul, q₁, q₂]
    · simp only [indicator_of_notMem hx, zero_mul]
  have hp' : (∫ x, ψ (dist x c) * (φ x * (-ν x i)) ∂μ) =
      -(∫ x in E, q₁ x) - ∫ x in E, q₂ x := by
    rw [heq, integral_indicator₀ hE, integral_add hi₁ hi₂] at hp
    have he : (∫ x, Φ x * (-ν x i) ∂μ) =
        ∫ x, ψ (dist x c) * (φ x * (-ν x i)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by change (φ x * ψ (dist x c)) * _ = _; ring
    rw [he] at hp
    linarith
  have hsecond : (∫ x, ψ (dist x c) *
      (E.indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x (EuclideanSpace.single i 1))) =
      ∫ x in E, q₂ x := by
    rw [← integral_indicator₀ hE]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ E <;> simp [hx, q₂, ρ]
  rw [hp', hsecond, sub_add_cancel]
  congr 1
  have hmi : Measurable ((densityOne E).indicator q₁) :=
    hq₁.measurable.indicator (measurableSet_densityOne hE)
  have hi : Integrable ((densityOne E).indicator q₁) volume :=
    (hq₁.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right).indicator
      (measurableSet_densityOne hE)
  calc
    _ = ∫ x, (densityOne E).indicator q₁ x := by
      rw [← integral_indicator₀ hE]
      apply integral_congr_ae
      filter_upwards [densityOne_ae_eq (by norm_num : 0 < 3) hE] with x hx
      by_cases he : x ∈ E
      · have hd : x ∈ densityOne E := hx.mpr he
        simp only [indicator_of_mem he, indicator_of_mem hd]
      · simp only [indicator_of_notMem he,
          indicator_of_notMem (show x ∉ densityOne E from fun hh => he (hx.mp hh))]
    _ = ∫ r in Ioi (0 : ℝ), ∫ y in sphere c r,
        (densityOne E).indicator q₁ y ∂hausdorffMeasure2 3 :=
      integral_radial_disintegration c hmi.stronglyMeasurable hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      unfold weightedSphericalSectionFlux
      rw [← integral_const_mul]
      apply setIntegral_congr_fun isClosed_sphere.measurableSet
      intro y hy
      have hd : dist y c = r := hy
      by_cases he : y ∈ densityOne E
      · simp only [indicator_of_mem he, q₁, ρ,
          fderiv_radial_test_coordinate hψ hsψ, hd]
        ring
      · simp only [indicator_of_notMem he, mul_zero]

/-- The complete weighted radial flux identity holds for almost every positive
radius. The derivative of the weight is the ordinary volume term. -/
theorem IsAmbientOutwardPerimeterPolar.ae_weighted_integral_ball_eq_sphericalSectionFlux
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (hφ : ContDiff ℝ 1 φ) (i : Fin 3) :
    (fun r : ℝ => (∫ x in ball c r, φ x * (-ν x i) ∂μ) +
      ∫ x in ball c r, (densityOne E).indicator
        (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x) =ᵐ[volume.restrict (Ioi 0)]
      weightedSphericalSectionFlux E c φ i := by
  let := h.finiteOnCompacts
  let a : AmbientSpace → ℝ := fun x => φ x * (-ν x i)
  let b : AmbientSpace → ℝ := (densityOne E).indicator
    (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
  have ham : Measurable a := φ.continuous.measurable.mul
    (((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp h.measurable).neg)
  have hai : LocallyIntegrable a μ := by
    have hv : LocallyIntegrable (fun x => -ν x i) μ :=
      locallyIntegrable_of_ae_norm_le (C := 1) μ
        (((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp h.measurable).neg
          ).aestronglyMeasurable
        (h.norm_ae.mono fun x hx => by
          simpa only [norm_neg, hx] using PiLp.norm_apply_le (ν x) i)
    have ht := hv.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
    simpa only [a, smul_eq_mul] using! ht.locallyIntegrable
  have hbd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbm : Measurable b := hbd.measurable.indicator (measurableSet_densityOne hE)
  have hbi : LocallyIntegrable b volume :=
    ((hbd.integrable_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i 1))).indicator
        (measurableSet_densityOne hE)).locallyIntegrable
  let F : ℝ → ℝ := fun r => (∫ x in ball c r, a x ∂μ) + ∫ x in ball c r, b x
  let G : ℝ → ℝ := weightedSphericalSectionFlux E c φ i
  have hF : LocallyIntegrable F volume :=
    (locallyIntegrable_integral_ball_real μ ham hai c).add
      (locallyIntegrable_integral_ball_real volume hbm hbi c)
  have hG : LocallyIntegrable G volume := locallyIntegrable_weightedSphericalSectionFlux hE c φ i
  have hF0 : Tendsto F (𝓝 0) (𝓝 0) := by
    simpa only [add_zero] using
      (tendsto_integral_ball_real_zero μ ham hai c (h.measure_singleton c)).add
        (tendsto_integral_ball_real_zero volume hbm hbi c (MeasureTheory.measure_singleton c))
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := tendsto_weightedSphericalSectionFlux_zero E c φ i
  have hmean : Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo 0 r, F t - G t)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_mean_Ioo_zero_of_tendsto_zero
    simpa only [sub_zero] using (hF0.sub hG0).mono_left nhdsWithin_le_nhds
  have hz : (fun r => F r - G r) =ᵐ[volume.restrict (Ioi 0)] fun _ => 0 := by
    apply ae_eq_zero_of_integral_mul_deriv_eq_zero_of_average
      ((hF.sub hG).locallyIntegrableOn _) _ hmean
    intro ψ hψ hcψ hsψ
    have hAi : Integrable (fun r => (∫ x in ball c r, a x ∂μ) * deriv ψ r) volume := by
      simpa only [smul_eq_mul] using
        (locallyIntegrable_integral_ball_real μ ham hai c
          ).integrable_smul_right_of_hasCompactSupport
            (hψ.continuous_deriv le_rfl) hcψ.deriv
    have hBi : Integrable (fun r => (∫ x in ball c r, b x) * deriv ψ r) volume := by
      simpa only [smul_eq_mul] using
        (locallyIntegrable_integral_ball_real volume hbm hbi c
          ).integrable_smul_right_of_hasCompactSupport
            (hψ.continuous_deriv le_rfl) hcψ.deriv
    have hGi : Integrable (fun r => G r * deriv ψ r) volume := by
      simpa only [smul_eq_mul] using
        hG.integrable_smul_right_of_hasCompactSupport (hψ.continuous_deriv le_rfl) hcψ.deriv
    have ha := integral_ball_mul_deriv_Ioi μ hai c hψ hcψ
    have hb := integral_ball_mul_deriv_Ioi volume hbi c hψ hcψ
    have ht := h.weighted_radial_test_identity hE c φ hφ i hψ hcψ hsψ
    have hbe : (∫ x, ψ (dist x c) * b x) =
        ∫ x, ψ (dist x c) *
          (E.indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      apply integral_congr_ae
      filter_upwards [densityOne_ae_eq (by norm_num : 0 < 3) hE] with x hx
      by_cases he : x ∈ E
      · have hd : x ∈ densityOne E := hx.mpr he
        simp only [b, indicator_of_mem he, indicator_of_mem hd, one_mul]
      · simp only [b, indicator_of_notMem he,
          indicator_of_notMem (show x ∉ densityOne E from fun hh => he (hx.mp hh)),
          zero_mul, mul_zero]
    change (∫ r in Ioi (0 : ℝ), (F r - G r) * deriv ψ r) = 0
    simp only [F, sub_mul, add_mul]
    have hsum : IntegrableOn (fun r =>
        (∫ x in ball c r, a x ∂μ) * deriv ψ r +
          (∫ x in ball c r, b x) * deriv ψ r) (Ioi (0 : ℝ)) :=
      (hAi.add hBi).integrableOn
    rw [integral_sub hsum hGi.integrableOn,
      integral_add hAi.integrableOn hBi.integrableOn, ha, hb, hbe]
    dsimp only [a, G] at *
    have hcomm : (∫ r in Ioi (0 : ℝ), weightedSphericalSectionFlux E c φ i r * deriv ψ r) =
        ∫ r in Ioi (0 : ℝ), deriv ψ r * weightedSphericalSectionFlux E c φ i r := by
      congr 1
      funext r
      ring
    rw [hcomm]
    linarith
  exact hz.mono fun r hr => sub_eq_zero.mp hr

end LiquidDrop
