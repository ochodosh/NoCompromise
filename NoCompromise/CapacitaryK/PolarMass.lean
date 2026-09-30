module

public import NoCompromise.CapacitaryK.Calculus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Polar-coordinate ingredients for the far-field mass expansion

The sphere measure is `(volume : Measure E3).toSphere`; radial integration
uses Lebesgue measure and the Jacobian `r ^ 2`.

This file supplies the polar formulas, a uniform radial tail estimate,
the sphere mass, and cancellation of the cubic angular model. The uniform
small-parameter estimates for moving radial graphs and the sandwich argument
for the full far-region mass expansion are not yet assembled here.
-/

noncomputable section
open Real Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace LiquidDrop.CapacitaryK

/-- The unit sphere has surface measure `4π` for the polar-coordinate
normalization used by Mathlib. -/
theorem polar_sphere_measure_real :
    (volume : Measure E3).toSphere.real univ = 4 * π := by
  rw [Measure.toSphere_real_apply_univ]
  simp only [E3, finrank_euclideanSpace, Fintype.card_fin, Measure.real,
    EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  norm_num
  ring

/-- The same sphere-mass identity as an extended nonnegative real equality. -/
theorem polar_sphere_measure :
    (volume : Measure E3).toSphere univ = ENNReal.ofReal (4 * π) := by
  rw [← polar_sphere_measure_real, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Integrability in polar coordinates, with the Jacobian in the radial measure. -/
theorem polar_integrable_iff (f : E3 → ℝ) :
    Integrable f ↔
      Integrable (fun z : sphere (0 : E3) 1 × Ioi (0 : ℝ) => f (z.2.1 • z.1.1))
        ((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have h := (MeasurePreserving.symm (homeomorphUnitSphereProd E3).toMeasurableEquiv
    (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
      (homeomorphUnitSphereProd E3).symm.measurableEmbedding (g := fun y => f y.1)
  rw [← restrict_compl_singleton (μ := (volume : Measure E3)) 0,
    ← IntegrableOn, integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
  simpa [Function.comp_def, E3] using h.symm

/-- Polar change of variables before applying Fubini. This equality also holds
for nonintegrable functions, with the usual Bochner-integral convention. -/
theorem polar_integral_prod (f : E3 → ℝ) :
    ∫ y, f y =
      ∫ z : sphere (0 : E3) 1 × Ioi (0 : ℝ), f (z.2.1 • z.1.1)
        ∂((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have h := (MeasurePreserving.symm (homeomorphUnitSphereProd E3).toMeasurableEquiv
    (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd).integral_comp
      (homeomorphUnitSphereProd E3).symm.measurableEmbedding (fun y => f y.1)
  rw [integral_subtype_comap (measurableSet_singleton _).compl,
    restrict_compl_singleton] at h
  simpa [E3] using h.symm

/-- Moving the polar Jacobian from the measure to the integrand. -/
theorem polar_integral_radial_measure (f : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2 =
      ∫ r in Ioi (0 : ℝ), r ^ 2 * f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const 2).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r ^ 2) • f r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg r), smul_eq_mul]

/-- The real-valued polar-coordinate integral formula in dimension three. -/
theorem polar_integral {f : E3 → ℝ} (hf : Integrable f) :
    ∫ y, f y = ∫ θ : sphere (0 : E3) 1,
      (∫ r in Ioi (0 : ℝ), r ^ 2 * f (r • (θ : E3)))
        ∂(volume : Measure E3).toSphere := by
  rw [polar_integral_prod, integral_prod _ ((polar_integrable_iff f).mp hf)]
  exact integral_congr_ae (.of_forall fun θ =>
    polar_integral_radial_measure (fun r => f (r • (θ : E3))))

/-- Integration outside a positive angular radial graph. The boundary function
is required to be constant along positive rays; the value at the origin is irrelevant. -/
theorem polar_integral_exterior {G b : E3 → ℝ} (hbm : Measurable b)
    (hbh : ∀ (r : ℝ), 0 < r → ∀ θ : sphere (0 : E3) 1, b (r • (θ : E3)) = b θ)
    (hb0 : ∀ θ : sphere (0 : E3) 1, 0 < b θ)
    (hG : IntegrableOn G {y : E3 | b y ≤ ‖y‖}) :
    ∫ y in {y : E3 | b y ≤ ‖y‖}, G y =
      ∫ θ : sphere (0 : E3) 1,
        (∫ r in Ici (b θ), r ^ 2 * G (r • (θ : E3)))
          ∂(volume : Measure E3).toSphere := by
  classical
  have hs : MeasurableSet {y : E3 | b y ≤ ‖y‖} := measurableSet_le hbm measurable_norm
  rw [← integral_indicator hs, polar_integral (hG.integrable_indicator hs)]
  apply integral_congr_ae
  filter_upwards with θ
  have hi : (∫ r in Ioi (0 : ℝ),
      r ^ 2 * {y : E3 | b y ≤ ‖y‖}.indicator G (r • (θ : E3))) =
      ∫ r in Ioi (0 : ℝ), (Ici (b θ)).indicator
        (fun r => r ^ 2 * G (r • (θ : E3))) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    have hn : ‖r • (θ : E3)‖ = r := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, norm_eq_of_mem_sphere θ]
    by_cases h : b θ ≤ r
    · simp [indicator_of_mem, h, hbh r hr θ, hn]
    · simp [indicator_of_notMem, h, hbh r hr θ, hn]
  rw [hi, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hsub : Ici (b θ) ⊆ Ioi (0 : ℝ) := fun r hr => (hb0 θ).trans_le hr
  rw [inter_eq_left.mpr hsub]

/-- Polar change of variables for a nonnegative, possibly nonintegrable function. -/
theorem polar_lintegral {f : E3 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ θ : sphere (0 : E3) 1,
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * f (r • (θ : E3)))
        ∂(volume : Measure E3).toSphere := by
  have h := (MeasurePreserving.symm (homeomorphUnitSphereProd E3).toMeasurableEquiv
    (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd).lintegral_comp
      (hf.comp measurable_subtype_coe)
  simp only [Function.comp_def] at h
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
    restrict_compl_singleton] at h
  have hprod : ∫⁻ y, f y =
      ∫⁻ z : sphere (0 : E3) 1 × Ioi (0 : ℝ), f (z.2.1 • z.1.1)
        ∂((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa [Function.comp_def, E3] using h.symm
  rw [hprod, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro θ
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
  · exact lintegral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r ^ 2) * f (r • (θ : E3)))
  · fun_prop
  · fun_prop

/-- Every inverse power of order at least two is integrable away from zero. -/
theorem polar_integrable_inv_pow {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    IntegrableOn (fun r : ℝ => 1 / r ^ (n + 2)) (Ioi ρ) := by
  have h := integrableOn_Ioi_rpow_of_lt
    (show -((n + 2 : ℕ) : ℝ) < -1 by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]) hρ
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div] using h

/-- Exact tail integral of an inverse power, in a form using natural powers only. -/
theorem polar_integral_inv_pow {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∫ r : ℝ in Ioi ρ, 1 / r ^ (n + 2) =
      1 / ((n + 1 : ℝ) * ρ ^ (n + 1)) := by
  have h := integral_Ioi_rpow_of_lt
    (show -((n + 2 : ℕ) : ℝ) < -1 by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]) hρ
  have he : -((n + 2 : ℕ) : ℝ) + 1 = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he] at h
  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, neg_div_neg_eq] at h
  simp only [one_div]
  rw [h]
  push_cast
  simp [div_eq_mul_inv, mul_comm]

/-- The two explicit terms in the radial far-field expansion. -/
theorem polar_integral_model {ρ : ℝ} (hρ : 0 < ρ) (C p : ℝ) :
    ∫ r : ℝ in Ioi ρ, (2 * C / r ^ 2 + p / r ^ 4) =
      2 * C / ρ + p / (3 * ρ ^ 3) := by
  have h2 := (polar_integrable_inv_pow hρ 0).const_mul (2 * C)
  have h4 := (polar_integrable_inv_pow hρ 2).const_mul p
  simp only [Nat.reduceAdd, mul_one_div] at h2 h4
  rw [integral_add h2 h4]
  simp only [div_eq_mul_inv]
  rw [integral_const_mul, integral_const_mul]
  have h2' := polar_integral_inv_pow hρ 0
  have h4' := polar_integral_inv_pow hρ 2
  norm_num at h2' h4'
  simp only [one_div] at h2' h4'
  rw [h2', h4']
  field_simp

/-- An integrable radial remainder gives a quantitative tail estimate.
No sign assumption on the function or on the coefficients is needed. -/
theorem polar_radial_tail_estimate {g : ℝ → ℝ} (hgm : Measurable g)
    {C p M ρ : ℝ} (hρ : 0 < ρ)
    (hg : ∀ r : ℝ, ρ ≤ r → |g r - 2 * C / r ^ 2 - p / r ^ 4| ≤ M / r ^ 5) :
    IntegrableOn g (Ioi ρ) ∧
      |(∫ r in Ioi ρ, g r) - 2 * C / ρ - p / (3 * ρ ^ 3)| ≤ M / (4 * ρ ^ 4) := by
  have h2 := (polar_integrable_inv_pow hρ 0).const_mul (2 * C)
  have h4 := (polar_integrable_inv_pow hρ 2).const_mul p
  have h5 := (polar_integrable_inv_pow hρ 3).const_mul M
  simp only [Nat.reduceAdd, mul_one_div] at h2 h4 h5
  have hmodel : IntegrableOn (fun r : ℝ => 2 * C / r ^ 2 + p / r ^ 4) (Ioi ρ) := h2.add h4
  have he : IntegrableOn (fun r => g r - (2 * C / r ^ 2 + p / r ^ 4)) (Ioi ρ) := by
    refine h5.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using hg r hr.le
  have hi : IntegrableOn g (Ioi ρ) := by
    have hi' : IntegrableOn
        (fun r => (g r - (2 * C / r ^ 2 + p / r ^ 4)) + (2 * C / r ^ 2 + p / r ^ 4))
        (Ioi ρ) := he.add hmodel
    simpa only [sub_add_cancel] using hi'
  refine ⟨hi, ?_⟩
  have hb : ‖∫ r in Ioi ρ, g r - (2 * C / r ^ 2 + p / r ^ 4)‖ ≤
      ∫ r in Ioi ρ, M / r ^ 5 := by
    apply norm_integral_le_of_norm_le h5
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using hg r hr.le
  rw [integral_sub hi hmodel, polar_integral_model hρ] at hb
  have h5' : ∫ r : ℝ in Ioi ρ, M / r ^ 5 = M / (4 * ρ ^ 4) := by
    simp only [div_eq_mul_inv]
    rw [integral_const_mul]
    have h := polar_integral_inv_pow hρ 3
    norm_num at h
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using congrArg (M * ·) h
  simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub, h5'] using hb

/-- Homogeneity turns the ambient far-field estimate into the weighted
one-dimensional estimate, uniformly over all directions on the unit sphere. -/
theorem polar_far_field_on_ray {G P : E3 → ℝ}
    (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    {C R M : ℝ}
    (hG : ∀ y : E3, R ≤ ‖y‖ →
      |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7)
    (θ : sphere (0 : E3) 1) {r : ℝ} (hr : 0 < r) (hRr : R ≤ r) :
    |r ^ 2 * G (r • (θ : E3)) - 2 * C / r ^ 2 - P θ / r ^ 4| ≤ M / r ^ 5 := by
  have hn : ‖r • (θ : E3)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp only [norm_eq_of_mem_sphere θ, mul_one]
  have h := hG (r • (θ : E3)) (by rwa [hn])
  rw [hn, hPh] at h
  have he : r ^ 2 * (G (r • (θ : E3)) - 2 * C / r ^ 4 -
      (r ^ 2 * P θ) / r ^ 8) =
      r ^ 2 * G (r • (θ : E3)) - 2 * C / r ^ 2 - P θ / r ^ 4 := by
    field_simp
  rw [← he, abs_mul, abs_of_nonneg (sq_nonneg r)]
  calc
    r ^ 2 * |G (r • (θ : E3)) - 2 * C / r ^ 4 - r ^ 2 * P θ / r ^ 8|
        ≤ r ^ 2 * (M / r ^ 7) := mul_le_mul_of_nonneg_left h (sq_nonneg r)
    _ = M / r ^ 5 := by field_simp

/-- The radial far-field mass equals its two explicit terms up to a uniform
error `M / (4 * ρ ^ 4)`, for every direction and every `ρ ≥ R`, `ρ > 0`. -/
theorem polar_far_field_tail {G P : E3 → ℝ} (hGm : Measurable G)
    (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    {C R M : ℝ}
    (hG : ∀ y : E3, R ≤ ‖y‖ →
      |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7)
    (θ : sphere (0 : E3) 1) {ρ : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * G (r • (θ : E3))) (Ioi ρ) ∧
      |(∫ r in Ioi ρ, r ^ 2 * G (r • (θ : E3))) - 2 * C / ρ -
        P θ / (3 * ρ ^ 3)| ≤ M / (4 * ρ ^ 4) := by
  apply polar_radial_tail_estimate (by fun_prop) hρ
  intro r hr
  exact polar_far_field_on_ray hPh hG θ (hρ.trans_le hr) (hRρ.trans hr)

/-- Closed-ray version of `polar_far_field_tail`, matching radial graph sets
defined using `ρ ≤ r`. -/
theorem polar_far_field_tail_Ici {G P : E3 → ℝ} (hGm : Measurable G)
    (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    {C R M : ℝ}
    (hG : ∀ y : E3, R ≤ ‖y‖ →
      |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7)
    (θ : sphere (0 : E3) 1) {ρ : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * G (r • (θ : E3))) (Ici ρ) ∧
      |(∫ r in Ici ρ, r ^ 2 * G (r • (θ : E3))) - 2 * C / ρ -
        P θ / (3 * ρ ^ 3)| ≤ M / (4 * ρ ^ 4) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi, integral_Ici_eq_integral_Ioi]
  exact polar_far_field_tail hGm hPh hG θ hρ hRρ

/-- Continuous ambient functions are integrable on the unit sphere. -/
theorem polar_sphere_integrable {f : E3 → ℝ} (hf : Continuous f) :
    Integrable (fun θ : sphere (0 : E3) 1 => f θ) (volume : Measure E3).toSphere := by
  have h := (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact
    (μ := (volume : Measure E3).toSphere) (K := univ) isCompact_univ
  simpa only [integrableOn_univ, Function.comp_def] using h

/-- A continuous function on the sphere has a uniform nonnegative bound. -/
theorem polar_sphere_bounded {f : E3 → ℝ} (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : sphere (0 : E3) 1, |f θ| ≤ B := by
  obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : E3) 1).image hf).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun θ => ?_⟩
  exact (hB _ (mem_image_of_mem f θ.property)).trans (le_max_left _ _)

/-- Degree-two homogeneity identifies the angular coefficient at every
nonzero ambient point. The algebraic identity itself also holds at zero. -/
theorem polar_homogeneous_normalize {q : E3 → ℝ}
    (hqh : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y) (y : E3) :
    q (‖y‖⁻¹ • y) = q y / ‖y‖ ^ 2 := by
  rw [hqh, inv_pow, div_eq_mul_inv, mul_comm]

/-- The normalized degree-two coefficient is uniformly bounded off the origin. -/
theorem polar_homogeneous_bound {q : E3 → ℝ} (hqc : Continuous q)
    (hqh : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : E3, y ≠ 0 → |q y / ‖y‖ ^ 2| ≤ B := by
  obtain ⟨B, hB, hb⟩ := polar_sphere_bounded hqc
  refine ⟨B, hB, fun y hy => ?_⟩
  have hn : ‖y‖⁻¹ • y ∈ sphere (0 : E3) 1 := by
    simp [norm_smul, hy]
  simpa only [polar_homogeneous_normalize hqh] using hb ⟨_, hn⟩

/-- The angular averages cancel both cubic terms in the proposed expansion. -/
theorem polar_integral_cubic_model {q P : E3 → ℝ} (hqc : Continuous q) (hPc : Continuous P)
    (hqm : ∫ θ : sphere (0 : E3) 1, q θ ∂(volume : Measure E3).toSphere = 0)
    (hPm : ∫ θ : sphere (0 : E3) 1, P θ ∂(volume : Measure E3).toSphere = 0)
    (C t : ℝ) :
    ∫ θ : sphere (0 : E3) 1,
        (2 * t - 2 * q θ * t ^ 3 / C ^ 3 + P θ * t ^ 3 / (3 * C ^ 3))
          ∂(volume : Measure E3).toSphere = 8 * π * t := by
  have hq := (((polar_sphere_integrable hqc).const_mul 2).mul_const (t ^ 3)).div_const (C ^ 3)
  have hP := ((polar_sphere_integrable hPc).mul_const (t ^ 3)).div_const (3 * C ^ 3)
  have hconst : Integrable (fun _ : sphere (0 : E3) 1 => 2 * t)
      (volume : Measure E3).toSphere := integrable_const _
  have hsub : Integrable (fun θ : sphere (0 : E3) 1 => 2 * t - 2 * q θ * t ^ 3 / C ^ 3)
      (volume : Measure E3).toSphere := hconst.sub hq
  rw [integral_add hsub hP, integral_sub hconst hq]
  simp only [integral_div, integral_mul_const, integral_const_mul, hqm, hPm,
    mul_zero, zero_mul, zero_div, sub_zero, add_zero, integral_const, smul_eq_mul,
    polar_sphere_measure_real]
  ring

end LiquidDrop.CapacitaryK
