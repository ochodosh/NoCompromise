import NoCompromise.CapacitaryK.PolarMass

/-!
# The volume route to the far-field mass expansion

The sphere measure throughout is `(volume : Measure E3).toSphere`.
-/

noncomputable section
open Real Set Filter MeasureTheory Metric Asymptotics
open scoped ENNReal Topology

namespace LiquidDrop.CapacitaryK

/-- In dimension three, inverse powers of order at least four are integrable
on every exterior region with positive inner radius. -/
theorem polar_integrable_norm_inv_pow {R : ℝ} (hR : 0 < R) (n : ℕ) :
    IntegrableOn (fun y : E3 => 1 / ‖y‖ ^ (n + 4)) {y : E3 | R ≤ ‖y‖} := by
  have hs : MeasurableSet {y : E3 | R ≤ ‖y‖} := measurableSet_le measurable_const measurable_norm
  rw [← integrable_indicator_iff hs]
  have hi : Integrable ((Ici R).indicator (fun r : ℝ => 1 / r ^ (n + 2))) := by
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact polar_integrable_inv_pow hR n
  have hj : Integrable (fun y : E3 =>
      (Ici R).indicator (fun r : ℝ => 1 / r ^ (n + 4)) ‖y‖) := by
    rw [integrable_fun_norm_addHaar]
    refine hi.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    by_cases h : R ≤ r
    · simp only [mem_Ici, h, indicator_of_mem, E3, finrank_euclideanSpace,
        Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
      field_simp
      ring
    · simp [h, indicator_of_notMem]
  exact hj.congr (.of_forall fun y => by
    by_cases h : R ≤ ‖y‖ <;> simp [h])

/-- The assumed far-field expansion implies absolute integrability on the
fixed exterior region. It does not require a sign assumption on `G`. -/
theorem polar_far_field_integrable {G P : E3 → ℝ} (hGm : Measurable G)
    (hPc : Continuous P)
    (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    {C R M : ℝ} (hR : 0 < R)
    (hG : ∀ y : E3, R ≤ ‖y‖ →
      |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7) :
    IntegrableOn G {y : E3 | R ≤ ‖y‖} := by
  obtain ⟨B, hB, hb⟩ := polar_homogeneous_bound hPc hPh
  have h4 := (polar_integrable_norm_inv_pow hR 0).const_mul (2 * |C|)
  have h6 := (polar_integrable_norm_inv_pow hR 2).const_mul B
  have h7 := (polar_integrable_norm_inv_pow hR 3).const_mul |M|
  simp only [Nat.reduceAdd, mul_one_div] at h4 h6 h7
  refine ((h4.add h6).add h7).mono' hGm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with y hy
  have hn : 0 < ‖y‖ := hR.trans_le hy
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp hn.ne'
  have hp : |P y / ‖y‖ ^ 8| ≤ B / ‖y‖ ^ 6 := by
    have he : P y / ‖y‖ ^ 8 = (P y / ‖y‖ ^ 2) / ‖y‖ ^ 6 := by ring
    rw [he, abs_div, abs_of_nonneg (by positivity : 0 ≤ ‖y‖ ^ 6)]
    exact div_le_div_of_nonneg_right (hb y hy0) (by positivity)
  have hm : |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ |M| / ‖y‖ ^ 7 :=
    (hG y hy).trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
  have hc : |2 * C / ‖y‖ ^ 4| = 2 * |C| / ‖y‖ ^ 4 := by
    simp [abs_div, abs_mul, abs_of_nonneg (norm_nonneg y)]
  rw [Real.norm_eq_abs]
  calc
    |G y| = |(G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8) +
        2 * C / ‖y‖ ^ 4 + P y / ‖y‖ ^ 8| := by ring_nf
    _ ≤ |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| +
        |2 * C / ‖y‖ ^ 4| + |P y / ‖y‖ ^ 8| :=
      le_trans (abs_add_le _ _) (by gcongr; exact abs_add_le _ _)
    _ ≤ 2 * |C| / ‖y‖ ^ 4 + B / ‖y‖ ^ 6 + |M| / ‖y‖ ^ 7 := by
      rw [hc]
      linarith

/-- A quantitative first-order reciprocal expansion on a fixed neighborhood
of zero. -/
theorem polar_reciprocal_remainder {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |1 / (1 + x) - (1 - x)| ≤ 2 * x ^ 2 := by
  have hx' := (abs_le.mp hx).1
  have hpos : 0 < 1 + x := by linarith
  have hinv : 1 / (1 + x) ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith)
  have he : 1 / (1 + x) - (1 - x) = x ^ 2 / (1 + x) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_nonneg (sq_nonneg x), abs_of_pos hpos, div_eq_mul_inv]
  have h := mul_le_mul_of_nonneg_left hinv (sq_nonneg x)
  simpa only [one_div, mul_comm] using h

/-- A uniform Lipschitz bound for the cubic reciprocal. -/
theorem polar_cubic_reciprocal_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |1 / (1 + x) ^ 3 - 1| ≤ 14 * |x| := by
  have hx' := (abs_le.mp hx).1
  have hpos : 0 < 1 + x := by linarith
  have hz0 : 0 ≤ 1 / (1 + x) := by positivity
  have hz2 : 1 / (1 + x) ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith)
  have hfirst : |1 / (1 + x) - 1| ≤ 2 * |x| := by
    have he : 1 / (1 + x) - 1 = -x / (1 + x) := by field_simp; ring
    rw [he, abs_div, abs_neg, abs_of_pos hpos, div_eq_mul_inv]
    simpa only [one_div, mul_comm] using mul_le_mul_of_nonneg_left hz2 (abs_nonneg x)
  have hpoly : (1 / (1 + x)) ^ 2 + 1 / (1 + x) + 1 ≤ 7 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz2)]
  have he : 1 / (1 + x) ^ 3 - 1 =
      (1 / (1 + x) - 1) * ((1 / (1 + x)) ^ 2 + 1 / (1 + x) + 1) := by
    field_simp
    ring
  rw [he, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (1 / (1 + x)) ^ 2 + 1 / (1 + x) + 1)]
  calc
    _ ≤ (2 * |x|) * 7 := mul_le_mul hfirst hpoly (by positivity) (by positivity)
    _ = 14 * |x| := by ring

/-- The normalized radial model has a uniform fourth-order remainder.
Here `k`, `p`, and `a` are the coefficients after dividing by the appropriate
powers of `C`. -/
theorem polar_normalized_model_estimate {t k p a D B : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hD : 0 ≤ D) (hp : |p| ≤ B)
    (hx : |t ^ 2 * k + a * t ^ 3| ≤ D * t ^ 2)
    (hsmall : D * t ^ 2 ≤ 1 / 2) :
    |2 * t / (1 + (t ^ 2 * k + a * t ^ 3)) +
        p * t ^ 3 / (1 + (t ^ 2 * k + a * t ^ 3)) ^ 3 -
        (2 * t - 2 * k * t ^ 3 + p * t ^ 3)| ≤
      (2 * |a| + 4 * D ^ 2 + 14 * B * D) * t ^ 4 := by
  have hB : 0 ≤ B := (abs_nonneg p).trans hp
  let x := t ^ 2 * k + a * t ^ 3
  have hxsmall : |x| ≤ 1 / 2 := hx.trans hsmall
  have hx2 : x ^ 2 ≤ D ^ 2 * t ^ 4 := by
    calc
      x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (D * t ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
      _ = D ^ 2 * t ^ 4 := by ring
  have ht5 : t ^ 5 ≤ t ^ 4 := by
    have h := mul_le_mul_of_nonneg_right ht1 (pow_nonneg ht.le 4)
    nlinarith
  have hfirst : |2 * t / (1 + x) - (2 * t - 2 * k * t ^ 3)| ≤
      (2 * |a| + 4 * D ^ 2) * t ^ 4 := by
    have he : 2 * t / (1 + x) - (2 * t - 2 * k * t ^ 3) =
        2 * t * (1 / (1 + x) - (1 - x)) - 2 * a * t ^ 4 := by
      dsimp [x]
      ring
    rw [he]
    calc
      _ ≤ |2 * t * (1 / (1 + x) - (1 - x))| + |2 * a * t ^ 4| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
          (2 * t * (1 / (1 + x) - (1 - x))) (-(2 * a * t ^ 4))
      _ = 2 * t * |1 / (1 + x) - (1 - x)| + 2 * |a| * t ^ 4 := by
        simp [abs_mul, abs_of_pos ht]
      _ ≤ 2 * t * (2 * x ^ 2) + 2 * |a| * t ^ 4 := by
        gcongr
        exact polar_reciprocal_remainder hxsmall
      _ ≤ 2 * t * (2 * (D ^ 2 * t ^ 4)) + 2 * |a| * t ^ 4 := by gcongr
      _ = 4 * D ^ 2 * t ^ 5 + 2 * |a| * t ^ 4 := by ring
      _ ≤ 4 * D ^ 2 * t ^ 4 + 2 * |a| * t ^ 4 := by gcongr
      _ = (2 * |a| + 4 * D ^ 2) * t ^ 4 := by ring
  have hsecond : |p * t ^ 3 / (1 + x) ^ 3 - p * t ^ 3| ≤
      14 * B * D * t ^ 4 := by
    have he : p * t ^ 3 / (1 + x) ^ 3 - p * t ^ 3 =
        p * t ^ 3 * (1 / (1 + x) ^ 3 - 1) := by ring
    rw [he, abs_mul, abs_mul, abs_pow, abs_of_pos ht]
    calc
      _ ≤ (B * t ^ 3) * (14 * |x|) := by
        gcongr
        exact polar_cubic_reciprocal_bound hxsmall
      _ ≤ (B * t ^ 3) * (14 * (D * t ^ 2)) := by gcongr
      _ = 14 * B * D * t ^ 5 := by ring
      _ ≤ 14 * B * D * t ^ 4 := by gcongr
  calc
    _ = |(2 * t / (1 + x) - (2 * t - 2 * k * t ^ 3)) +
        (p * t ^ 3 / (1 + x) ^ 3 - p * t ^ 3)| := by congr 1; dsimp [x]; ring
    _ ≤ |2 * t / (1 + x) - (2 * t - 2 * k * t ^ 3)| +
        |p * t ^ 3 / (1 + x) ^ 3 - p * t ^ 3| := abs_add_le _ _
    _ ≤ (2 * |a| + 4 * D ^ 2 + 14 * B * D) * t ^ 4 := by linarith

/-- The ambient radius used to define a moving exterior graph. -/
def polar_graph_radius (C : ℝ) (q : E3 → ℝ) (A t : ℝ) (y : E3) : ℝ :=
  C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) + A * t ^ 2

/-- Measurability of the ambient graph radius, including its value at zero. -/
theorem polar_graph_radius_measurable {q : E3 → ℝ} (hqc : Continuous q) (C A t : ℝ) :
    Measurable (polar_graph_radius C q A t) := by
  unfold polar_graph_radius
  fun_prop

/-- The graph radius is constant along every positive ray. -/
theorem polar_graph_radius_on_ray {q : E3 → ℝ}
    (hqh : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y)
    (C A t : ℝ) {r : ℝ} (hr : 0 < r) (θ : sphere (0 : E3) 1) :
    polar_graph_radius C q A t (r • (θ : E3)) = polar_graph_radius C q A t θ := by
  simp only [polar_graph_radius, hqh, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, norm_eq_of_mem_sphere θ, mul_one, one_pow]
  congr 2
  field_simp

/-- Evaluation of the graph radius on the unit sphere. -/
theorem polar_graph_radius_on_sphere (q : E3 → ℝ) (C A t : ℝ)
    (θ : sphere (0 : E3) 1) :
    polar_graph_radius C q A t θ = C / t + t * q θ / C ^ 2 + A * t ^ 2 := by
  simp [polar_graph_radius, norm_eq_of_mem_sphere θ]

/-- Measurability of the radial tail as a function of direction, for a
measurable moving lower endpoint. -/
theorem polar_tail_measurable {G : E3 → ℝ} (hGm : Measurable G)
    {ρ : sphere (0 : E3) 1 → ℝ} (hρm : Measurable ρ) :
    Measurable (fun θ : sphere (0 : E3) 1 =>
      ∫ r in Ici (ρ θ), r ^ 2 * G (r • (θ : E3))) := by
  have hm : Measurable (fun z : sphere (0 : E3) 1 × ℝ =>
      ({z : sphere (0 : E3) 1 × ℝ | ρ z.1 ≤ z.2}.indicator
        (fun z => z.2 ^ 2 * G (z.2 • (z.1 : E3)))) z) := by
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_le (hρm.comp measurable_fst) measurable_snd
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  convert hi using 1
  ext θ
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with r
  by_cases h : ρ θ ≤ r <;> simp [h]

/-- Uniform scalar estimates for the moving radius, with coefficients ranging
in fixed bounded intervals. -/
theorem polar_radius_uniform_estimates {C Q B R A : ℝ}
    (hC : 0 < C) (hQ : 0 ≤ Q) (_hB : 0 ≤ B) (hR : 0 < R) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
      ∀ k p : ℝ, |k| ≤ Q → |p| ≤ B →
        let ρ := C / t + t * k / C ^ 2 + A * t ^ 2
        R ≤ ρ ∧ 0 < ρ ∧
        |2 * C / ρ + p / (3 * ρ ^ 3) -
          (2 * t - 2 * k * t ^ 3 / C ^ 3 + p * t ^ 3 / (3 * C ^ 3))| ≤ K * t ^ 4 ∧
        1 / ρ ^ 4 ≤ 16 * t ^ 4 / C ^ 4 := by
  let D := Q / C ^ 3 + |A| / C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2 * |A / C| + 4 * D ^ 2 + 14 * (B / (3 * C ^ 3)) * D, ?_⟩
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => D * t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hid.pow 2)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), D * t ^ 2 < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < min 1 (C / (2 * R))), hsmall]
    with t ht hsmall
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := (ht.2.trans_le (min_le_left _ _)).le
  have hRt : R ≤ C / (2 * t) := by
    have htR : t < C / (2 * R) := ht.2.trans_le (min_le_right _ _)
    apply (le_div_iff₀ (by positivity)).mpr
    have := (lt_div_iff₀ (by positivity : 0 < 2 * R)).mp htR
    nlinarith
  refine ⟨ht0, fun k p hk hp => ?_⟩
  let x := t ^ 2 * (k / C ^ 3) + (A / C) * t ^ 3
  have hk' : |k / C ^ 3| ≤ Q / C ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < C ^ 3)]
    exact div_le_div_of_nonneg_right hk (by positivity)
  have hp' : |p / (3 * C ^ 3)| ≤ B / (3 * C ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 3 * C ^ 3)]
    exact div_le_div_of_nonneg_right hp (by positivity)
  have ht3 : t ^ 3 ≤ t ^ 2 := by
    have := mul_le_mul_of_nonneg_right ht1 (sq_nonneg t)
    nlinarith
  have hx : |x| ≤ D * t ^ 2 := by
    calc
      |x| ≤ |t ^ 2 * (k / C ^ 3)| + |(A / C) * t ^ 3| := abs_add_le _ _
      _ = t ^ 2 * |k / C ^ 3| + (|A| / C) * t ^ 3 := by
        simp [abs_mul, abs_div, abs_of_pos hC, abs_of_pos ht0]
      _ ≤ t ^ 2 * (Q / C ^ 3) + (|A| / C) * t ^ 2 := by gcongr
      _ = D * t ^ 2 := by dsimp [D]; ring
  have hxsmall : |x| ≤ 1 / 2 := hx.trans hsmall.le
  have hxpos : 0 < 1 + x := by have := (abs_le.mp hxsmall).1; linarith
  let ρ := C / t + t * k / C ^ 2 + A * t ^ 2
  have he : ρ = C / t * (1 + x) := by
    dsimp [ρ, x]
    field_simp
    ring
  have hρ : 0 < ρ := by rw [he]; positivity
  have hρlow : C / (2 * t) ≤ ρ := by
    rw [he]
    calc
      C / (2 * t) = C / t * (1 / 2) := by ring
      _ ≤ C / t * (1 + x) := by
        gcongr
        have := (abs_le.mp hxsmall).1
        linarith
  refine ⟨hRt.trans hρlow, hρ, ?_, ?_⟩
  · have hmodel := polar_normalized_model_estimate ht0 ht1 hD hp' hx hsmall.le
    have heq : 2 * C / ρ + p / (3 * ρ ^ 3) -
        (2 * t - 2 * k * t ^ 3 / C ^ 3 + p * t ^ 3 / (3 * C ^ 3)) =
        2 * t / (1 + x) + (p / (3 * C ^ 3)) * t ^ 3 / (1 + x) ^ 3 -
        (2 * t - 2 * (k / C ^ 3) * t ^ 3 + (p / (3 * C ^ 3)) * t ^ 3) := by
      rw [he]
      field_simp
    rw [heq]
    exact hmodel
  · have hinv : 1 / ρ ≤ 2 * t / C := by
      apply (div_le_iff₀ hρ).mpr
      have := (div_le_iff₀ (by positivity : 0 < 2 * t)).mp hρlow
      calc
        1 ≤ (2 * t * ρ) / C := (le_div_iff₀ hC).mpr (by nlinarith)
        _ = 2 * t / C * ρ := by ring
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / ρ) hinv 4
    norm_num [div_pow, mul_pow] at hpow ⊢
    exact hpow

/-- Integrating a uniform error around the cubic angular model cancels the
two mean-zero coefficients and multiplies the error by the sphere area. -/
theorem polar_sphere_model_error {f : sphere (0 : E3) 1 → ℝ}
    (hfm : Measurable f) {q P : E3 → ℝ} (hqc : Continuous q) (hPc : Continuous P)
    (hqm : ∫ θ : sphere (0 : E3) 1, q θ ∂(volume : Measure E3).toSphere = 0)
    (hPm : ∫ θ : sphere (0 : E3) 1, P θ ∂(volume : Measure E3).toSphere = 0)
    (C t K : ℝ)
    (herror : ∀ θ : sphere (0 : E3) 1,
      |f θ - (2 * t - 2 * q θ * t ^ 3 / C ^ 3 + P θ * t ^ 3 / (3 * C ^ 3))| ≤ K) :
    |(∫ θ, f θ ∂(volume : Measure E3).toSphere) - 8 * π * t| ≤ 4 * π * K := by
  let model := fun θ : sphere (0 : E3) 1 =>
    2 * t - 2 * q θ * t ^ 3 / C ^ 3 + P θ * t ^ 3 / (3 * C ^ 3)
  have hm : Integrable model (volume : Measure E3).toSphere :=
    ((integrable_const (2 * t)).sub
      ((((polar_sphere_integrable hqc).const_mul 2).mul_const (t ^ 3)).div_const (C ^ 3))).add
      (((polar_sphere_integrable hPc).mul_const (t ^ 3)).div_const (3 * C ^ 3))
  have he : Integrable (fun θ => f θ - model θ) (volume : Measure E3).toSphere := by
    refine (integrable_const K).mono' ?_ ?_
    · dsimp [model]
      fun_prop
    · exact .of_forall fun θ => (herror θ : |f θ - model θ| ≤ K)
  have hf : Integrable f (volume : Measure E3).toSphere := by
    have hsum : Integrable (fun θ => (f θ - model θ) + model θ)
        (volume : Measure E3).toSphere := he.add hm
    simpa only [sub_add_cancel] using hsum
  have hb := norm_integral_le_of_norm_le_const
    (μ := (volume : Measure E3).toSphere) (f := fun θ => f θ - model θ)
    (.of_forall fun θ => (herror θ : |f θ - model θ| ≤ K))
  rw [integral_sub hf hm, polar_integral_cubic_model hqc hPc hqm hPm C t] at hb
  simpa only [Real.norm_eq_abs, polar_sphere_measure_real, mul_comm K] using hb

/-- Each moving graph has the required mass estimate. The same statement also
records that its whole boundary lies in the fixed exterior region. No sign
assumption on `G` is needed for this graph estimate. -/
theorem polar_graph_mass_estimate {G q P : E3 → ℝ}
    (hGm : Measurable G)
    (hqc : Continuous q) (hqh : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y)
    (hPc : Continuous P) (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    (hqm : ∫ θ : sphere (0 : E3) 1, q θ ∂(volume : Measure E3).toSphere = 0)
    (hPm : ∫ θ : sphere (0 : E3) 1, P θ ∂(volume : Measure E3).toSphere = 0)
    {C R M A : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hG : ∀ y : E3, R ≤ ‖y‖ →
      |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ y : E3, R ≤ polar_graph_radius C q A t y ∧ 0 < polar_graph_radius C q A t y) ∧
      IntegrableOn G {y : E3 | polar_graph_radius C q A t y ≤ ‖y‖} ∧
      |(∫ y in {y : E3 | polar_graph_radius C q A t y ≤ ‖y‖}, G y) - 8 * π * t| ≤
        K * t ^ 4 := by
  obtain ⟨Q, hQ, hq⟩ := polar_homogeneous_bound hqc hqh
  obtain ⟨B, hB, hp⟩ := polar_sphere_bounded hPc
  obtain ⟨K, hK⟩ := polar_radius_uniform_estimates (A := A) hC hQ hB hR
  have hGi := polar_far_field_integrable hGm hPc hPh hR hG
  refine ⟨4 * π * (K + 4 * |M| / C ^ 4), ?_⟩
  filter_upwards [hK] with t ht
  have hlower : ∀ y : E3,
      R ≤ polar_graph_radius C q A t y ∧ 0 < polar_graph_radius C q A t y := by
    intro y
    have hqy : |q y / ‖y‖ ^ 2| ≤ Q := by
      by_cases hy : y = 0
      · simp [hy, hQ]
      · exact hq y hy
    have h := ht.2 (q y / ‖y‖ ^ 2) 0 hqy (by simpa using hB)
    have he : polar_graph_radius C q A t y =
        C / t + t * (q y / ‖y‖ ^ 2) / C ^ 2 + A * t ^ 2 := by
      unfold polar_graph_radius
      ring
    rw [he]
    exact ⟨h.1, h.2.1⟩
  have hi : IntegrableOn G {y : E3 | polar_graph_radius C q A t y ≤ ‖y‖} :=
    hGi.mono_set fun y hy => (hlower y).1.trans hy
  refine ⟨hlower, hi, ?_⟩
  rw [polar_integral_exterior (polar_graph_radius_measurable hqc C A t)
    (fun r hr θ => polar_graph_radius_on_ray hqh C A t hr θ)
    (fun θ => (hlower θ).2) hi]
  have herr := polar_sphere_model_error
    (polar_tail_measurable hGm
      ((polar_graph_radius_measurable hqc C A t).comp measurable_subtype_coe))
    hqc hPc hqm hPm C t ((K + 4 * |M| / C ^ 4) * t ^ 4) ?_
  · calc
      _ ≤ 4 * π * ((K + 4 * |M| / C ^ 4) * t ^ 4) := herr
      _ = (4 * π * (K + 4 * |M| / C ^ 4)) * t ^ 4 := by ring
  intro θ
  have hqθ : |q θ| ≤ Q := by
    have hθ : (θ : E3) ≠ 0 := by
      intro hzero
      have hn := norm_eq_of_mem_sphere θ
      rw [hzero, norm_zero] at hn
      norm_num at hn
    simpa only [norm_eq_of_mem_sphere θ, one_pow, div_one] using hq θ hθ
  have hs := ht.2 (q θ) (P θ) hqθ (hp θ)
  let ρ := C / t + t * q θ / C ^ 2 + A * t ^ 2
  have hρ : 0 < ρ := hs.2.1
  have htail := (polar_far_field_tail_Ici hGm hPh hG θ hρ hs.1).2
  have htail' : |(∫ r in Ici ρ, r ^ 2 * G (r • (θ : E3))) -
      2 * C / ρ - P θ / (3 * ρ ^ 3)| ≤ (4 * |M| / C ^ 4) * t ^ 4 := by
    refine htail.trans ?_
    calc
      M / (4 * ρ ^ 4) ≤ |M| / (4 * ρ ^ 4) :=
        div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
      _ = (|M| / 4) * (1 / ρ ^ 4) := by
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ac_rfl
      _ ≤ (|M| / 4) * (16 * t ^ 4 / C ^ 4) :=
        mul_le_mul_of_nonneg_left hs.2.2.2 (by positivity)
      _ = (4 * |M| / C ^ 4) * t ^ 4 := by ring
  simp only [Function.comp_apply, polar_graph_radius_on_sphere]
  have hmodel := hs.2.2.1
  calc
    _ = |((∫ r in Ici ρ, r ^ 2 * G (r • (θ : E3))) - 2 * C / ρ - P θ / (3 * ρ ^ 3)) +
        (2 * C / ρ + P θ / (3 * ρ ^ 3) -
          (2 * t - 2 * q θ * t ^ 3 / C ^ 3 + P θ * t ^ 3 / (3 * C ^ 3)))| := by
      congr 1
      dsimp [ρ]
      ring
    _ ≤ |(∫ r in Ici ρ, r ^ 2 * G (r • (θ : E3))) - 2 * C / ρ - P θ / (3 * ρ ^ 3)| +
        |2 * C / ρ + P θ / (3 * ρ ^ 3) -
          (2 * t - 2 * q θ * t ^ 3 / C ^ 3 + P θ * t ^ 3 / (3 * C ^ 3))| := abs_add_le _ _
    _ ≤ (K + 4 * |M| / C ^ 4) * t ^ 4 := by linarith

/-- The far-field mass expansion for a measurable region squeezed between
two degree-two angular graphs. Nonnegativity of `G` is required only in the
fixed exterior region. -/
theorem polar_far_mass_expansion {G q P : E3 → ℝ}
    (hGm : Measurable G)
    (hqc : Continuous q) (hqh : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y)
    (hPc : Continuous P) (hPh : ∀ (c : ℝ) (y : E3), P (c • y) = c ^ 2 * P y)
    (hqm : ∫ θ, q (θ : E3) ∂(volume : Measure E3).toSphere = 0)
    (hPm : ∫ θ, P (θ : E3) ∂(volume : Measure E3).toSphere = 0)
    {C R M A : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hG0 : ∀ y : E3, R ≤ ‖y‖ → 0 ≤ G y)
    (hG : ∀ y : E3, R ≤ ‖y‖ → |G y - 2 * C / ‖y‖ ^ 4 - P y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7)
    (S : ℝ → Set E3) (hSm : ∀ t, MeasurableSet (S t))
    (hS : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ y : E3, y ≠ 0 → C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) + A * t ^ 2 ≤ ‖y‖ → y ∈ S t) ∧
      (∀ y ∈ S t, y ≠ 0 ∧ C / t + t * q y / (C ^ 2 * ‖y‖ ^ 2) - A * t ^ 2 ≤ ‖y‖)) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn G (S t)) ∧
    (fun t => (∫ y in S t, G y) - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  obtain ⟨Kplus, hplus⟩ := polar_graph_mass_estimate
    hGm hqc hqh hPc hPh hqm hPm (A := A) hC hR hG
  obtain ⟨Kminus, hminus⟩ := polar_graph_mass_estimate
    hGm hqc hqh hPc hPh hqm hPm (A := -A) hC hR hG
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn G (S t) ∧
      |(∫ y in S t, G y) - 8 * π * t| ≤ (|Kplus| + |Kminus|) * t ^ 4 := by
    filter_upwards [hplus, hminus, hS] with t hp hm hs
    let inner := {y : E3 | polar_graph_radius C q A t y ≤ ‖y‖}
    let outer := {y : E3 | polar_graph_radius C q (-A) t y ≤ ‖y‖}
    have hinner : inner ⊆ S t := by
      intro y hy
      have hy0 : y ≠ 0 := by
        intro he
        have hn : 0 < ‖y‖ := (hp.1 y).2.trans_le hy
        simp [he] at hn
      exact hs.1 y hy0 hy
    have houter : S t ⊆ outer := by
      intro y hy
      have h := (hs.2 y hy).2
      change polar_graph_radius C q (-A) t y ≤ ‖y‖
      simpa only [polar_graph_radius, neg_mul, sub_eq_add_neg] using h
    have hfar : ∀ y ∈ outer, R ≤ ‖y‖ := fun y hy => (hm.1 y).1.trans hy
    have hi : IntegrableOn G (S t) := hm.2.1.mono_set houter
    have hlo : (∫ y in inner, G y) ≤ ∫ y in S t, G y := by
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem (hSm t)] with y hy
        exact hG0 y (hfar y (houter hy))
      · exact .of_forall hinner
    have hhi : (∫ y in S t, G y) ≤ ∫ y in outer, G y := by
      apply setIntegral_mono_set hm.2.1
      · filter_upwards [ae_restrict_mem
          (measurableSet_le (polar_graph_radius_measurable hqc C (-A) t) measurable_norm)] with y hy
        exact hG0 y (hfar y hy)
      · exact .of_forall houter
    refine ⟨hi, abs_le.mpr ⟨?_, ?_⟩⟩
    · have hbound := (abs_le.mp hp.2.2).1
      have hK : Kplus * t ^ 4 ≤ (|Kplus| + |Kminus|) * t ^ 4 := by
        gcongr
        exact (le_abs_self Kplus).trans (le_add_of_nonneg_right (abs_nonneg Kminus))
      linarith
    · have hbound := (abs_le.mp hm.2.2).2
      have hK : Kminus * t ^ 4 ≤ (|Kplus| + |Kminus|) * t ^ 4 := by
        gcongr
        exact (le_abs_self Kminus).trans (le_add_of_nonneg_left (abs_nonneg Kplus))
      linarith
  refine ⟨hgood.mono fun t ht => ht.1, IsBigO.of_bound (|Kplus| + |Kminus|) ?_⟩
  filter_upwards [hgood] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)] using ht.2

end LiquidDrop.CapacitaryK
