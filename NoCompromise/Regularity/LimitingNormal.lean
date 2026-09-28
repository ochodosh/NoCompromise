import NoCompromise.Regularity.UniformCenters
import NoCompromise.Regularity.RepresentativeBoundary

/-!
# The limiting normal of the excess iteration at reduced-boundary points

Blueprint `thm:eps-regularity`, Step 3. The excess-decay iteration of
`normals_cauchy` selects, at a boundary centre `z`, a sequence of unit axes
`ν j` converging to a unit vector `νlim`. This file identifies `νlim` with the
measure-theoretic outward normal `reducedNormal E … z` whenever `z` is a
reduced-boundary point, by differentiating the perimeter measure at `z`.

The mechanism is the exact expansion
`‖ν_E y - ν‖ ^ 2 = 2 - 2 ⟪ν, ν_E y⟫` valid for unit vectors, which turns the
unnormalized excess on a ball into `2 μ(B) - 2 ⟪ν, ∫_B ν_E⟫`. Dividing by the
Ahlfors lower density `μ(B_s) ≥ (π/2) s ^ 2` of the perimeter measure at a
reduced point gives `1 - ⟪ν, ⨍_{B_s} ν_E⟫ ≤ Exc(E, z, s, ν) / π`. Along the
iteration scales the excess tends to zero and the averages tend to
`reducedNormal E … z`, so `⟪νlim, reducedNormal E … z⟫ ≥ 1`, forcing equality
of the two unit vectors.

As a consequence the angle bound of Step 3 is proved: under a small enough
absolute threshold every limiting normal, hence every measure-theoretic normal
at a reduced-boundary point of the eighth cylinder, makes an angle less than
`π / 4` with the initial axis.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The reduced normal is integrable on every bounded set for the
reduced-boundary area measure. -/
lemma integrableOn_reducedNormal (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {U : Set AmbientSpace}
    (hbU : Bornology.IsBounded U) :
    IntegrableOn (reducedNormal E hE hmE) U
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  have hp := reducedBoundary_outwardPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  have hfin : ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) U < ∞ :=
    hbU.measure_lt_top
  let : IsFiniteMeasure
      (((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_reducedNormal E hE hmE).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae hp.norm_ae] with y hy
  exact hy.le

/-- Exact expansion of the unnormalized excess against a unit axis. -/
lemma normalExcessIntegral_eq_two_sub (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {U : Set AmbientSpace} (hbU : Bornology.IsBounded U)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    normalExcessIntegral E hE hmE U ν =
      2 * ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real U -
        2 * inner ℝ ν (∫ y in U, reducedNormal E hE hmE y
          ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  have hp := reducedBoundary_outwardPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  have hfin : ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) U < ∞ :=
    hbU.measure_lt_top
  let : IsFiniteMeasure
      (((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hint := integrableOn_reducedNormal E hE hmE hbU
  have hcongr : ∫ y in U, ‖reducedNormal E hE hmE y - ν‖ ^ 2
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
      = ∫ y in U, (2 - 2 * inner ℝ ν (reducedNormal E hE hmE y))
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hp.norm_ae] with y hy
    rw [norm_sub_sq_real, hy, hν, real_inner_comm ν (reducedNormal E hE hmE y)]
    ring
  rw [normalExcessIntegral, hcongr,
    integral_sub (integrable_const _)
      ((Integrable.const_inner (𝕜 := ℝ) ν hint).const_mul 2),
    setIntegral_const, integral_const_mul, integral_inner hint ν]
  simp only [smul_eq_mul]
  ring

/-- The Ahlfors lower density of the reduced-boundary area measure at a
reduced-boundary point, in real form. -/
lemma exists_reducedBoundary_area_lower (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {z : AmbientSpace} (hz : z ∈ reducedBoundary E hE hmE) :
    ∃ R > 0, ∀ s : ℝ, 0 < s → s < R →
      Real.pi / 2 * s ^ 2 ≤
        ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real (ball z s) := by
  obtain ⟨R, hR, hb⟩ := exists_perimeter_density_bounds E hE hmE hz
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  refine ⟨R, hR, fun s hs hsR => ?_⟩
  have hfin : canonicalPerimeterMeasure E hE hmE (ball z s) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall z s).measure_lt_top).ne
  have h1 := (hb s hs hsR).1
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE, measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h1

/-- Differentiation of the perimeter measure at a reduced-boundary point: the
ball averages of the reduced normal converge to its value at the point. -/
lemma tendsto_average_reducedNormal (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {z : AmbientSpace} (hz : z ∈ reducedBoundary E hE hmE) :
    Tendsto (fun s : ℝ => ⨍ y in ball z s, reducedNormal E hE hmE y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE))
      (𝓝[>] (0 : ℝ)) (𝓝 (reducedNormal E hE hmE z)) := by
  have h := tendsto_average_reducedNormalOfPolar (canonicalPerimeterMeasure E hE hmE)
    (-canonicalOutwardPolarDensity E hE hmE) hz
  have hval : reducedNormalOfPolar (canonicalPerimeterMeasure E hE hmE)
      (-canonicalOutwardPolarDensity E hE hmE) z = reducedNormal E hE hmE z := rfl
  rw [hval] at h
  have hae : (-canonicalOutwardPolarDensity E hE hmE)
      =ᵐ[canonicalPerimeterMeasure E hE hmE] (-reducedNormal E hE hmE) := by
    filter_upwards [reducedNormal_ae_eq_polarDensity E hE hmE] with y hy
    simp only [Pi.neg_apply, hy]
  simp_rw [average_ball_congr_ae (canonicalPerimeterMeasure E hE hmE) hae] at h
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE] at h
  have hneg : ∀ t : ℝ, (⨍ y in ball z t, (-reducedNormal E hE hmE) y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE))
      = -⨍ y in ball z t, reducedNormal E hE hmE y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) := by
    intro t
    simp only [setAverage_eq, Pi.neg_apply, integral_neg, smul_neg]
  simp_rw [hneg] at h
  simpa only [neg_neg] using h.neg

/-- The quantitative form of Step 3: small cylindrical excess about a unit axis
forces the ball average of the reduced normal to be nearly parallel to that
axis, at every scale where the Ahlfors lower density is available. -/
lemma one_sub_excess_div_pi_le_inner_average (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {z ν : AmbientSpace} (hν : ‖ν‖ = 1) {s : ℝ} (hs : 0 < s)
    (hdens : Real.pi / 2 * s ^ 2 ≤
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real (ball z s)) :
    1 - cylindricalExcess E hE hmE z s ν / Real.pi ≤
      inner ℝ ν (⨍ y in ball z s, reducedNormal E hE hmE y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  have hπ := Real.pi_pos
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hmpos : 0 < ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real (ball z s) :=
    lt_of_lt_of_le (by positivity) hdens
  have hExc : 0 ≤ cylindricalExcess E hE hmE z s ν :=
    div_nonneg (normalExcessIntegral_nonneg E hE hmE _ _) (sq_nonneg s)
  have hcyl : s ^ 2 * cylindricalExcess E hE hmE z s ν
      = normalExcessIntegral E hE hmE (cylinder z s ν) ν := by
    rw [cylindricalExcess]
    field_simp
  have hball : normalExcessIntegral E hE hmE (ball z s) ν
      ≤ s ^ 2 * cylindricalExcess E hE hmE z s ν := by
    rw [hcyl]
    exact normalExcessIntegral_mono E hE hmE (isBounded_cylinder z s hν)
      (ball_subset_cylinder z s hν) ν
  have hexp := normalExcessIntegral_eq_two_sub E hE hmE
    (isBounded_ball (x := z) (r := s)) hν
  have hmain : 2 * ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real (ball z s) -
      2 * inner ℝ ν (∫ y in ball z s, reducedNormal E hE hmE y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE))
      ≤ s ^ 2 * cylindricalExcess E hE hmE z s ν := by
    rw [← hexp]; exact hball
  obtain ⟨u, hu⟩ : ∃ u : ℝ, cylindricalExcess E hE hmE z s ν = Real.pi * u :=
    ⟨cylindricalExcess E hE hmE z s ν / Real.pi, by field_simp⟩
  have hunn : 0 ≤ u := nonneg_of_mul_nonneg_right (by rwa [← hu]) hπ
  rw [hu] at hmain ⊢
  rw [mul_div_cancel_left₀ _ hπ.ne', setAverage_eq, real_inner_smul_right,
    inv_mul_eq_div, le_div_iff₀ hmpos]
  have hprod := mul_le_mul_of_nonneg_left hdens hunn
  linarith

/-- Blueprint `thm:eps-regularity`, Step 3, core differentiation statement.
If the selected unit axes converge and the cylindrical excess about them tends
to zero along a sequence of scales shrinking to zero, then at a reduced-boundary
point the limiting axis is the measure-theoretic outward normal. -/
theorem limiting_normal_eq_reducedNormal_of_tendsto_excess (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {z : AmbientSpace} (hz : z ∈ reducedBoundary E hE hmE)
    {s : ℕ → ℝ} (hspos : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0))
    {ν : ℕ → AmbientSpace} (hν : ∀ j, ‖ν j‖ = 1)
    {νlim : AmbientSpace} (hνlim : ‖νlim‖ = 1) (hlim : Tendsto ν atTop (𝓝 νlim))
    (hexc : Tendsto (fun j => cylindricalExcess E hE hmE z (s j) (ν j)) atTop (𝓝 0)) :
    νlim = reducedNormal E hE hmE z := by
  obtain ⟨R, hR, hdens⟩ := exists_reducedBoundary_area_lower E hE hmE hz
  have hsw : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hs0
      (Eventually.of_forall hspos)
  have hA : Tendsto (fun j => ⨍ y in ball z (s j), reducedNormal E hE hmE y
      ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) atTop
      (𝓝 (reducedNormal E hE hmE z)) :=
    (tendsto_average_reducedNormal E hE hmE hz).comp hsw
  have hinner := Filter.Tendsto.inner (𝕜 := ℝ) hlim hA
  have hlow : Tendsto (fun j => 1 - cylindricalExcess E hE hmE z (s j) (ν j) / Real.pi)
      atTop (𝓝 1) := by
    simpa using (hexc.div_const Real.pi).const_sub 1
  have hev : ∀ᶠ j in atTop, (1 - cylindricalExcess E hE hmE z (s j) (ν j) / Real.pi)
      ≤ inner ℝ (ν j) (⨍ y in ball z (s j), reducedNormal E hE hmE y
        ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
    filter_upwards [hs0.eventually (gt_mem_nhds hR)] with j hj
    exact one_sub_excess_div_pi_le_inner_average E hE hmE (hν j) (hspos j)
      (hdens (s j) (hspos j) hj)
  have hge : (1 : ℝ) ≤ inner ℝ νlim (reducedNormal E hE hmE z) :=
    le_of_tendsto_of_tendsto hlow hinner hev
  have hsq : ‖νlim - reducedNormal E hE hmE z‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hνlim, norm_reducedNormal E hE hmE hz]
    linarith
  have hzero : ‖νlim - reducedNormal E hE hmE z‖ = 0 := by
    nlinarith [norm_nonneg (νlim - reducedNormal E hE hmE z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Blueprint `thm:eps-regularity`, Step 3, in the geometric-decay form produced
by the excess iteration. -/
theorem limiting_normal_eq_reducedNormal (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {z : AmbientSpace} (hz : z ∈ reducedBoundary E hE hmE)
    {θ r : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r) (C M : ℝ)
    {ν : ℕ → AmbientSpace} (hν : ∀ j, ‖ν j‖ = 1)
    {νlim : AmbientSpace} (hνlim : ‖νlim‖ = 1) (hlim : Tendsto ν atTop (𝓝 νlim))
    (hdecay : ∀ j, cylindricalExcess E hE hmE z (θ ^ j * r) (ν j) ≤ C * θ ^ j * M) :
    νlim = reducedNormal E hE hmE z := by
  have hpow : Tendsto (fun j : ℕ => θ ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1
  refine limiting_normal_eq_reducedNormal_of_tendsto_excess E hE hmE hz
    (fun j => mul_pos (pow_pos hθ j) hr) (by simpa using hpow.mul_const r)
    hν hνlim hlim ?_
  refine squeeze_zero
    (fun j => div_nonneg (normalExcessIntegral_nonneg E hE hmE _ _) (sq_nonneg _))
    hdecay ?_
  simpa using (hpow.const_mul C).mul_const M

/-- Blueprint `thm:eps-regularity`, Steps 2 and 3 combined: the uniform-centre
iteration together with the identification of the limiting normal at every
reduced-boundary centre. -/
theorem normals_cauchy_uniform_centers_reduced :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 32 ∧ ∃ ε₀' > 0, ∃ C > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε₀' →
      ∀ z ∈ frontier (densityOne E) ∩ cylinder x (r / 8) ν₀,
      ∃ (ν : ℕ → AmbientSpace) (νlim : AmbientSpace),
        ν 0 = ν₀ ∧ (∀ j, ‖ν j‖ = 1) ∧ ‖νlim‖ = 1 ∧ Tendsto ν atTop (𝓝 νlim) ∧
        (z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable →
          νlim = reducedNormal E hE.locallyFinite hE.nullMeasurable z) ∧
        let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
          z (θ ^ j * (r / 8)) (ν j)
        ∀ j, e j + ω * (θ ^ j * (r / 8)) ≤ 64 * ε₀' ∧
          e j + ω * (θ ^ j * (r / 8)) ≤ C * θ ^ j * (e 0 + ω * (r / 8)) ∧
          ‖ν (j + 1) - ν j‖ ^ 2 ≤ C * (e j + ω * (θ ^ j * (r / 8))) ∧
          ‖ν j - νlim‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt (e 0 + ω * (r / 8)) := by
  obtain ⟨θ, hθ, hθ32, ε, hε, C, hC, hmain⟩ := normals_cauchy_uniform_centers
  refine ⟨θ, hθ, hθ32, ε, hε, C, hC, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ hx hsmall z hz
  obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hrest⟩ :=
    hmain E ω hE x r ν₀ hr hr1 hν₀ hx hsmall z hz
  refine ⟨ν, νlim, hinit, hunit, hnlim, htend, ?_, hrest⟩
  intro hzred
  have hr8 : (0 : ℝ) < r / 8 := by linarith
  have hdec : ∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable
        z (θ ^ j * (r / 8)) (ν j)
      ≤ C * θ ^ j * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable
        z (θ ^ 0 * (r / 8)) (ν 0) + ω * (r / 8)) := by
    intro j
    have h := (hrest j).2.1
    have hω : 0 ≤ ω * (θ ^ j * (r / 8)) :=
      mul_nonneg hE.nonneg (mul_nonneg (pow_nonneg hθ.le j) hr8.le)
    linarith
  exact limiting_normal_eq_reducedNormal E hE.locallyFinite hE.nullMeasurable hzred
    hθ (by linarith) hr8 _ _ hunit hnlim htend hdec

/-- Blueprint `thm:eps-regularity`, Step 3, angle bound. Below an absolute
threshold, the limiting normal at every boundary centre of the eighth cylinder
makes an angle less than `π / 4` with the initial axis, and at reduced-boundary
centres it is the measure-theoretic normal. -/
theorem limiting_normal_angle_uniform_centers :
    ∃ ε₀ > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε₀ →
      ∀ z ∈ frontier (densityOne E) ∩ cylinder x (r / 8) ν₀,
      ∃ νlim : AmbientSpace, ‖νlim‖ = 1 ∧
        Real.sqrt 2 / 2 < inner ℝ ν₀ νlim ∧
        (z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable →
          νlim = reducedNormal E hE.locallyFinite hE.nullMeasurable z) := by
  obtain ⟨θ, hθ, hθ32, ε, hε, C, hC, hmain⟩ := normals_cauchy_uniform_centers_reduced
  have hs2 : Real.sqrt 2 < 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hCsq : (0 : ℝ) < C ^ 2 := by positivity
  have hδ : (0 : ℝ) < (2 - Real.sqrt 2) / (128 * C ^ 2) := by
    apply div_pos (by linarith) (by positivity)
  refine ⟨min ε ((2 - Real.sqrt 2) / (128 * C ^ 2)), lt_min hε hδ, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ hx hsmall z hz
  have hsmall' : cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε :=
    hsmall.trans (min_le_left _ _)
  obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hred, hrest⟩ :=
    hmain E ω hE x r ν₀ hr hr1 hν₀ hx hsmall' z hz
  refine ⟨νlim, hnlim, ?_, hred⟩
  have hr8 : (0 : ℝ) < r / 8 := by linarith
  have hω : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
  have hE0 : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable z (r / 8) ν₀ :=
    div_nonneg (normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable _ _)
      (sq_nonneg _)
  have hcenter := excess_change_center E hE.locallyFinite hE.nullMeasurable hr hν₀ hz.2
  have hrate := (hrest 0).2.2.2
  simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one, pow_zero, one_mul,
    hinit] at hrate
  set T := cylindricalExcess E hE.locallyFinite hE.nullMeasurable z (r / 8) ν₀ +
    ω * (r / 8) with hT
  have hTnonneg : 0 ≤ T := by
    have : 0 ≤ ω * (r / 8) := mul_nonneg hE.nonneg hr8.le
    simp only [hT]; linarith
  have hTbound : T ≤ 64 * ((2 - Real.sqrt 2) / (128 * C ^ 2)) := by
    have h1 : cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤
        (2 - Real.sqrt 2) / (128 * C ^ 2) := hsmall.trans (min_le_right _ _)
    simp only [hT]
    linarith
  have hd : ‖ν₀ - νlim‖ ^ 2 ≤ C ^ 2 * T := by
    have hb := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC.le (Real.sqrt_nonneg _))).mpr hrate
    rwa [mul_pow, Real.sq_sqrt hTnonneg] at hb
  have hprod : C ^ 2 * T ≤ C ^ 2 * (64 * ((2 - Real.sqrt 2) / (128 * C ^ 2))) :=
    mul_le_mul_of_nonneg_left hTbound hCsq.le
  have hclean : C ^ 2 * (64 * ((2 - Real.sqrt 2) / (128 * C ^ 2))) = (2 - Real.sqrt 2) / 2 := by
    field_simp
    ring
  have hexpand : ‖ν₀ - νlim‖ ^ 2 = ‖ν₀‖ ^ 2 - 2 * inner ℝ ν₀ νlim + ‖νlim‖ ^ 2 :=
    norm_sub_sq_real ν₀ νlim
  rw [hν₀, hnlim] at hexpand
  linarith

/-- Blueprint `thm:eps-regularity`, Step 3: the measure-theoretic normal at every
reduced-boundary point of the eighth cylinder makes an angle less than `π / 4`
with the initial axis. -/
theorem reducedNormal_angle_uniform_centers :
    ∃ ε₀ > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε₀ →
      ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ cylinder x (r / 8) ν₀,
        Real.sqrt 2 / 2 <
          inner ℝ ν₀ (reducedNormal E hE.locallyFinite hE.nullMeasurable z) := by
  obtain ⟨ε₀, hε₀, hmain⟩ := limiting_normal_angle_uniform_centers
  refine ⟨ε₀, hε₀, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ hx hsmall z hz
  have hzf : z ∈ frontier (densityOne E) := by
    rw [hE.frontier_densityOne]
    exact reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable hz.1
  obtain ⟨νlim, _, hangle, hred⟩ :=
    hmain E ω hE x r ν₀ hr hr1 hν₀ hx hsmall z ⟨hzf, hz.2⟩
  rwa [hred hz.1] at hangle

end LiquidDrop
