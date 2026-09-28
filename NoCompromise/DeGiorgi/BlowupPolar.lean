import NoCompromise.DeGiorgi.HalfspaceRigidity
import NoCompromise.DeGiorgi.ReducedPerimeter
import NoCompromise.DeGiorgi.BlowupCompactness
import NoCompromise.Measure.PositiveWeakStar
import Mathlib.Analysis.Convex.Integral

/-!
# Constant polar direction in blow-up limits

The unit vector-average limit at every reduced point controls the mean squared
polar error, and hence its mean norm. Positive weak-star extraction and the
scaled distributional test identities then identify the limiting polar field.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- For a unit field, the squared distance from a fixed unit vector is controlled
exactly by the vector average. -/
lemma average_sq_norm_sub_unit {μ : Measure AmbientSpace}
    {S : Set AmbientSpace} (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ∞)
    {σ : AmbientSpace → AmbientSpace} {ν : AmbientSpace}
    (hi : IntegrableOn σ S μ) (hu : ∀ᵐ y ∂μ.restrict S, ‖σ y‖ = 1) (hν : ‖ν‖ = 1) :
    (⨍ y in S, ‖σ y - ν‖ ^ 2 ∂μ) = 2 - 2 * inner ℝ ν (⨍ y in S, σ y ∂μ) := by
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have heq : (fun y => ‖σ y - ν‖ ^ 2) =ᵐ[μ.restrict S]
      (fun y => (2 : ℝ) - 2 * inner ℝ ν (σ y)) := by
    filter_upwards [hu] with y hy
    rw [norm_sub_sq_real, hy, hν, real_inner_comm]
    ring
  have hip : Integrable (fun y => inner ℝ ν (σ y)) (μ.restrict S) :=
    (innerSL ℝ ν).integrable_comp hi
  have havg : (⨍ y in S, inner ℝ ν (σ y) ∂μ) =
      inner ℝ ν (⨍ y in S, σ y ∂μ) :=
    (innerSL ℝ ν).integral_comp_comm hi.to_average
  rw [average_congr heq, average_fun_sub (integrable_const 2) (hip.const_mul 2),
    setAverage_const hS0 hSfin, average_const_mul, havg]

/-- Jensen controls the mean polar error by the square root of its exact squared error. -/
lemma average_norm_sub_unit_le {μ : Measure AmbientSpace}
    {S : Set AmbientSpace} (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ∞)
    {σ : AmbientSpace → AmbientSpace} {ν : AmbientSpace}
    (hi : IntegrableOn σ S μ) (hu : ∀ᵐ y ∂μ.restrict S, ‖σ y‖ = 1) (hν : ‖ν‖ = 1) :
    (⨍ y in S, ‖σ y - ν‖ ∂μ) ≤
      Real.sqrt (2 - 2 * inner ℝ ν (⨍ y in S, σ y ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have hi1 : Integrable (fun y => ‖σ y - ν‖) (μ.restrict S) := (hi.sub (integrable_const ν)).norm
  have hi2 : Integrable (fun y => ‖σ y - ν‖ ^ 2) (μ.restrict S) := by
    apply (integrable_const (4 : ℝ)).mono'
      ((hi.aestronglyMeasurable.sub stronglyMeasurable_const.aestronglyMeasurable).norm.pow 2)
    filter_upwards [hu] with y hy
    have hb : ‖σ y - ν‖ ≤ 2 := by simpa only [hy, hν, one_add_one_eq_two] using norm_sub_le (σ y) ν
    change ‖‖σ y - ν‖ ^ 2‖ ≤ 4
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (σ y - ν)]
  have hc : ConvexOn ℝ (Ici 0) (fun a : ℝ => a ^ 2) := convexOn_pow 2
  have hj := hc.map_set_average_le (by fun_prop) isClosed_Ici hS0 hSfin
    (Eventually.of_forall fun y => norm_nonneg (σ y - ν)) hi1 hi2
  rw [average_sq_norm_sub_unit hS0 hSfin hi hu hν] at hj
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt hj)

/-- The mean polar error vanishes at every point with a unit vector-average limit. -/
theorem tendsto_average_norm_sub_of_unit_average
    (μ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts μ]
    {σ : AmbientSpace → AmbientSpace} (hi : LocallyIntegrable σ μ)
    (hu : ∀ᵐ y ∂μ, ‖σ y‖ = 1) {x ν : AmbientSpace}
    (hx : x ∈ μ.support) (hν : ‖ν‖ = 1)
    (ht : Tendsto (fun r => ⨍ y in ball x r, σ y ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 ν)) :
    Tendsto (fun r => ⨍ y in ball x r, ‖σ y - ν‖ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (⨍ y in ball x r, ‖σ y - ν‖ ∂μ) ≤
        Real.sqrt (2 - 2 * inner ℝ ν (⨍ y in ball x r, σ y ∂μ)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hpos := (μ.mem_support_iff_forall x).mp hx (ball x r) (ball_mem_nhds x hr)
    have hfin : μ (ball x r) ≠ ∞ := ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall x r).measure_lt_top).ne
    exact average_norm_sub_unit_le hpos.ne' hfin
      ((hi.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall)
      (ae_restrict_of_ae hu) hν
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun y => norm_nonneg _) hbound
  have hlim := ((tendsto_const_nhds (x := (2 : ℝ))).sub
    (((innerSL ℝ ν).continuous.tendsto ν).comp ht |>.const_mul 2)).sqrt
  simpa only [Function.comp_def, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    hν, one_pow, mul_one, sub_self, Real.sqrt_zero] using hlim

/-- The canonical outward field has vanishing mean error at every reduced point. -/
theorem tendsto_average_polar_error_at_reduced
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) :
    Tendsto (fun r => ⨍ y in ball x r,
      ‖canonicalOutwardPolarDensity E hE hmE y - reducedNormal E hE hmE x‖
        ∂canonicalPerimeterMeasure E hE hmE) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  apply tendsto_average_norm_sub_of_unit_average _ h.locallyIntegrable h.norm_ae hx.1
    (norm_reducedNormal E hE hmE hx)
  have ht := (tendsto_normalized_perimeterDerivativeBall E hE hmE hx).neg
  simpa only [setAverage_eq, perimeterDerivativeBall, integral_neg, smul_neg, neg_neg] using ht

/-- The quadratic perimeter bound upgrades mean polar convergence to scale-normalized
integral convergence on every fixed blow-up ball. -/
theorem tendsto_scaled_polar_error_at_reduced
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun j => (r j)⁻¹ ^ 2 * ∫ y in ball x (r j * R),
      ‖canonicalOutwardPolarDensity E hE hmE y - reducedNormal E hE hmE x‖
        ∂canonicalPerimeterMeasure E hE hmE) atTop (𝓝 0) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let σ := canonicalOutwardPolarDensity E hE hmE
  let ν := reducedNormal E hE hmE x
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  obtain ⟨δ, hδ, hb⟩ := reduced_perimeter_upper_bound_real E hE hmE hx
  have htR : Tendsto (fun j => r j * R) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using ht.mul_const R, Eventually.of_forall fun j => mul_pos (hr j) hR⟩
  have he := (tendsto_average_polar_error_at_reduced E hE hmE hx).comp htR
  have htδ : ∀ᶠ j in atTop, r j * R ≤ δ :=
    (htR.mono_right nhdsWithin_le_nhds).eventually (Iic_mem_nhds hδ)
  have hbound : ∀ᶠ j in atTop,
      (r j)⁻¹ ^ 2 * (∫ y in ball x (r j * R), ‖σ y - ν‖ ∂μ) ≤
        (96 * Real.pi * R ^ 2) * (⨍ y in ball x (r j * R), ‖σ y - ν‖ ∂μ) := by
    filter_upwards [htδ] with j hj
    have hp := (μ.mem_support_iff_forall x).mp hx.1 (ball x (r j * R))
      (ball_mem_nhds x (mul_pos (hr j) hR))
    have hfin : μ (ball x (r j * R)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall x (r j * R)).measure_lt_top).ne
    have hreal : 0 < μ.real (ball x (r j * R)) := ENNReal.toReal_pos hp.ne' hfin
    have havg : (∫ y in ball x (r j * R), ‖σ y - ν‖ ∂μ) =
        μ.real (ball x (r j * R)) * (⨍ y in ball x (r j * R), ‖σ y - ν‖ ∂μ) := by
      rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hreal.ne', one_mul]
    rw [havg, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => norm_nonneg _)
    calc
      (r j)⁻¹ ^ 2 * μ.real (ball x (r j * R)) ≤
          (r j)⁻¹ ^ 2 * ((96 * Real.pi) * (r j * R) ^ 2) :=
        mul_le_mul_of_nonneg_left (hb _ (mul_pos (hr j) hR) hj) (sq_nonneg _)
      _ = 96 * Real.pi * R ^ 2 := by field_simp [(hr j).ne']
  apply squeeze_zero' (Eventually.of_forall fun j =>
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => norm_nonneg _)) hbound
  simpa only [mul_zero, Function.comp_def, μ, σ, ν] using he.const_mul (96 * Real.pi * R ^ 2)

/-- Forward translation and positive dilation for a blow-up. -/
def blowupHomeomorph (x : AmbientSpace) {r : ℝ} (hr : 0 < r) : AmbientSpace ≃ₜ AmbientSpace :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)

@[simp]
lemma blowupHomeomorph_apply (x y : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    blowupHomeomorph x hr y = x + r • y := rfl

@[simp]
lemma blowupHomeomorph_symm_apply (x y : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    (blowupHomeomorph x hr).symm y = r⁻¹ • (y - x) := by
  apply (blowupHomeomorph x hr).injective
  simp only [Homeomorph.apply_symm_apply, blowupHomeomorph_apply]
  simp [smul_smul, hr.ne']

/-- Perimeter-homogeneous rescaling of a positive measure in three dimensions. -/
def blowupPolarMeasure (μ : Measure AmbientSpace) (x : AmbientSpace) (r : ℝ) :
    Measure AmbientSpace :=
  ENNReal.ofReal (r⁻¹ ^ 2) • Measure.map (fun y => r⁻¹ • (y - x)) μ

lemma blowupPolarMeasure_apply (μ : Measure AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) {S : Set AmbientSpace} (hS : MeasurableSet S) :
    blowupPolarMeasure μ x r S =
      ENNReal.ofReal (r⁻¹ ^ 2) * μ ((fun y => x + r • y) '' S) := by
  have heq : (fun y : AmbientSpace => r⁻¹ • (y - x)) ⁻¹' S =
      (fun y => x + r • y) '' S := by
    ext y
    constructor
    · intro hy
      exact ⟨r⁻¹ • (y - x), hy, by simp [smul_smul, hr.ne']⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [smul_smul, hr.ne'] using hz
  rw [blowupPolarMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) hS, heq]

lemma blowupPolarMeasure_finiteOnCompacts (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasureOnCompacts (blowupPolarMeasure μ x r) := by
  constructor
  intro K hK
  rw [blowupPolarMeasure_apply μ x hr hK.measurableSet]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (hK.image (show Continuous (fun y : AmbientSpace => x + r • y) by fun_prop)).measure_lt_top

lemma integral_blowupPolarMeasure (μ : Measure AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (f : AmbientSpace → ℝ) :
    (∫ y, f y ∂blowupPolarMeasure μ x r) = r⁻¹ ^ 2 * ∫ y, f (r⁻¹ • (y - x)) ∂μ := by
  rw [blowupPolarMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  congr 1
  have h := (blowupHomeomorph x hr).symm.measurableEmbedding.integral_map (μ := μ) f
  have he : ⇑(blowupHomeomorph x hr).symm = (fun y => r⁻¹ • (y - x)) :=
    funext (blowupHomeomorph_symm_apply x · hr)
  simpa only [he] using h

/-- The rescaled positive polar measures have uniformly bounded mass on every compact set. -/
theorem eventually_bounded_blowupPolarMeasure
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {K : Set AmbientSpace} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ᶠ j in atTop,
      (blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x (r j) K).toReal ≤ C := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  refine ⟨96 * Real.pi * R ^ 2, ?_⟩
  filter_upwards [eventually_perimeterIn_blowupSet_ball_le E hE hmE hx hr ht hR] with j hj
  have : IsFiniteMeasureOnCompacts (blowupPolarMeasure μ x (r j)) :=
    blowupPolarMeasure_finiteOnCompacts μ x (hr j)
  have hle := ENNReal.toReal_mono
    (((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : AmbientSpace) R).measure_lt_top).ne :
      blowupPolarMeasure μ x (r j) (ball 0 R) ≠ ∞) (measure_mono hKR)
  apply hle.trans
  rw [blowupPolarMeasure_apply μ x (hr j) measurableSet_ball,
    image_ball_translate_pos_smul x (hr j), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  simpa only [perimeterIn_blowupSet_ball_real E hE hmE x (hr j), measureReal_def] using hj

/-- Pull a compact scalar test back from blow-up coordinates to the original space. -/
def blowupPullbackTest (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) : CompactlySupportedContinuousMap AmbientSpace ℝ :=
  ⟨⟨fun y => φ (r⁻¹ • (y - x)), φ.continuous.comp (by fun_prop)⟩,
    by simpa only [Function.comp_def, blowupHomeomorph_symm_apply] using
      φ.hasCompactSupport.comp_homeomorph (blowupHomeomorph x hr).symm⟩

@[simp]
lemma blowupPullbackTest_apply (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (x y : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    blowupPullbackTest φ x hr y = φ (r⁻¹ • (y - x)) := rfl

lemma contDiff_blowupPullbackTest {φ : CompactlySupportedContinuousMap AmbientSpace ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (blowupPullbackTest φ x hr) :=
  hφ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

lemma fderiv_blowupPullbackTest {φ : CompactlySupportedContinuousMap AmbientSpace ℝ}
    (hφ : ContDiff ℝ 1 φ) (x y v : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (blowupPullbackTest φ x hr) y v = r⁻¹ * fderiv ℝ φ (r⁻¹ • (y - x)) v := by
  have hd := ((hφ.differentiable one_ne_zero _).hasFDerivAt.comp y
    (((hasFDerivAt_id y).sub_const x).const_smul r⁻¹)).fderiv
  change fderiv ℝ (fun z => φ (r⁻¹ • (z - x))) y v = _
  simpa [Function.comp_def] using congrArg (fun A => A v) hd

/-- The real-valued change of variables used in the scaled distributional pairing. -/
lemma integral_comp_blowupCoordinates (f : AmbientSpace → ℝ) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    (∫ y, f (r⁻¹ • (y - x))) = r ^ 3 * ∫ y, f y := by
  calc
    _ = ∫ y, f (r⁻¹ • ((x + y) - x)) :=
      (integral_add_left_eq_self (fun y : AmbientSpace => f (r⁻¹ • (y - x))) x).symm
    _ = ∫ y, f (r⁻¹ • y) := by simp
    _ = r ^ 3 * ∫ y, f y := by
      have h := setIntegral_image_smul (fun y : AmbientSpace => f (r⁻¹ • y)) univ hr
      have hs : Function.Surjective (fun y : AmbientSpace => r • y) :=
        (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hr.ne')).surjective
      simpa only [image_univ_of_surjective hs, setIntegral_univ, smul_smul,
        inv_mul_cancel₀ hr.ne', one_smul] using h

lemma indicator_blowup_inverse (E : Set AmbientSpace) (x y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    (blowupSet E x r).indicator (fun _ => (1 : ℝ)) (r⁻¹ • (y - x)) =
      E.indicator (fun _ => (1 : ℝ)) y := by
  have heq : r⁻¹ • (y - x) ∈ blowupSet E x r ↔ y ∈ E := by
    simp [blowupSet, smul_smul, hr.ne']
  by_cases hy : y ∈ E
  · simp [hy, heq.mpr hy]
  · have hn : r⁻¹ • (y - x) ∉ blowupSet E x r := fun h => hy (heq.mp h)
    simp only [indicator_of_notMem hn, indicator_of_notMem hy]

/-- Exact coordinate pairing for an actual positive-scale blow-up. -/
theorem IsAmbientOutwardPerimeterPolar.blowup_coordinate_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (i : Fin 3)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (hφ : ContDiff ℝ 1 φ) :
    -(∫ y, (blowupSet E x r).indicator (fun _ => (1 : ℝ)) y *
      fderiv ℝ φ y (EuclideanSpace.single i 1)) =
      r⁻¹ ^ 2 * ∫ y, φ (r⁻¹ • (y - x)) * (-σ y i) ∂μ := by
  have hp := h.coordinate_eq i (blowupPullbackTest φ x hr) (contDiff_blowupPullbackTest hφ x hr)
  simp_rw [fderiv_blowupPullbackTest hφ, ← mul_assoc, mul_comm _ r⁻¹] at hp
  have hscale := integral_comp_blowupCoordinates
    (fun y => (blowupSet E x r).indicator (fun _ => (1 : ℝ)) y *
      fderiv ℝ φ y (EuclideanSpace.single i 1)) x hr
  simp only [indicator_blowup_inverse E x _ hr] at hscale
  have hp' : -(r⁻¹ * (r ^ 3 * ∫ y,
      (blowupSet E x r).indicator (fun _ => (1 : ℝ)) y *
        fderiv ℝ φ y (EuclideanSpace.single i 1))) =
      ∫ y, φ (r⁻¹ • (y - x)) * (-σ y i) ∂μ := by
    rw [← hscale, ← integral_const_mul]
    simpa only [mul_assoc, blowupPullbackTest_apply] using hp
  rw [← hp']
  field_simp [hr.ne']

lemma tsupport_blowupPullbackTest_subset
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (x : AmbientSpace)
    {r R : ℝ} (hr : 0 < r) (hφ : tsupport φ ⊆ ball 0 R) :
    tsupport (blowupPullbackTest φ x hr) ⊆ ball x (r * R) := by
  have he : (blowupPullbackTest φ x hr : AmbientSpace → ℝ) =
      (φ : AmbientSpace → ℝ) ∘ (blowupHomeomorph x hr).symm := by
    funext y
    simp only [Function.comp_def, blowupPullbackTest_apply, blowupHomeomorph_symm_apply]
  rw [he, tsupport_comp_eq_preimage]
  intro y hy
  have hy' : y ∈ (fun z => x + r • z) '' ball 0 R := by
    refine ⟨(blowupHomeomorph x hr).symm y, hφ hy, ?_⟩
    exact (blowupHomeomorph x hr).apply_symm_apply y
  rwa [image_ball_translate_pos_smul x hr R] at hy'

/-- Compact scalar weights bound a coordinate error by the full polar norm error. -/
lemma abs_integral_compact_mul_coordinate_sub_le
    (μ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts μ]
    {σ : AmbientSpace → AmbientSpace} (hσ : LocallyIntegrable σ μ) (ν : AmbientSpace)
    (ψ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3)
    {x : AmbientSpace} {R C : ℝ} (hs : tsupport ψ ⊆ ball x R)
    (hb : ∀ y, |ψ y| ≤ C) :
    |∫ y, ψ y * (ν i - σ y i) ∂μ| ≤ C * ∫ y in ball x R, ‖σ y - ν‖ ∂μ := by
  have hd : LocallyIntegrable (fun y => ν - σ y) μ := continuous_const.locallyIntegrable.sub hσ
  have hiG := hd.integrable_smul_left_of_hasCompactSupport ψ.continuous ψ.hasCompactSupport
  have hi : Integrable (fun y => ψ y * (ν i - σ y i)) μ := by
    simpa only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      CompactlySupportedContinuousMap.coe_toContinuousMap] using
      hiG.eval_piLp i
  have hin : IntegrableOn (fun y => ‖σ y - ν‖) (ball x R) μ := by
    have hij := (hσ.sub (show LocallyIntegrable (fun _ => ν) μ from
      continuous_const.locallyIntegrable)).integrableOn_isCompact (isCompact_closedBall x R)
    exact (hij.mono_set ball_subset_closedBall).norm
  have heq : (∫ y in ball x R, ψ y * (ν i - σ y i) ∂μ) =
      ∫ y, ψ y * (ν i - σ y i) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)), zero_mul]
  rw [← heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y in ball x R, ‖ψ y * (ν i - σ y i)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in ball x R, C * ‖σ y - ν‖ ∂μ := by
      apply integral_mono_ae hi.integrableOn.norm (hin.const_mul C)
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [norm_mul, Real.norm_eq_abs]
        have hc : ‖ν i - σ y i‖ ≤ ‖σ y - ν‖ := by
          simpa only [PiLp.sub_apply, norm_sub_rev] using PiLp.norm_apply_le (ν - σ y) i
        exact mul_le_mul (hb y) hc (norm_nonneg _) ((abs_nonneg _).trans (hb y))
    _ = _ := integral_const_mul C _

/-- The scaled pairing differs from the constant-normal pairing by the exact polar error. -/
lemma IsAmbientOutwardPerimeterPolar.blowup_pairing_error
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (x ν : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (i : Fin 3)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (hφ : ContDiff ℝ 1 φ) :
    -(∫ y, (blowupSet E x r).indicator (fun _ => (1 : ℝ)) y *
      fderiv ℝ φ y (EuclideanSpace.single i 1)) -
        (-ν i) * (∫ y, φ y ∂blowupPolarMeasure μ x r) =
      r⁻¹ ^ 2 * ∫ y, φ (r⁻¹ • (y - x)) * (ν i - σ y i) ∂μ := by
  let := h.finiteOnCompacts
  let ψ := blowupPullbackTest φ x hr
  have hiG := h.locallyIntegrable.neg.integrable_smul_left_of_hasCompactSupport
    ψ.continuous ψ.hasCompactSupport
  have hi : Integrable (fun y => ψ y * (-σ y i)) μ := by
    simpa only [PiLp.smul_apply, PiLp.neg_apply, Pi.neg_apply, smul_eq_mul,
      CompactlySupportedContinuousMap.coe_toContinuousMap] using
      hiG.eval_piLp i
  have hc : Integrable (fun y => ψ y * (-ν i)) μ :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport |>.mul_const _
  rw [h.blowup_coordinate_pairing x hr i φ hφ, integral_blowupPolarMeasure μ x hr]
  change r⁻¹ ^ 2 * (∫ y, ψ y * (-σ y i) ∂μ) - (-ν i) *
    (r⁻¹ ^ 2 * ∫ y, ψ y ∂μ) = r⁻¹ ^ 2 * ∫ y, ψ y * (ν i - σ y i) ∂μ
  calc
    _ = r⁻¹ ^ 2 * ((∫ y, ψ y * (-σ y i) ∂μ) - (∫ y, ψ y * (-ν i) ∂μ)) := by
      rw [integral_mul_const]; ring
    _ = _ := by
      rw [← integral_sub hi hc]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by ring

/-- Every fixed smooth compact test has vanishing constant-normal pairing error. -/
theorem tendsto_blowup_pairing_error_at_reduced
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (hφ : ContDiff ℝ 1 φ) :
    Tendsto (fun j =>
      -(∫ y, (blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y *
        fderiv ℝ φ y (EuclideanSpace.single i 1)) -
      (-reducedNormal E hE hmE x i) *
        (∫ y, φ y ∂blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x (r j)))
      atTop (𝓝 0) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let σ := canonicalOutwardPolarDensity E hE hmE
  let ν := reducedNormal E hE hmE x
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  obtain ⟨R, hR, hφR⟩ := φ.hasCompactSupport.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (g := fun j => ‖φ.toBoundedContinuousFunction‖ *
    ((r j)⁻¹ ^ 2 * ∫ y in ball x (r j * R), ‖σ y - ν‖ ∂μ))
    (fun _ => norm_nonneg _) (fun j => ?_) ?_
  · rw [hp.blowup_pairing_error x ν (hr j) i φ hφ, norm_mul,
      Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    have hb := abs_integral_compact_mul_coordinate_sub_le μ hp.locallyIntegrable ν
      (blowupPullbackTest φ x (hr j)) i
      (tsupport_blowupPullbackTest_subset φ x (hr j) hφR)
      (fun y => by
        simpa only [blowupPullbackTest_apply, Real.norm_eq_abs,
          CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
          φ.toBoundedContinuousFunction.norm_coe_le_norm ((r j)⁻¹ • (y - x)))
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq (by ring)
  · simpa only [mul_zero] using
      (tendsto_scaled_polar_error_at_reduced E hE hmE hx hr ht hR).const_mul
        ‖φ.toBoundedContinuousFunction‖

/-- Local indicator convergence passes all compact C¹ coordinate test pairings to the limit. -/
theorem tendsto_indicator_coordinate_pairing_of_locally_l1
    (E : ℕ → Set AmbientSpace) {F : Set AmbientSpace}
    (hE : ∀ j, NullMeasurableSet (E j) volume) (hF : NullMeasurableSet F volume)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
        atTop (𝓝 0))
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (hφ : ContDiff ℝ 1 φ) :
    Tendsto (fun j => -(∫ y, (E j).indicator (fun _ => (1 : ℝ)) y *
      fderiv ℝ φ y (EuclideanSpace.single i 1))) atTop
      (𝓝 (-(∫ y, F.indicator (fun _ => (1 : ℝ)) y *
        fderiv ℝ φ y (EuclideanSpace.single i 1)))) := by
  have hsupport (u : AmbientSpace → ℝ) :
      (∫ y in tsupport φ, u y * fderiv ℝ φ y (EuclideanSpace.single i 1)) =
        ∫ y, u y * fderiv ℝ φ y (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ hy]
    simp
  have ht := tendsto_integral_mul_of_l1_on_compact
    (ψ := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) φ.hasCompactSupport
    (fun j => (locallyIntegrable_indicator_one (hE j)).integrableOn_isCompact φ.hasCompactSupport)
    ((locallyIntegrable_indicator_one hF).integrableOn_isCompact φ.hasCompactSupport)
    (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
    (hlim (tsupport φ) φ.hasCompactSupport)
  simp_rw [hsupport] at ht
  exact ht.neg

/-- Positive rescaled perimeter measures admit a subsequential locally finite limit whose
constant polar identity is identified by the local L¹ limit of the actual blow-up indicators.
The same subsequence retains convergence on every compact continuous test. -/
theorem exists_blowup_constant_polar_limit
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {F : Set AmbientSpace} (hF : NullMeasurableSet F volume)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)) :
    ∃ (μ : Measure AmbientSpace) (τ : ℕ → ℕ), StrictMono τ ∧ μ.Regular ∧
      IsFiniteMeasureOnCompacts μ ∧ HasConstantIndicatorPolar F μ (reducedNormal E hE hmE x) ∧
      ∀ φ : CompactlySupportedContinuousMap AmbientSpace ℝ,
        Tendsto (fun j => ∫ y, φ y ∂blowupPolarMeasure
          (canonicalPerimeterMeasure E hE hmE) x (r (τ j))) atTop (𝓝 (∫ y, φ y ∂μ)) := by
  let μ₀ := canonicalPerimeterMeasure E hE hmE
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let M (j : ℕ) := blowupPolarMeasure μ₀ x (r j)
  let : ∀ j, IsFiniteMeasureOnCompacts (M j) :=
    fun j => blowupPolarMeasure_finiteOnCompacts μ₀ x (hr j)
  obtain ⟨μ, τ, hτ, hμ, hμfin, htest⟩ := exists_subseq_positive_measure_of_eventually M
    (fun K hK => eventually_bounded_blowupPolarMeasure E hE hmE hx hr ht hK)
  refine ⟨μ, τ, hτ, hμ, hμfin, ?_, htest⟩
  intro i φ hφ
  have hleft := (tendsto_indicator_coordinate_pairing_of_locally_l1
    (fun j => blowupSet E x (r j))
    (fun j => nullMeasurableSet_blowupSet hmE x (hr j)) hF hlim i φ hφ).comp hτ.tendsto_atTop
  have hright := (htest φ).const_mul (-reducedNormal E hE hmE x i)
  have herr := (tendsto_blowup_pairing_error_at_reduced E hE hmE hx hr ht i φ hφ).comp
    hτ.tendsto_atTop
  have heq := tendsto_nhds_unique (hleft.sub hright) herr
  rw [integral_mul_const]
  linarith

end LiquidDrop
