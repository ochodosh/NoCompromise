import NoCompromise.Regularity.MonotonicityPrimitive
import NoCompromise.Regularity.MonotonicityTests
import NoCompromise.Regularity.RadialField
import NoCompromise.Regularity.FirstVariation

/-!
# Radial first-variation inequalities

Compact radial primitives turn the geometric first-variation estimate into a
one-dimensional weak inequality. Ball masses are used with their left-continuous
open-ball convention, and every tilt integral is localized away from radius zero.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma locallyIntegrable_ball_mass (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (x : AmbientSpace) :
    LocallyIntegrable (fun r : ℝ => μ.real (ball x r)) volume := by
  have h := locallyIntegrable_integral_ball_real μ (f := fun _ => (1 : ℝ))
    measurable_const continuous_const.locallyIntegrable x
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using h

lemma integral_radial_primitive_eq_ball_mass (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (x : AmbientSpace) {η p : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hd : ∀ r, 0 ≤ r → HasDerivAt η (-p r) r) :
    (∫ y, η ‖y - x‖ ∂μ) = ∫ r : ℝ, μ.real (ball x r) * p r := by
  have h := integral_ball_mul_deriv μ (f := fun _ => (1 : ℝ))
    continuous_const.locallyIntegrable x hη hcη
  simp only [setIntegral_const, smul_eq_mul, mul_one, dist_eq_norm] at h
  have he (r : ℝ) : μ.real (ball x r) * deriv η r = -(μ.real (ball x r) * p r) := by
    by_cases hr : 0 ≤ r
    · rw [(hd r hr).deriv]
      ring
    · simp only [ball_eq_empty.mpr (le_of_not_ge hr), measureReal_empty, zero_mul, neg_zero]
  simp only [he, integral_neg] at h
  linarith

lemma integral_radius_mul_radial_primitive_le_ball_mass (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (x : AmbientSpace) {η p : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hnη : ∀ r, 0 ≤ η r)
    (hp : Continuous p) (hcp : HasCompactSupport p)
    (hd : ∀ r, 0 ≤ r → HasDerivAt η (-p r) r) :
    (∫ y, ‖y - x‖ * η ‖y - x‖ ∂μ) ≤
      ∫ r : ℝ, μ.real (ball x r) * (r * p r) := by
  have hc : HasCompactSupport (fun r : ℝ => r * η r) := hcη.mul_left
  have h := integral_ball_mul_deriv μ (f := fun _ => (1 : ℝ))
    continuous_const.locallyIntegrable x (contDiff_id.mul hη) hc
  simp only [setIntegral_const, smul_eq_mul, mul_one, dist_eq_norm, id_eq] at h
  have he (r : ℝ) : μ.real (ball x r) * deriv (fun t : ℝ => t * η t) r =
      μ.real (ball x r) * η r - μ.real (ball x r) * (r * p r) := by
    by_cases hr : 0 ≤ r
    · have hd' : HasDerivAt (fun t : ℝ => t * η t) (η r + r * (-p r)) r := by
        simpa only [id_eq, one_mul] using! (hasDerivAt_id r).mul (hd r hr)
      rw [hd'.deriv]
      ring
    · simp only [ball_eq_empty.mpr (le_of_not_ge hr), measureReal_empty, zero_mul, sub_self]
  have hiη : Integrable (fun r : ℝ => μ.real (ball x r) * η r) :=
    (locallyIntegrable_ball_mass μ x).integrable_smul_right_of_hasCompactSupport
      hη.continuous hcη
  have hip : Integrable (fun r : ℝ => μ.real (ball x r) * (r * p r)) :=
    (locallyIntegrable_ball_mass μ x).integrable_smul_right_of_hasCompactSupport
      (continuous_id.mul hp) hcp.mul_left
  simp only [he] at h
  rw [integral_sub hiη hip] at h
  have hn : 0 ≤ ∫ r : ℝ, μ.real (ball x r) * η r :=
    integral_nonneg fun r => mul_nonneg (measureReal_nonneg) (hnη r)
  linarith

lemma hasCompactSupport_radial_coefficient {q : ℝ → ℝ} {b : ℝ}
    (hq : ∀ r, b ≤ r → q r = 0) (x : AmbientSpace) :
    HasCompactSupport (fun y : AmbientSpace => q ‖y - x‖) := by
  apply (isCompact_closedBall x b).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hn
  have hr : b < ‖y - x‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  exact hy (hq _ hr.le)

lemma integrable_radial_coefficient (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {q : ℝ → ℝ} (hq : Continuous q) {b : ℝ}
    (hz : ∀ r, b ≤ r → q r = 0) (x : AmbientSpace) :
    Integrable (fun y : AmbientSpace => q ‖y - x‖) μ :=
  (hq.comp (continuous_id.sub continuous_const).norm).integrable_of_hasCompactSupport
    (hasCompactSupport_radial_coefficient hz x)

lemma radial_tangential_divergence_centered {η : ℝ → ℝ} {a : ℝ}
    {x y : AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hy : y ≠ x) (hη : HasDerivAt η a ‖y - x‖) (hν : ‖ν y‖ = 1) :
    tangentialDivergence (fun z => η ‖z - x‖ • (z - x)) ν y =
      2 * η ‖y - x‖ + (a / ‖y - x‖) *
        (‖y - x‖ ^ 2 - (inner ℝ (y - x) (ν y)) ^ 2) := by
  have hbase := hasFDerivAt_radial_field (sub_ne_zero.mpr hy) hη
  have hd := hbase.comp y ((hasFDerivAt_id y).sub_const x)
  have hD : fderiv ℝ (fun z => η ‖z - x‖ • (z - x)) y =
      fderiv ℝ (fun z => η ‖z‖ • z) (y - x) := by
    rw [hbase.fderiv]
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using! hd.fderiv
  have h := radial_tangential_divergence (ν := fun z => ν (z + x))
    (sub_ne_zero.mpr hy) hη (by simpa only [sub_add_cancel] using hν)
  simpa only [tangentialDivergence, divergenceN, hD, sub_add_cancel] using h

lemma integrable_radial_tilt_profile (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {p : ℝ → ℝ}
    (hp : Continuous p) (hpn : ∀ r, 0 ≤ p r) {b : ℝ}
    (hpz : ∀ r, b ≤ r → p r = 0) (x : AmbientSpace) :
    Integrable (fun y => (p ‖y - x‖ / ‖y - x‖) * (inner ℝ (y - x) (ν y)) ^ 2) μ := by
  have hi : Integrable (fun y : AmbientSpace => p ‖y - x‖ * ‖y - x‖) μ :=
    integrable_radial_coefficient (q := fun r => p r * r) μ (hp.mul continuous_id)
      (fun r hr => by rw [hpz r hr, zero_mul]) x
  have hm : Measurable (fun y => (p ‖y - x‖ / ‖y - x‖) *
      (inner ℝ (y - x) (ν y)) ^ 2) := by
    have hr := (continuous_id.sub (continuous_const (y := x))).norm.measurable
    exact ((hp.measurable.comp hr).div hr).mul
      (((continuous_id.sub continuous_const).measurable.inner hν).pow_const 2)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [hn] with y hy
  have hinner : |inner ℝ (y - x) (ν y)| ≤ ‖y - x‖ := by
    simpa only [Real.norm_eq_abs, hy, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (y - x) (ν y)
  have hsq : (inner ℝ (y - x) (ν y)) ^ 2 ≤ ‖y - x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y - x‖ - |inner ℝ (y - x) (ν y)|),
      abs_nonneg (inner ℝ (y - x) (ν y)), sq_abs (inner ℝ (y - x) (ν y))]
  rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (hpn _) (norm_nonneg _)) (sq_nonneg _))]
  calc
    _ ≤ (p ‖y - x‖ / ‖y - x‖) * ‖y - x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (div_nonneg (hpn _) (norm_nonneg _))
    _ = p ‖y - x‖ * ‖y - x‖ := by
      by_cases hzero : ‖y - x‖ = 0
      · simp [hzero]
      · field_simp

/-- The exact radial first-variation comparison before introducing an integrating factor. -/
theorem radial_first_variation_profile (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (x : AmbientSpace) (hx : μ {x} = 0)
    (hfv : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ ball x 1 → |∫ y, tangentialDivergence X ν y ∂μ| ≤
        ω * ∫ y, |inner ℝ (X y) (ν y)| ∂μ)
    {η p : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hη0 : ∀ᶠ r in 𝓝 (0 : ℝ), η r = η 0) (hηn : ∀ r, 0 ≤ η r)
    (hp : Continuous p) (hcp : HasCompactSupport p) (hpn : ∀ r, 0 ≤ p r)
    {b : ℝ} (hb : b < 1) (hηz : ∀ r, b ≤ r → η r = 0)
    (hpz : ∀ r, b ≤ r → p r = 0)
    (hd : ∀ r, 0 ≤ r → HasDerivAt η (-p r) r) :
    2 * (∫ r : ℝ, μ.real (ball x r) * p r) +
        (∫ y, (p ‖y - x‖ / ‖y - x‖) * (inner ℝ (y - x) (ν y)) ^ 2 ∂μ) ≤
      (∫ y, p ‖y - x‖ * ‖y - x‖ ∂μ) +
        ω * ∫ r : ℝ, μ.real (ball x r) * (r * p r) := by
  obtain ⟨hX, hcX, hsX⟩ := radial_test_field hη hη0 hb hηz x
  have h := hfv (fun y => η ‖y - x‖ • (y - x)) hX hcX hsX
  have hiη := integrable_radial_coefficient μ hη.continuous hηz x
  have hip : Integrable (fun y : AmbientSpace => p ‖y - x‖ * ‖y - x‖) μ :=
    integrable_radial_coefficient (q := fun r => p r * r) μ (hp.mul continuous_id)
      (fun r hr => by rw [hpz r hr, zero_mul]) x
  have hiT := integrable_radial_tilt_profile μ hν hn hp hpn hpz x
  have hiR : Integrable (fun y : AmbientSpace => ‖y - x‖ * η ‖y - x‖) μ :=
    integrable_radial_coefficient (q := fun r => r * η r) μ (continuous_id.mul hη.continuous)
      (fun r hr => by rw [hηz r hr, mul_zero]) x
  have hbound : ∀ᵐ y ∂μ,
      |inner ℝ (η ‖y - x‖ • (y - x)) (ν y)| ≤ ‖y - x‖ * η ‖y - x‖ := by
    filter_upwards [hn] with y hy
    have hh := norm_inner_le_norm (𝕜 := ℝ) (η ‖y - x‖ • (y - x)) (ν y)
    simpa only [Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg (hηn _), hy,
      mul_one, one_mul, mul_comm] using hh
  have hiN : Integrable (fun y => |inner ℝ (η ‖y - x‖ • (y - x)) (ν y)|) μ :=
    hiR.mono' (by fun_prop) (hbound.mono fun y hy => by
      simpa only [Real.norm_eq_abs, abs_abs] using hy)
  have hrhs := (integral_mono_ae hiN hiR hbound).trans
    (integral_radius_mul_radial_primitive_le_ball_mass μ x hη hcη hηn hp hcp hd)
  have hae : ∀ᵐ y ∂μ, y ≠ x := by
    simpa only [mem_singleton_iff] using measure_eq_zero_iff_ae_notMem.mp hx
  have he : (fun y => tangentialDivergence (fun z => η ‖z - x‖ • (z - x)) ν y) =ᵐ[μ]
      fun y => (2 * η ‖y - x‖ - p ‖y - x‖ * ‖y - x‖) +
        (p ‖y - x‖ / ‖y - x‖) * (inner ℝ (y - x) (ν y)) ^ 2 := by
    filter_upwards [hae, hn] with y hy hyn
    rw [radial_tangential_divergence_centered hy (hd _ (norm_nonneg _)) hyn]
    have hz : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
    field_simp
    ring
  have hleft := (le_abs_self (∫ y,
    tangentialDivergence (fun z => η ‖z - x‖ • (z - x)) ν y ∂μ)).trans h
  have hiS : Integrable (fun y : AmbientSpace => 2 * η ‖y - x‖ -
      p ‖y - x‖ * ‖y - x‖) μ := by
    simpa only [Pi.sub_apply] using! (hiη.const_mul 2).sub hip
  rw [integral_congr_ae he, integral_add hiS hiT,
    integral_sub (hiη.const_mul 2) hip, integral_const_mul,
    integral_radial_primitive_eq_ball_mass μ x hη hcη hd] at hleft
  have hh := mul_le_mul_of_nonneg_left hrhs hω
  linarith

/-- Nonnegative kernels supported in a positive annulus satisfy the actual
radial measure inequality supplied by bounded first variation. -/
theorem radial_first_variation_kernel (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (x : AmbientSpace) (hx : μ {x} = 0)
    (hfv : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ ball x 1 → |∫ y, tangentialDivergence X ν y ∂μ| ≤
        ω * ∫ y, |inner ℝ (X y) (ν y)| ∂μ)
    {p : ℝ → ℝ} (hp : Continuous p) (hpn : ∀ r, 0 ≤ p r)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hs : tsupport p ⊆ Ioo a b) :
    2 * (∫ r : ℝ, μ.real (ball x r) * p r) +
        (∫ y, (p ‖y - x‖ / ‖y - x‖) * (inner ℝ (y - x) (ν y)) ^ 2 ∂μ) ≤
      (∫ y, p ‖y - x‖ * ‖y - x‖ ∂μ) +
        ω * ∫ r : ℝ, μ.real (ball x r) * (r * p r) := by
  obtain ⟨η, hη, hcη, hη0, hηz, hηn, hd⟩ :=
    exists_compact_radial_primitive hp ha hs hpn
  have hcp : HasCompactSupport p :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs.trans Ioo_subset_Icc_self)
  have hpz : ∀ r, b ≤ r → p r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport (fun h => (not_lt_of_ge hr) (hs h).2)
  exact radial_first_variation_profile μ hν hn hω x hx hfv hη hcη hη0 hηn hp hcp hpn
    hb hηz hpz hd

end LiquidDrop
