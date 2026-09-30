module

public import NoCompromise.Regularity.MonotonicityRadial

@[expose] public section

/-!
# The exponential integrating factor in radial first variation

Tests supported in positive annuli remove the apparent singularity of the
powers of the radius. The resulting inequality is the genuine distributional
inequality for the exponentially weighted open-ball area ratio.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def radialWeightedTest (ω : ℝ) (m : ℕ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp (ω * r) * φ r / r ^ m

lemma tsupport_radialWeightedTest_subset (ω : ℝ) (m : ℕ) (φ : ℝ → ℝ) :
    tsupport (radialWeightedTest ω m φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro r hr
  apply subset_tsupport
  intro h
  exact hr (by simp [radialWeightedTest, h])

lemma contDiff_radialWeightedTest (ω : ℝ) (m : ℕ) {n : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ n φ) (hs : tsupport φ ⊆ Ioi 0) :
    ContDiff ℝ n (radialWeightedTest ω m φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    have hn : (0 : ℝ) ∉ tsupport φ := fun h => (lt_irrefl (0 : ℝ)) (hs h)
    have he : radialWeightedTest ω m φ =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [isClosed_tsupport φ |>.isOpen_compl.mem_nhds hn] with t ht
      simp [radialWeightedTest, image_eq_zero_of_notMem_tsupport ht]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (((contDiffAt_const.mul contDiffAt_id).exp).mul hφ.contDiffAt).div
      (contDiffAt_id.pow m) (pow_ne_zero m hr)

lemma continuous_radialWeightedTest (ω : ℝ) (m : ℕ) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hs : tsupport φ ⊆ Ioi 0) :
    Continuous (radialWeightedTest ω m φ) :=
  (contDiff_radialWeightedTest ω m (contDiff_zero.mpr hφ) hs).continuous

lemma hasCompactSupport_radialWeightedTest (ω : ℝ) (m : ℕ) {φ : ℝ → ℝ}
    (hcφ : HasCompactSupport φ) : HasCompactSupport (radialWeightedTest ω m φ) :=
  hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_radialWeightedTest_subset ω m φ)

lemma radialWeightedTest_nonneg (ω : ℝ) (m : ℕ) {φ : ℝ → ℝ}
    (hφ : ∀ r, 0 ≤ φ r) (hs : tsupport φ ⊆ Ioi 0) (r : ℝ) :
    0 ≤ radialWeightedTest ω m φ r := by
  by_cases hr : 0 ≤ r
  · exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ r)) (pow_nonneg hr _)
  · have hz : φ r = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (not_lt_of_ge (le_of_not_ge hr)) (hs h))
    simp [radialWeightedTest, hz]

lemma radialWeightedTest_three_mul_radius (ω : ℝ) (φ : ℝ → ℝ) (r : ℝ) :
    radialWeightedTest ω 3 φ r * r = radialWeightedTest ω 2 φ r := by
  by_cases hr : r = 0
  · simp [radialWeightedTest, hr]
  · unfold radialWeightedTest
    field_simp

lemma deriv_radialWeightedTest_two (ω : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {r : ℝ} (hr : r ≠ 0) :
    deriv (radialWeightedTest ω 2 φ) r = radialWeightedTest ω 2 (deriv φ) r +
      ω * radialWeightedTest ω 2 φ r - 2 * radialWeightedTest ω 3 φ r := by
  have he := (((hasDerivAt_id r).const_mul ω).exp.mul
    (hφ.differentiable one_ne_zero r).hasDerivAt).div
      ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)
  have hd : deriv (radialWeightedTest ω 2 φ) r =
      ((Real.exp (ω * r) * ω * φ r + Real.exp (ω * r) * deriv φ r) * r ^ 2 -
        Real.exp (ω * r) * φ r * (2 * r)) / (r ^ 2) ^ 2 := by
    simpa only [radialWeightedTest, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
      id_eq, mul_one, pow_one, Nat.cast_ofNat, Nat.reduceSub] using! he.deriv
  rw [hd]
  unfold radialWeightedTest
  field_simp
  ring

/-- The exponential area ratio has a distributional derivative dominating
its genuine positive radial tilt density on every annulus. -/
theorem weighted_radial_first_variation_weak (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (x : AmbientSpace) (hx : μ {x} = 0)
    (hfv : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ ball x 1 → |∫ y, tangentialDivergence X ν y ∂μ| ≤
        ω * ∫ y, |inner ℝ (X y) (ν y)| ∂μ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφn : ∀ r, 0 ≤ φ r) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hs : tsupport φ ⊆ Ioo a b) :
    (∫ y, φ ‖y - x‖ * (Real.exp (ω * ‖y - x‖) *
      (inner ℝ (y - x) (ν y)) ^ 2 / ‖y - x‖ ^ 4) ∂μ) ≤
      -(∫ r : ℝ, (Real.exp (ω * r) * μ.real (ball x r) / r ^ 2) * deriv φ r) := by
  have hs0 : tsupport φ ⊆ Ioi 0 := fun r hr => ha.trans (hs hr).1
  have hq := contDiff_radialWeightedTest ω 2 hφ hs0
  have hp := contDiff_radialWeightedTest ω 3 hφ hs0
  have hcq := hasCompactSupport_radialWeightedTest ω 2 hcφ
  have hcp := hasCompactSupport_radialWeightedTest ω 3 hcφ
  have h := radial_first_variation_kernel μ hν hn hω x hx hfv hp.continuous
    (radialWeightedTest_nonneg ω 3 hφn hs0) ha hb
    ((tsupport_radialWeightedTest_subset ω 3 φ).trans hs)
  have hcdf := integral_ball_mul_deriv μ (f := fun _ => (1 : ℝ))
    continuous_const.locallyIntegrable x hq hcq
  simp only [setIntegral_const, smul_eq_mul, mul_one, dist_eq_norm] at hcdf
  have hiq : Integrable (fun r : ℝ => μ.real (ball x r) * radialWeightedTest ω 2 φ r) :=
    (locallyIntegrable_ball_mass μ x).integrable_smul_right_of_hasCompactSupport
      hq.continuous hcq
  have hip : Integrable (fun r : ℝ => μ.real (ball x r) * radialWeightedTest ω 3 φ r) :=
    (locallyIntegrable_ball_mass μ x).integrable_smul_right_of_hasCompactSupport
      hp.continuous hcp
  have hid : Integrable (fun r : ℝ => μ.real (ball x r) *
      radialWeightedTest ω 2 (deriv φ) r) :=
    (locallyIntegrable_ball_mass μ x).integrable_smul_right_of_hasCompactSupport
      (continuous_radialWeightedTest ω 2 (hφ.continuous_deriv le_rfl)
        (tsupport_deriv_subset.trans hs0))
      (hasCompactSupport_radialWeightedTest ω 2 hcφ.deriv)
  have he (r : ℝ) : μ.real (ball x r) * deriv (radialWeightedTest ω 2 φ) r =
      (μ.real (ball x r) * radialWeightedTest ω 2 (deriv φ) r +
        ω * (μ.real (ball x r) * radialWeightedTest ω 2 φ r)) -
          2 * (μ.real (ball x r) * radialWeightedTest ω 3 φ r) := by
    by_cases hr : r = 0
    · simp [hr]
    · rw [deriv_radialWeightedTest_two ω hφ hr]
      ring
  simp only [he] at hcdf
  have his : Integrable (fun r : ℝ =>
      μ.real (ball x r) * radialWeightedTest ω 2 (deriv φ) r +
        ω * (μ.real (ball x r) * radialWeightedTest ω 2 φ r)) := by
    simpa only [Pi.add_apply] using! hid.add (hiq.const_mul ω)
  rw [integral_sub his (hip.const_mul 2),
    integral_add hid (hiq.const_mul ω), integral_const_mul, integral_const_mul] at hcdf
  have het (y : AmbientSpace) :
      (radialWeightedTest ω 3 φ ‖y - x‖ / ‖y - x‖) *
        (inner ℝ (y - x) (ν y)) ^ 2 =
      φ ‖y - x‖ * (Real.exp (ω * ‖y - x‖) *
        (inner ℝ (y - x) (ν y)) ^ 2 / ‖y - x‖ ^ 4) := by
    unfold radialWeightedTest
    ring
  have hem (r : ℝ) : r * radialWeightedTest ω 3 φ r =
      radialWeightedTest ω 2 φ r := by
    rw [mul_comm, radialWeightedTest_three_mul_radius]
  have hed (r : ℝ) : μ.real (ball x r) * radialWeightedTest ω 2 (deriv φ) r =
      (Real.exp (ω * r) * μ.real (ball x r) / r ^ 2) * deriv φ r := by
    unfold radialWeightedTest
    ring
  simp only [het, hem, radialWeightedTest_three_mul_radius] at h
  simp only [hed] at hcdf
  linarith

end LiquidDrop
