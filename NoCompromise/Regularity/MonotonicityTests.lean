module

public import NoCompromise.BV.CoareaSmooth
public import NoCompromise.Measure.RadialCumulative

@[expose] public section

/-!
# One-sided smooth interval tests for radial monotonicity

The profiles approach `[σ, ρ)` pointwise, including both endpoints. Their two
transition derivatives are probability kernels approaching the endpoints from
the left. This preserves the correct convention for possible sphere atoms.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A smooth approximation of the half-open interval `[σ, ρ)`. -/
def monotonicityIntervalTest (k σ ρ t : ℝ) : ℝ :=
  Real.smoothTransition (k * (ρ - t)) - Real.smoothTransition (k * (σ - t))

lemma contDiff_monotonicityIntervalTest (k σ ρ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (monotonicityIntervalTest k σ ρ) :=
  (Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub contDiff_id))).sub
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_const.sub contDiff_id)))

lemma monotonicityIntervalTest_nonneg {k σ ρ : ℝ} (hk : 0 ≤ k) (hσρ : σ ≤ ρ) (t : ℝ) :
    0 ≤ monotonicityIntervalTest k σ ρ t := by
  apply sub_nonneg.mpr
  exact Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left (by linarith) hk)

lemma monotonicityIntervalTest_le_one (k σ ρ t : ℝ) :
    monotonicityIntervalTest k σ ρ t ≤ 1 :=
  (sub_le_self _ (Real.smoothTransition.nonneg _)).trans (Real.smoothTransition.le_one _)

lemma monotonicityIntervalTest_eq_zero_left {k σ ρ t : ℝ}
    (hk : 0 < k) (hσρ : σ ≤ ρ) (ht : t ≤ σ - k⁻¹) :
    monotonicityIntervalTest k σ ρ t = 0 := by
  have hσ : 1 ≤ k * (σ - t) := by
    have h := mul_le_mul_of_nonneg_left ht hk.le
    rw [mul_sub, mul_inv_cancel₀ hk.ne'] at h
    nlinarith
  have hρ : 1 ≤ k * (ρ - t) := hσ.trans (by nlinarith)
  simp only [monotonicityIntervalTest, Real.smoothTransition.one_of_one_le hσ,
    Real.smoothTransition.one_of_one_le hρ, sub_self]

lemma monotonicityIntervalTest_eq_zero_right {k σ ρ t : ℝ}
    (hk : 0 ≤ k) (hσρ : σ ≤ ρ) (ht : ρ ≤ t) :
    monotonicityIntervalTest k σ ρ t = 0 := by
  have hσ : k * (σ - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith)
  have hρ : k * (ρ - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith)
  simp only [monotonicityIntervalTest, Real.smoothTransition.zero_of_nonpos hσ,
    Real.smoothTransition.zero_of_nonpos hρ, sub_self]

lemma tsupport_monotonicityIntervalTest_subset {k σ ρ : ℝ}
    (hk : 0 < k) (hσρ : σ ≤ ρ) :
    tsupport (monotonicityIntervalTest k σ ρ) ⊆ Icc (σ - k⁻¹) ρ := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn | hn
  · exact ht (monotonicityIntervalTest_eq_zero_left hk hσρ hn.le)
  · exact ht (monotonicityIntervalTest_eq_zero_right hk.le hσρ hn.le)

lemma hasCompactSupport_monotonicityIntervalTest {k σ ρ : ℝ}
    (hk : 0 < k) (hσρ : σ ≤ ρ) :
    HasCompactSupport (monotonicityIntervalTest k σ ρ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_monotonicityIntervalTest_subset hk hσρ)

lemma deriv_monotonicityIntervalTest (k σ ρ t : ℝ) :
    deriv (monotonicityIntervalTest k σ ρ) t =
      smoothSuperlevelKernel k σ t - smoothSuperlevelKernel k ρ t := by
  have hd (a : ℝ) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
      (k * (a - t))).hasDerivAt.comp t (((hasDerivAt_id t).const_sub a).const_mul k)
  have h := ((hd ρ).sub (hd σ)).deriv
  change deriv (monotonicityIntervalTest k σ ρ) t = _ at h
  rw [h]
  simp only [smoothSuperlevelKernel]
  ring

lemma integrable_smoothSuperlevelKernel {k : ℝ} (hk : 0 < k) (a : ℝ) :
    Integrable (smoothSuperlevelKernel k a) := by
  have hd : Integrable (deriv Real.smoothTransition) :=
    continuous_deriv_smoothTransition.integrable_of_hasCompactSupport
      hasCompactSupport_deriv_smoothTransition
  exact ((hd.comp_mul_left' hk.ne').comp_sub_left a).const_mul k

lemma integral_smoothSuperlevelKernel {k : ℝ} (hk : 0 < k) (a : ℝ) :
    (∫ t : ℝ, smoothSuperlevelKernel k a t) = 1 := by
  change (∫ t : ℝ, k * deriv Real.smoothTransition (k * (a - t))) = 1
  rw [integral_const_mul, integral_sub_left_eq_self
    (fun t => deriv Real.smoothTransition (k * t)) volume a,
    Measure.integral_comp_mul_left, integral_deriv_smoothTransition]
  simp [abs_of_pos (inv_pos.mpr hk), smul_eq_mul, hk.ne']

lemma support_smoothSuperlevelKernel_subset {k : ℝ} (hk : 0 < k) (a : ℝ) :
    Function.support (smoothSuperlevelKernel k a) ⊆ Icc (a - k⁻¹) a := by
  intro t ht
  have hder : deriv Real.smoothTransition (k * (a - t)) ≠ 0 :=
    fun h => ht (by simp [smoothSuperlevelKernel, h])
  have hs := tsupport_deriv_smoothTransition_subset (subset_tsupport _ hder)
  have hl := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hk.le)
  have hright := nonneg_of_mul_nonneg_right hs.1 hk
  simp only [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, mul_one] at hl
  exact ⟨by linarith, by linarith⟩

lemma tendsto_monotonicityIntervalTest (σ ρ t : ℝ) (hσρ : σ ≤ ρ) :
    Tendsto (fun j : ℕ => monotonicityIntervalTest ((j : ℝ) + 1) σ ρ t) atTop
      (𝓝 ((Ico σ ρ).indicator (fun _ => (1 : ℝ)) t)) := by
  have h := (tendsto_smoothTransition_nat_mul_sub ρ t).sub
    (tendsto_smoothTransition_nat_mul_sub σ t)
  change Tendsto _ _ (𝓝 ((if t < ρ then 1 else 0) - (if t < σ then 1 else 0))) at h
  have he : (Ico σ ρ).indicator (fun _ => (1 : ℝ)) t =
      (if t < ρ then 1 else 0) - (if t < σ then 1 else 0) := by
    by_cases hσ : t < σ
    · have hρ := hσ.trans_le hσρ
      simp [Set.indicator, hσ, hρ, not_le_of_gt hσ]
    · have hσ' : σ ≤ t := le_of_not_gt hσ
      by_cases hρ : t < ρ <;> simp [Set.indicator, hσ, hσ', hρ]
  simpa only [monotonicityIntervalTest, he] using h

/-- Probability kernels supported in shrinking left intervals recover the
left-continuous representative, including at atoms of a radial measure. -/
lemma tendsto_integral_left_probability_kernel {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousWithinAt f (Iic a) a) (κ : ℕ → ℝ → ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hk : ∀ j t, 0 ≤ κ j t) (hki : ∀ j, Integrable (κ j))
    (hkm : ∀ j, (∫ t : ℝ, κ j t) = 1)
    (hks : ∀ j, Function.support (κ j) ⊆ Icc (a - δ j) a)
    (hfi : ∀ᶠ j in atTop, Integrable (fun t => κ j t * f t)) :
    Tendsto (fun j => ∫ t : ℝ, κ j t * f t) atTop (𝓝 (f a)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf' : Tendsto f (𝓝[≤] a) (𝓝 (f a)) := hf
  rw [Metric.tendsto_nhdsWithin_nhds] at hf'
  obtain ⟨η, hη, hb⟩ := hf' (ε / 2) (half_pos hε)
  filter_upwards [hδ.eventually (eventually_lt_nhds hη), hfi] with j hj hji
  have hi : Integrable (fun t => κ j t * (f t - f a)) := by
    simpa only [mul_sub, Pi.sub_apply] using! hji.sub ((hki j).mul_const (f a))
  have heq : (∫ t : ℝ, κ j t * f t) - f a =
      ∫ t : ℝ, κ j t * (f t - f a) := by
    simp_rw [mul_sub]
    rw [integral_sub hji ((hki j).mul_const _), integral_mul_const, hkm j, one_mul]
  have hbound (t : ℝ) : ‖κ j t * (f t - f a)‖ ≤ κ j t * (ε / 2) := by
    by_cases ht : κ j t = 0
    · simp [ht]
    · have hs := hks j ht
      have hd : dist t a < η := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
        linarith [hs.1]
      rw [norm_mul, Real.norm_of_nonneg (hk j t)]
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (hb hs.2 hd).le)
        (hk j t)
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ∫ t : ℝ, ‖κ j t * (f t - f a)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, κ j t * (ε / 2) := integral_mono hi.norm ((hki j).mul_const _) hbound
    _ = ε / 2 := by rw [integral_mul_const, hkm j, one_mul]
    _ < ε := by linarith

lemma tendsto_integral_smoothSuperlevelKernel_left {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousWithinAt f (Iic a) a)
    (hi : ∀ᶠ j : ℕ in atTop,
      Integrable (fun t => smoothSuperlevelKernel ((j : ℝ) + 1) a t * f t)) :
    Tendsto (fun j : ℕ => ∫ t : ℝ, smoothSuperlevelKernel ((j : ℝ) + 1) a t * f t)
      atTop (𝓝 (f a)) := by
  apply tendsto_integral_left_probability_kernel hf
    (fun j => smoothSuperlevelKernel ((j : ℝ) + 1) a) (fun j => ((j : ℝ) + 1)⁻¹)
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    (fun j t => smoothSuperlevelKernel_nonneg (by positivity) a t)
    (fun j => integrable_smoothSuperlevelKernel (by positivity) a)
    (fun j => integral_smoothSuperlevelKernel (by positivity) a)
    (fun j => support_smoothSuperlevelKernel_subset (by positivity) a) hi

lemma continuous_smoothSuperlevelKernel (k a : ℝ) :
    Continuous (smoothSuperlevelKernel k a) :=
  (continuous_deriv_smoothTransition.comp
    (continuous_const.mul (continuous_const.sub continuous_id))).const_mul k

lemma tsupport_smoothSuperlevelKernel_subset {k : ℝ} (hk : 0 < k) (a : ℝ) :
    tsupport (smoothSuperlevelKernel k a) ⊆ Icc (a - k⁻¹) a :=
  closure_minimal (support_smoothSuperlevelKernel_subset hk a) isClosed_Icc

lemma hasCompactSupport_smoothSuperlevelKernel {k : ℝ} (hk : 0 < k) (a : ℝ) :
    HasCompactSupport (smoothSuperlevelKernel k a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smoothSuperlevelKernel_subset hk a)

lemma integrable_real_compact_factor_on_open {f ζ : ℝ → ℝ} {U : Set ℝ}
    (hf : LocallyIntegrableOn f U) (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ U) : Integrable (fun t => ζ t * f t) := by
  have hi := (hf.integrableOn_compact_subset hsζ hcζ).mul_continuousOn hζ.continuousOn hcζ
  have hi' : IntegrableOn (fun t => ζ t * f t) (tsupport ζ) := by
    simpa only [mul_comm] using hi
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi'
  intro t ht
  by_contra hn
  exact ht (by change ζ t * f t = 0; rw [image_eq_zero_of_notMem_tsupport hn, zero_mul])

lemma tendsto_integral_monotonicityIntervalTest (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] {σ ρ : ℝ} (hσρ : σ ≤ ρ) :
    Tendsto (fun j : ℕ => ∫ t : ℝ, monotonicityIntervalTest ((j : ℝ) + 1) σ ρ t ∂μ)
      atTop (𝓝 (μ.real (Ico σ ρ))) := by
  let K := Icc (σ - 1) ρ
  have hK : IsCompact K := isCompact_Icc
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hb (j : ℕ) (t : ℝ) : ‖monotonicityIntervalTest ((j : ℝ) + 1) σ ρ t‖ ≤
      K.indicator (fun _ => (1 : ℝ)) t := by
    by_cases ht : t ∈ K
    · rw [indicator_of_mem ht, Real.norm_of_nonneg
        (monotonicityIntervalTest_nonneg (by positivity) hσρ t)]
      exact monotonicityIntervalTest_le_one _ _ _ _
    · rw [indicator_of_notMem ht]
      have hz : monotonicityIntervalTest ((j : ℝ) + 1) σ ρ t = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have hs' := tsupport_monotonicityIntervalTest_subset (by positivity :
          0 < (j : ℝ) + 1) hσρ hs
        have hinv : ((j : ℝ) + 1)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]
          linarith [show 0 ≤ (j : ℝ) from Nat.cast_nonneg j]
        exact ht ⟨by linarith [hs'.1], hs'.2⟩
      simp [hz]
  have h := tendsto_integral_of_dominated_convergence
    (K.indicator (fun _ => (1 : ℝ)))
    (fun j => (contDiff_monotonicityIntervalTest _ _ _).continuous.aestronglyMeasurable) hi
    (fun j => Eventually.of_forall (hb j))
    (Eventually.of_forall fun t => tendsto_monotonicityIntervalTest σ ρ t hσρ)
  simpa only [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one]
    using h

/-- The weak radial inequality implies the exact half-open annular estimate.
No cumulative integral from radius zero occurs in either hypothesis or conclusion. -/
theorem interval_mass_le_sub_of_weak_derivative
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] {f : ℝ → ℝ} {a b σ ρ : ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (haσ : a < σ) (hσρ : σ ≤ ρ) (hρb : ρ < b)
    (hσ : ContinuousWithinAt f (Iic σ) σ) (hρ : ContinuousWithinAt f (Iic ρ) ρ)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∀ t, 0 ≤ φ t) →
        (∫ t, φ t ∂μ) ≤ -(∫ t : ℝ, f t * deriv φ t)) :
    μ.real (Ico σ ρ) ≤ f ρ - f σ := by
  have hδ : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ j : ℕ in atTop, a < σ - ((j : ℝ) + 1)⁻¹ := by
    filter_upwards [hδ.eventually (eventually_lt_nhds (sub_pos.mpr haσ))] with j hj
    linarith
  have hki (c : ℝ) (hσc : σ ≤ c) (hcρ : c ≤ ρ) :
      ∀ᶠ j : ℕ in atTop,
        Integrable (fun t => smoothSuperlevelKernel ((j : ℝ) + 1) c t * f t) := by
    filter_upwards [hsmall] with j hj
    apply integrable_real_compact_factor_on_open hf (continuous_smoothSuperlevelKernel _ _)
      (hasCompactSupport_smoothSuperlevelKernel (by positivity) _)
    intro t ht
    have hh := tsupport_smoothSuperlevelKernel_subset (by positivity : 0 < (j : ℝ) + 1) c ht
    exact ⟨by linarith [hh.1], hh.2.trans_lt (hcρ.trans_lt hρb)⟩
  have hiσ := hki σ le_rfl hσρ
  have hiρ := hki ρ hσρ le_rfl
  have he : ∀ᶠ j : ℕ in atTop,
      (∫ t, monotonicityIntervalTest ((j : ℝ) + 1) σ ρ t ∂μ) ≤
        (∫ t : ℝ, smoothSuperlevelKernel ((j : ℝ) + 1) ρ t * f t) -
          ∫ t : ℝ, smoothSuperlevelKernel ((j : ℝ) + 1) σ t * f t := by
    filter_upwards [hsmall, hiσ, hiρ] with j hj hjσ hjρ
    have hs : tsupport (monotonicityIntervalTest ((j : ℝ) + 1) σ ρ) ⊆ Ioo a b := by
      intro t ht
      have hh := tsupport_monotonicityIntervalTest_subset (by positivity :
        0 < (j : ℝ) + 1) hσρ ht
      exact ⟨hj.trans_le hh.1, hh.2.trans_lt hρb⟩
    have h := hweak _ ((contDiff_monotonicityIntervalTest _ _ _).of_le (by simp))
      (hasCompactSupport_monotonicityIntervalTest (by positivity) hσρ) hs
      (monotonicityIntervalTest_nonneg (by positivity) hσρ)
    have hid : (∫ t : ℝ, f t * deriv (monotonicityIntervalTest ((j : ℝ) + 1) σ ρ) t) =
        (∫ t : ℝ, smoothSuperlevelKernel ((j : ℝ) + 1) σ t * f t) -
          ∫ t : ℝ, smoothSuperlevelKernel ((j : ℝ) + 1) ρ t * f t := by
      simp_rw [deriv_monotonicityIntervalTest, mul_sub, mul_comm (f _)]
      exact integral_sub hjσ hjρ
    rw [hid] at h
    linarith
  exact le_of_tendsto_of_tendsto (tendsto_integral_monotonicityIntervalTest μ hσρ)
    ((tendsto_integral_smoothSuperlevelKernel_left hρ hiρ).sub
      (tendsto_integral_smoothSuperlevelKernel_left hσ hiσ)) he

end LiquidDrop
