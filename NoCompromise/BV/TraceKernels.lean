module

public import NoCompromise.BV.TraceApproximation
public import NoCompromise.BV.CoareaSmooth

@[expose] public section

/-!
# One-sided kernel recovery of BV traces

Probability kernels supported in a shrinking one-sided slab recover the actual
BV trace. The proof uses the established strong normal mean approximation.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_normal_kernel_error_le {f k : ℝ → ℝ} (hf : Integrable f volume)
    (hk : Integrable k volume) {a r C T : ℝ}
    (hs : Function.support k ⊆ Icc (a - r) a) (hm : (∫ t, k t) = 1)
    (hb : ∀ t, |k t| ≤ C * r⁻¹) :
    |(∫ t, k t * f t) - T| ≤ C * (r⁻¹ * ∫ t in Ioo (a - r) a, |f t - T|) := by
  have hkf : Integrable (fun t => k t * f t) volume :=
    hf.bdd_mul hk.aestronglyMeasurable (ae_of_all _ fun t => by
      simpa only [Real.norm_eq_abs] using hb t)
  have hke : Integrable (fun t => k t * (f t - T)) volume := by
    simpa only [mul_sub, Pi.sub_def] using! hkf.sub (hk.mul_const T)
  have he : (∫ t, k t * f t) - T = ∫ t, k t * (f t - T) := by
    simp only [mul_sub]
    rw [integral_sub hkf (hk.mul_const T), integral_mul_const, hm, one_mul]
  rw [he]
  calc
    _ ≤ ∫ t, |k t * (f t - T)| := abs_integral_le_integral_abs
    _ = ∫ t in Icc (a - r) a, |k t * (f t - T)| := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hz : k t = 0 := by
        by_contra hn
        exact ht (hs hn)
      rw [hz, zero_mul, abs_zero]
    _ ≤ ∫ t in Icc (a - r) a, C * r⁻¹ * |f t - T| := by
      have hi : IntegrableOn (fun t => |f t - T|) (Icc (a - r) a) volume := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using!
          (hf.integrableOn.sub (integrableOn_const isCompact_Icc.measure_ne_top)).norm
      apply setIntegral_mono_on hke.abs.integrableOn (hi.const_mul _) measurableSet_Icc
      intro t _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
    _ = _ := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioo]
      ring

lemma IsBVOn.integrable_flatBVMeanErrors {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Integrable (flatBVLeftMeanError f a r) volume ∧
      Integrable (flatBVRightMeanError f a r) volume := by
  have hb : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      flatBVLeftMeanError f a r x ≤ 2 * (variation (lineSlice f x) univ).toReal ∧
      flatBVRightMeanError f a r x ≤ 2 * (variation (lineSlice f x) univ).toReal := by
    filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1] with x hx
    have hx' : IsBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hx
    exact hx'.mean_abs_sub_traces_le a hr hr1
  have hfin : (∫⁻ x : EuclideanSpace ℝ (Fin n), 2 * variation (lineSlice f x) univ) < ∞ := by
    rw [lintegral_const_mul' _ _ (by norm_num)]
    calc
      _ ≤ 2 * variation f univ := by
        gcongr
        exact hf.ae_lineSlice_and_lintegral_variation_le.2
      _ < ∞ := ENNReal.mul_lt_top (by norm_num) hf.2
  have hgeneral {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : AEStronglyMeasurable g volume)
      (hn : ∀ x, 0 ≤ g x)
      (hle : ∀ᵐ x, g x ≤ 2 * (variation (lineSlice f x) univ).toReal) : Integrable g volume := by
    refine ⟨hg, ?_⟩
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono_ae
    filter_upwards [hle] with x hx
    rw [Real.enorm_eq_ofReal (hn x)]
    apply (ENNReal.ofReal_le_ofReal hx).trans
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    gcongr
    exact ENNReal.ofReal_toReal_le
  constructor
  · apply hgeneral
      (aestronglyMeasurable_normal_mean_error (integrableOn_univ.mp hf.1).aestronglyMeasurable
        (hf.aestronglyMeasurable_flatBVLeftTrace a) _ r)
      (fun x => mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => abs_nonneg _))
    exact hb.mono fun _ hx => hx.1
  · apply hgeneral
      (aestronglyMeasurable_normal_mean_error (integrableOn_univ.mp hf.1).aestronglyMeasurable
        (hf.aestronglyMeasurable_flatBVRightTrace a) _ r)
      (fun x => mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => abs_nonneg _))
    exact hb.mono fun _ hx => hx.2

/-- A bounded normal kernel recovers the integrated lower trace up to the actual mean error. -/
lemma IsBVOn.integral_normal_kernel_error_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ)
    {k : ℝ → ℝ} (hk : Integrable k volume) {a r C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : Function.support k ⊆ Icc (a - r) a) (hm : (∫ t, k t) = 1)
    (hb : ∀ t, |k t| ≤ C * r⁻¹) :
    |(∫ z, k (z (Fin.last n)) * f z) - ∫ x, flatBVLeftTrace f a x| ≤
      C * ∫ x, flatBVLeftMeanError f a r x := by
  have hi := integrableOn_univ.mp hf.1
  have hp := realLineCoordinates_measurePreserving n
  have hig := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hik : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => k p.2)
      (volume.prod volume) := hk.aestronglyMeasurable.aemeasurable.comp_snd.aestronglyMeasurable
  have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      k p.2 * f (graphAppendN p.1 p.2)) (volume.prod volume) :=
    hig.bdd_mul hik (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using hb p.2)
  have hJ : (∫ z, k (z (Fin.last n)) * f z) =
      ∫ x : EuclideanSpace ℝ (Fin n), ∫ t : ℝ, k t * f (graphAppendN x t) := by
    have he := hp.integral_comp (realLineCoordinates n).measurableEmbedding
      (fun z => k (z (Fin.last n)) * f z)
    simp only [realLineCoordinates_apply, graphAppendN_last] at he
    rw [← he]
    exact integral_prod _ hprod
  have hiT := (hf.integrable_flatBVTraces a).1
  have hiE := (hf.integrable_flatBVMeanErrors a hr hr1).1
  have hline : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      |(∫ t : ℝ, k t * f (graphAppendN x t)) - flatBVLeftTrace f a x| ≤
        C * flatBVLeftMeanError f a r x := by
    filter_upwards [hig.prod_right_ae] with x hx
    exact LiquidDrop.integral_normal_kernel_error_le hx hk hs hm hb
  rw [hJ, ← integral_sub hprod.integral_prod_left hiT]
  calc
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n),
        |(∫ t : ℝ, k t * f (graphAppendN x t)) - flatBVLeftTrace f a x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, C * flatBVLeftMeanError f a r x :=
      integral_mono_ae (hprod.integral_prod_left.sub hiT).abs (hiE.const_mul C) hline
    _ = _ := integral_const_mul _ _

/-- One-sided mass-one kernels converge to the integral of the constructed BV trace. -/
theorem IsBVOn.tendsto_integral_normal_kernel {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {k : ℕ → ℝ → ℝ} (hk : ∀ j, Integrable (k j) volume)
    (hs : ∀ j, Function.support (k j) ⊆ Icc (a - r j) a)
    (hm : ∀ j, (∫ t, k j t) = 1) {C : ℝ}
    (hb : ∀ j t, |k j t| ≤ C * (r j)⁻¹) :
    Tendsto (fun j => ∫ z, k j (z (Fin.last n)) * f z) atTop
      (𝓝 (∫ x, flatBVLeftTrace f a x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hr⟩
  have hlim : Tendsto (fun j => C * ∫ x, flatBVLeftMeanError f a (r j) x) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((hf.tendsto_flatBVMeanError_integral a).1.comp hr').const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hlim
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
  exact hf.integral_normal_kernel_error_le (hk j) (hr j) hj.le (hs j) (hm j) (hb j)

lemma integrable_smoothSuperlevelKernel {k : ℝ} (hk : 0 < k) (a : ℝ) :
    Integrable (smoothSuperlevelKernel k a) volume := by
  have hd : Integrable (deriv Real.smoothTransition) volume :=
    continuous_deriv_smoothTransition.integrable_of_hasCompactSupport
    hasCompactSupport_deriv_smoothTransition
  exact ((hd.comp_mul_left' hk.ne').comp_sub_left a).const_mul k

lemma integral_smoothSuperlevelKernel {k : ℝ} (hk : 0 < k) (a : ℝ) :
    (∫ t, smoothSuperlevelKernel k a t) = 1 := by
  have he := lintegral_smoothSuperlevelKernel hk a
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_smoothSuperlevelKernel hk a)
    (ae_of_all _ fun t => smoothSuperlevelKernel_nonneg hk.le a t)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal
    (integral_nonneg (fun t => smoothSuperlevelKernel_nonneg hk.le a t))] using ht

lemma support_smoothSuperlevelKernel_subset {k : ℝ} (hk : 0 < k) (a : ℝ) :
    Function.support (smoothSuperlevelKernel k a) ⊆ Icc (a - k⁻¹) a := by
  intro t ht
  have hd : deriv Real.smoothTransition (k * (a - t)) ≠ 0 := by
    intro hz
    exact ht (by simp only [smoothSuperlevelKernel, hz, mul_zero])
  have hs := tsupport_deriv_smoothTransition_subset (subset_closure hd)
  have h0 : 0 ≤ a - t := (mul_nonneg_iff_of_pos_left hk).mp hs.1
  have h1 : a - t ≤ k⁻¹ := by
    rw [← one_div, le_div_iff₀ hk]
    simpa only [mul_comm] using hs.2
  constructor <;> linarith

/-- The actual derivative kernel of the smooth one-sided cutoff recovers the lower trace. -/
theorem IsBVOn.tendsto_integral_smooth_normal_kernel {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    Tendsto (fun j : ℕ => ∫ z,
      smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * f z) atTop
      (𝓝 (∫ x, flatBVLeftTrace f a x)) := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_deriv_smoothTransition.isCompact_range
    continuous_deriv_smoothTransition).isBounded.exists_norm_le
  have hr : ∀ j : ℕ, 0 < ((j : ℝ) + 1)⁻¹ := fun _ => by positivity
  have ht : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply hf.tendsto_integral_normal_kernel a hr ht
    (fun j => integrable_smoothSuperlevelKernel (by positivity) a)
    (fun j => support_smoothSuperlevelKernel_subset (by positivity) a)
    (fun j => integral_smoothSuperlevelKernel (by positivity) a) (C := C)
  intro j t
  have hd : |deriv Real.smoothTransition (((j : ℝ) + 1) * (a - t))| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC _ (mem_range_self _)
  dsimp only [smoothSuperlevelKernel]
  rw [inv_inv, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
  calc
    _ ≤ ((j : ℝ) + 1) * C := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := mul_comm _ _

end LiquidDrop
