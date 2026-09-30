module

public import NoCompromise.Sobolev.PlanarGN

@[expose] public section

/-!
# Whole-space spatial H¹ to L⁶ estimate

The BV Sobolev inequality applied to fourth powers gives `‖f‖₆ ≤ 4 ‖G‖₂`.
Smooth mollifications are bounded by Cauchy–Schwarz, so the powers are integrable
before cancellation. Almost-everywhere approximation and Fatou give the full H¹ result.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The Lᵖ norm of an integer power, including infinite norms. -/
lemma eLpNorm_real_pow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (p : ℝ≥0∞) {m : ℕ} (hm : 0 < m) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f x ^ m) p μ = eLpNorm f (p * m) μ ^ m := by
  have h := eLpNorm_norm_rpow (p := p) (μ := μ) f hf (q := (m : ℝ)) (by exact_mod_cast hm)
  simp only [Real.rpow_natCast, ENNReal.ofReal_natCast, ENNReal.rpow_natCast] at h
  rw [← h]
  apply eLpNorm_congr_norm_ae (hf.pow m) (hf.norm.pow m)
  exact Eventually.of_forall fun x => by simp [norm_pow]

/-- A bounded L² function has an L² square and cube. -/
lemma memLp_sq_cube_of_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 volume) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    MemLp (fun x => f x ^ 2) 2 volume ∧ MemLp (fun x => f x ^ 3) 2 volume := by
  constructor
  · apply hf.of_le_mul (c := B) (hf.aestronglyMeasurable.pow 2)
    filter_upwards with x
    rw [Pi.pow_apply, norm_pow, pow_two]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  · apply hf.of_le_mul (c := B ^ 2) (hf.aestronglyMeasurable.pow 3)
    filter_upwards with x
    rw [Pi.pow_apply, norm_pow, pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (norm_nonneg _)

/-- Fourth-power gradients have the expected pointwise formula. -/
lemma gradient_pow_four {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) :
    gradient (fun x => f x ^ 4) = fun x => (4 : ℝ) • (f x ^ 3 • gradient f x) := by
  funext x
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_single,
    fderiv_fun_pow 4 (hf.differentiable one_ne_zero x)]
  simp [PiLp.smul_apply, gradient_apply_eq_fderiv_single, mul_assoc]

/-- Bounded smooth whole-space H¹ functions satisfy the spatial Sobolev estimate. -/
theorem lpNorm_six_le_of_contDiff_bound {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : ContDiff ℝ 1 f) (hf : MemLp f 2 volume)
    (hG : MemLp (gradient f) 2 volume) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    MemLp f 6 volume ∧ lpNorm f 6 volume ≤ 4 * lpNorm (gradient f) 2 volume := by
  obtain ⟨h2, h3⟩ := memLp_sq_cube_of_bound hf hb
  have h6 : MemLp f 6 volume := by
    have h := h3.eLpNorm_lt_top
    rw [eLpNorm_real_pow f 2 (by norm_num : 0 < 3) hf.aestronglyMeasurable] at h
    norm_num at h
    exact h
  have hi : Integrable (fun x => f x ^ 4) := by
    convert h2.integrable_mul h2 using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  have hiG : Integrable (fun x => f x ^ 3 • gradient f x) :=
    memLp_one_iff_integrable.mp (h3.smul hG : MemLp ((fun x => f x ^ 3) • gradient f) 1 volume)
  have hgrad : Integrable (gradient (fun x => f x ^ 4)) := by
    rw [gradient_pow_four hc]
    exact Integrable.smul (4 : ℝ) hiG
  have hgBound : (∫ x, ‖gradient (fun x => f x ^ 4) x‖) ≤
      4 * lpNorm (fun x => f x ^ 3) 2 volume * lpNorm (gradient f) 2 volume := by
    simp only [gradient_pow_four hc, norm_smul, Real.norm_ofNat]
    rw [integral_const_mul]
    simpa only [norm_smul, mul_assoc] using
      mul_le_mul_of_nonneg_left (integral_norm_smul_le_lpNorm_two_mul h3 hG)
        (show (0 : ℝ) ≤ 4 by norm_num)
  have hv := (variation_le_integral_norm_gradient (hc.pow 4) hgrad).trans
    (ENNReal.ofReal_le_ofReal hgBound)
  have hbv : IsBVOn (fun x => f x ^ 4) univ :=
    ⟨hi.integrableOn, hv.trans_lt ENNReal.ofReal_lt_top⟩
  have hs := (bv_sobolev_three hbv).trans hv
  rw [eLpNorm_real_pow f (3 / 2) (by norm_num : 0 < 4) hc.continuous.aestronglyMeasurable] at hs
  have harith : (3 / 2 : ℝ≥0∞) * 4 = 6 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    norm_num
  norm_num only [Nat.cast_ofNat] at hs
  rw [harith] at hs
  have hpow : lpNorm (fun x => f x ^ 3) 2 volume = lpNorm f 6 volume ^ 3 := by
    have h := congrArg ENNReal.toReal (eLpNorm_real_pow (μ := volume) f 2
      (by norm_num : 0 < 3) hf.aestronglyMeasurable)
    norm_num only [show (2 : ℝ≥0∞) * 3 = 6 by norm_num, ENNReal.toReal_pow] at h
    simpa only [toReal_eLpNorm, toReal_eLpNorm] using h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_pow, toReal_eLpNorm, ENNReal.toReal_ofReal
    (mul_nonneg (mul_nonneg (by norm_num) lpNorm_nonneg) lpNorm_nonneg), hpow] at hr
  refine ⟨h6, ?_⟩
  by_cases hz : lpNorm f 6 volume = 0
  · rw [hz]
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  · have hp : 0 < lpNorm f 6 volume := lt_of_le_of_ne lpNorm_nonneg (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ (pow_pos hp 3)).mp
    nlinarith only [hr]

/-- Cauchy–Schwarz bounds an L² convolution uniformly at every point. -/
lemma norm_convolution_le_lpNorm_two_mul {n : ℕ}
    {k f : EuclideanSpace ℝ (Fin n) → ℝ} (hk : MemLp k 2 volume)
    (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ≤
      lpNorm k 2 volume * lpNorm f 2 volume := by
  have ht : MemLp (fun y => f (x - y)) 2 volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have heq : lpNorm (fun y => f (x - y)) 2 volume = lpNorm f 2 volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    exact congrArg ENNReal.toReal
      (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (volume.measurePreserving_sub_left x))
  rw [convolution_def]
  apply (norm_integral_le_integral_norm _).trans
  simpa only [heq, ContinuousLinearMap.lsmul_apply] using
    integral_norm_smul_le_lpNorm_two_mul hk ht

/-- The quantitative spatial Sobolev estimate for arbitrary whole-space H¹ functions. -/
theorem HasH1GradientOn.eLpNorm_six_le {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G univ) :
    eLpNorm f 6 volume ≤ ENNReal.ofReal (4 * lpNorm G 2 volume) := by
  have hmf : MemLp f 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_gradient
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1),
      by positivity, half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let u (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hu (j : ℕ) : MemLp (u j) 2 volume := by
    simpa only [Measure.restrict_univ] using
      (hf.bump_convolution (φ j)).2.2.1.memLp_function
  have hgrad (j : ℕ) : MemLp (gradient (u j)) 2 volume := by
    have h := (hf.bump_convolution (φ j)).2.2.1.memLp_gradient
    simp only [Measure.restrict_univ] at h
    have heq : gradient (u j) = (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
      funext (hf.bump_convolution (φ j)).2.1
    rw [heq]
    exact h
  have huG (j : ℕ) : lpNorm (gradient (u j)) 2 volume ≤ lpNorm G 2 volume := by
    have heq : gradient (u j) = (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
      funext (hf.bump_convolution (φ j)).2.1
    have h := (hf.bump_convolution (φ j)).2.2.2.2
    rw [← heq] at h
    have h' := ENNReal.toReal_mono hmG.eLpNorm_ne_top h
    simpa only [toReal_eLpNorm, toReal_eLpNorm] using h'
  have hb (j : ℕ) : eLpNorm (u j) 6 volume ≤ ENNReal.ofReal (4 * lpNorm G 2 volume) := by
    have hk : MemLp ((φ j).normed volume) 2 volume :=
      (φ j).continuous_normed.memLp_of_hasCompactSupport (φ j).hasCompactSupport_normed
    obtain ⟨h6, h6b⟩ := lpNorm_six_le_of_contDiff_bound
      ((hf.bump_convolution (φ j)).1.of_le (by simp)) (hu j) (hgrad j)
      (norm_convolution_le_lpNorm_two_mul hk hmf)
    rw [← ofReal_lpNorm h6]
    apply ENNReal.ofReal_le_ofReal
    exact h6b.trans (mul_le_mul_of_nonneg_left (huG j) (by norm_num))
  have ht : Tendsto (fun j => eLpNorm (u j - f) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_sub hmf hφ
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht).exists_seq_tendsto_ae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => (hu (σ j)).aestronglyMeasurable) f
    hmf.aestronglyMeasurable hae (p := 6)
  exact hfatou.trans ((liminf_le_liminf (Eventually.of_forall fun j => hb (σ j))).trans_eq
    tendsto_const_nhds.liminf_eq)

/-- Every whole-space spatial H¹ function belongs to L⁶. -/
theorem HasH1GradientOn.memLp_six {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G univ) : MemLp f 6 volume := by
  exact hf.eLpNorm_six_le.trans_lt ENNReal.ofReal_lt_top

/-- Whole-space spatial Sobolev in ordinary norms, with constant four. -/
theorem HasH1GradientOn.lpNorm_six_le {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G univ) : lpNorm f 6 volume ≤ 4 * lpNorm G 2 volume := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hf.eLpNorm_six_le
  have hnonneg : 0 ≤ 4 * lpNorm G 2 volume := mul_nonneg (by norm_num) lpNorm_nonneg
  simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal hnonneg] using h

/-- Gradient-free membership form of the whole-space spatial embedding. -/
theorem IsH1On.memLp_six {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : IsH1On f univ) : MemLp f 6 volume := by
  obtain ⟨G, hG⟩ := hf
  exact hG.memLp_six

end LiquidDrop
