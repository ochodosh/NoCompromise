module

public import NoCompromise.Sobolev.H1Mollification
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

/-!
# Strong translation and mollifier approximation in L²

Whole-space translations act continuously in Lᵖ for finite `p ≥ 1`. Probability
bump convolutions approximate both an H¹ function and its weak gradient in L².
No Sobolev density or extension result is used as a premise.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped NNReal ENNReal Topology Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Translation errors depend continuously on the translation parameter in every finite Lᵖ. -/
theorem continuous_lpNorm_translate_sub {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f p volume) :
    Continuous (fun y => lpNorm (fun x => f (x - y) - f x) p volume) := by
  let g (y : EuclideanSpace ℝ (Fin n)) :
      C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry _ (by
    change Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => q.2 - q.1)
    fun_prop)
  have hm (y) : MeasurePreserving (g y) volume volume := measurePreserving_sub_right volume y
  have ht := (continuous_const (y := hf.toLp f)).compMeasurePreservingLp hg hm hp
  have hn := (ht.sub (continuous_const (y := hf.toLp f))).norm
  convert hn using 1
  ext y
  have hd : MemLp (fun x => f (x - y) - f x) p volume :=
    (hf.comp_measurePreserving (measurePreserving_sub_right volume y)).sub hf
  rw [← toReal_eLpNorm, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (g y) (hm y) (hf.toLp f))
      (hf.toLp f), Lp.coeFn_compMeasurePreserving (hf.toLp f) (hm y),
      MemLp.coeFn_toLp hf, (hm y).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hf)]
    with x hx1 hx2 hx3 hx4
  exact (hx1.trans (congrArg₂ (· - ·) (hx2.trans hx4) hx3)).symm

/-- Strong translation continuity, stated in the extended Lᵖ norm. -/
theorem tendsto_eLpNorm_translate_sub_zero {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f p volume) :
    Tendsto (fun y => eLpNorm (fun x => f (x - y) - f x) p volume) (𝓝 0) (𝓝 0) := by
  have h := (ENNReal.continuous_ofReal.comp
    (continuous_lpNorm_translate_sub hp hf)).tendsto (0 : EuclideanSpace ℝ (Fin n))
  have heq (y : EuclideanSpace ℝ (Fin n)) :
      ENNReal.ofReal (lpNorm (fun x => f (x - y) - f x) p volume) =
        eLpNorm (fun x => f (x - y) - f x) p volume :=
    ofReal_lpNorm ((hf.comp_measurePreserving (measurePreserving_sub_right volume y)).sub hf)
  have hz : lpNorm (fun _ : EuclideanSpace ℝ (Fin n) => (0 : F)) p volume = 0 :=
    lpNorm_zero p volume
  simpa only [Function.comp_def, heq, sub_zero, sub_self, lpNorm_zero,
    hz, eLpNorm_zero, ENNReal.ofReal_zero] using h

/-- The square of the ordinary L² norm is the integral of the squared pointwise norm. -/
lemma lpNorm_two_sq_eq_integral_norm_sq {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- The squared L² translation error is a continuous scalar function. -/
theorem continuous_integral_norm_sq_translate_sub {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume) :
    Continuous (fun y => ∫ x, ‖f (x - y) - f x‖ ^ 2) := by
  have h := (continuous_lpNorm_translate_sub (by norm_num) hf).pow 2
  convert h using 1
  ext y
  exact (lpNorm_two_sq_eq_integral_norm_sq
    ((hf.comp_measurePreserving (measurePreserving_sub_right volume y)).sub hf)).symm

/-- Fubini integrability of the probability-weighted squared translation error. -/
lemma integrable_kernel_translation_error_sq {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {k : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n) → F} (hik : Integrable k)
    (hk0 : ∀ x, 0 ≤ k x) (hf : MemLp f 2 volume) :
    Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      k q.2 * ‖f (q.1 - q.2) - f q.1‖ ^ 2) (volume.prod volume) := by
  have hi2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hiA : Integrable
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        k q.2 * ‖f (q.1 - q.2)‖ ^ 2) (volume.prod volume) :=
    hik.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hi2
  have hiB : Integrable
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        k q.2 * ‖f q.1‖ ^ 2) (volume.prod volume) := (hik.mul_prod hi2).swap
  have htrans : AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (q.1 - q.2))
      (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  apply ((hiA.add hiB).const_mul 2).mono'
    (hik.1.comp_snd.mul ((htrans.sub hf.aestronglyMeasurable.comp_fst).norm.pow 2))
  exact Eventually.of_forall fun q => by
    change ‖k q.2 * ‖f (q.1 - q.2) - f q.1‖ ^ 2‖ ≤
      2 * (k q.2 * ‖f (q.1 - q.2)‖ ^ 2 + k q.2 * ‖f q.1‖ ^ 2)
    rw [Real.norm_of_nonneg (mul_nonneg (hk0 _) (sq_nonneg _))]
    have hn : ‖f (q.1 - q.2) - f q.1‖ ^ 2 ≤
        2 * ‖f (q.1 - q.2)‖ ^ 2 + 2 * ‖f q.1‖ ^ 2 := by
      nlinarith [norm_sub_le (f (q.1 - q.2)) (f q.1), norm_nonneg (f (q.1 - q.2)),
        norm_nonneg (f q.1), norm_nonneg (f (q.1 - q.2) - f q.1),
        sq_nonneg (‖f (q.1 - q.2)‖ - ‖f q.1‖)]
    have h := mul_le_mul_of_nonneg_left hn (hk0 q.2)
    nlinarith

/-- Jensen and Fubini bound the squared L² convolution error by the kernel average
of the squared L² translation errors. -/
theorem integral_norm_sq_convolution_sub_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Continuous k) (hck : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x)
    (hk1 : ∫ x, k x = 1) (hf : MemLp f 2 volume) :
    (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ^ 2) ≤
      ∫ y, k y * ∫ x, ‖f (x - y) - f x‖ ^ 2 := by
  have hik : Integrable k := hk.integrable_of_hasCompactSupport hck
  have hmc := (memLp_two_convolution_probability_kernel hk hck hk0 hk1 hf).1
  have hmd := hmc.sub hf
  have hdiff := integrable_kernel_translation_error_sq hik hk0 hf
  have hlocal := hf.locallyIntegrable (by norm_num)
  have hconv (x : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => k y • f (x - y)) :=
    hck.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hlocal x
  have hi (x : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => k y • (f (x - y) - f x)) := by
    simp only [smul_sub]
    exact (hconv x).sub (hik.smul_const (f x))
  have hId (x : EuclideanSpace ℝ (Fin n)) :
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x =
        ∫ y, k y • (f (x - y) - f x) := by
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_sub]
    rw [integral_sub (hconv x) (hik.smul_const (f x)), integral_smul_const, hk1, one_smul]
  calc
    _ ≤ ∫ x, ∫ y, k y * ‖f (x - y) - f x‖ ^ 2 := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hmd.aestronglyMeasurable).mp hmd)
        hdiff.integral_prod_left
      filter_upwards [hdiff.prod_right_ae] with x hx
      change ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ^ 2 ≤ _
      rw [hId]
      exact norm_integral_smul_sq_le_of_probability_kernel hk.measurable hik hk0 hk1 (hi x) hx
    _ = ∫ y, ∫ x, k y * ‖f (x - y) - f x‖ ^ 2 := integral_integral_swap hdiff
    _ = _ := by simp_rw [integral_const_mul]

/-- A compactly supported probability kernel inherits a bound on nearby squared
translation errors. -/
lemma integral_norm_sq_convolution_sub_le_of_support {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Continuous k) (hck : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x)
    (hk1 : ∫ x, k x = 1) (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : ∀ y ∈ Function.support k, (∫ x, ‖f (x - y) - f x‖ ^ 2) ≤ ε) :
    (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ^ 2) ≤ ε := by
  calc
    _ ≤ ∫ y, k y * ∫ x, ‖f (x - y) - f x‖ ^ 2 :=
      integral_norm_sq_convolution_sub_le hk hck hk0 hk1 hf
    _ ≤ ∫ y, k y * ε := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun y => mul_nonneg (hk0 y) (integral_nonneg fun _ => sq_nonneg _))
        ((hk.integrable_of_hasCompactSupport hck).mul_const ε)
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ Function.support k
        · exact mul_le_mul_of_nonneg_left (hε y hy) (hk0 y)
        · change k y * _ ≤ k y * ε
          rw [Function.notMem_support.mp hy, zero_mul, zero_mul]
    _ = ε := by rw [integral_mul_const, hk1, one_mul]

/-- Shrinking normalized bump convolution converges in the integral of the squared norm
for every whole-space L² function, including vector-valued functions. -/
theorem tendsto_integral_norm_sq_bump_convolution_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j =>
      ∫ x, ‖((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ^ 2)
      l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp
    (continuous_integral_norm_sq_translate_sub hf).continuousAt (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ j in l, (φ j).rOut < δ := (tendsto_order.mp hφ).2 δ hδ
  filter_upwards [hsmall] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  apply lt_of_le_of_lt (integral_norm_sq_convolution_sub_le_of_support
    (φ j).continuous_normed (φ j).hasCompactSupport_normed (φ j).nonneg_normed
    (φ j).integral_normed hf ?_) (half_lt_self hε)
  intro y hy
  rw [(φ j).support_normed_eq] at hy
  have hyδ : dist y 0 < δ := (mem_ball.mp hy).trans hj
  have hyb := hb hyδ
  simp only [sub_zero, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    integral_zero, Real.dist_eq] at hyb
  exact (le_abs_self _).trans hyb.le

/-- The ordinary L² norm is the square root of the squared-norm integral. -/
lemma lpNorm_two_eq_sqrt_integral_norm_sq {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [← lpNorm_two_sq_eq_integral_norm_sq hf, Real.sqrt_sq_eq_abs,
    abs_of_nonneg lpNorm_nonneg]

/-- Strong L² approximation by normalized shrinking bump kernels, in ordinary norm. -/
theorem tendsto_lpNorm_bump_convolution_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => lpNorm
      (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x) 2 volume)
      l (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_integral_norm_sq_bump_convolution_sub hf hφ)
  have heq (j : ι) : lpNorm
      (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x) 2 volume =
      Real.sqrt (∫ x, ‖((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ^ 2) :=
    lpNorm_two_eq_sqrt_integral_norm_sq
      ((memLp_two_convolution_probability_kernel (φ j).continuous_normed
        (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf).1.sub hf)
  simpa only [Function.comp_def, ← heq, Real.sqrt_zero] using h

/-- Strong L² approximation by normalized shrinking bump kernels, in extended norm. -/
theorem tendsto_eLpNorm_bump_convolution_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : MemLp f 2 volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x) 2 volume)
      l (𝓝 0) := by
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp
    (tendsto_lpNorm_bump_convolution_sub hf hφ)
  have heq (j : ι) : ENNReal.ofReal (lpNorm
      (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x) 2 volume) =
      eLpNorm (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x)
        2 volume :=
    ofReal_lpNorm ((memLp_two_convolution_probability_kernel (φ j).continuous_normed
      (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf).1.sub hf)
  simpa only [Function.comp_def, heq, ENNReal.ofReal_zero] using h

/-- Whole-space H¹ bump approximations converge strongly in L² both as functions
and through their classical gradients to the original weak gradient. -/
theorem HasH1GradientOn.tendsto_bump_convolution {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      (fun x => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x) 2 volume)
        l (𝓝 0) ∧
      Tendsto (fun j => eLpNorm
        (fun x => gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - G x)
        2 volume) l (𝓝 0) := by
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  refine ⟨tendsto_eLpNorm_bump_convolution_sub hmf hφ, ?_⟩
  have hgrad (j : ι) (x : EuclideanSpace ℝ (Fin n)) :=
    (hf.bump_convolution (φ j)).2.1 x
  simp_rw [hgrad]
  exact tendsto_eLpNorm_bump_convolution_sub hmG hφ

end LiquidDrop
