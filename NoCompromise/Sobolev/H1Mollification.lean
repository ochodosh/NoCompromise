module

public import NoCompromise.Sobolev.Hilbert
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-!
# Mollification of whole-space H¹ functions

A compact smooth convolution kernel commutes with the weak gradient. Positive
normalized kernels satisfy the L² contraction estimate by Jensen and Fubini.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A compact C¹ kernel commutes with a globally defined weak gradient, pointwise
as an identity for the classical gradient of the convolution. -/
theorem HasWeakGradientOn.gradient_convolution {n : ℕ}
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G univ) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x := by
  have hif := locallyIntegrableOn_univ.mp hf.locallyIntegrable_function
  have hiG := locallyIntegrableOn_univ.mp hf.locallyIntegrable_gradient
  let φ := fun y => k (x - y)
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hck.comp_homeomorph (Homeomorph.subLeft x)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiL := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hif (continuous_gradient_of_contDiff hk) x
  have hiR := hck.convolutionExists_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hiG hk.continuous x
  change Integrable (fun y => f y • gradient k (x - y)) at hiL
  change Integrable (fun y => k (x - y) • G y) at hiR
  rw [gradient_convolution_left hif hk hck x, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiL.eval_piLp, eval_integral_piLp hiR.eval_piLp]
  have h := hf.test_eq i φ hφ hcφ (subset_univ _)
  simp only [setIntegral_univ] at h
  have hderiv (y) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hderiv, mul_neg, integral_neg, neg_neg] at h
  simpa only [ContinuousLinearMap.lsmul_apply, PiLp.smul_apply, smul_eq_mul] using h

/-- Jensen's inequality for an explicitly normalized nonnegative scalar density. -/
lemma norm_integral_smul_sq_le_of_probability_kernel {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure α} {k : α → ℝ} {f : α → F}
    (hk : Measurable k) (hik : Integrable k μ) (hk0 : ∀ x, 0 ≤ k x)
    (hk1 : ∫ x, k x ∂μ = 1)
    (hif : Integrable (fun x => k x • f x) μ)
    (hi2 : Integrable (fun x => k x * ‖f x‖ ^ 2) μ) :
    ‖∫ x, k x • f x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖f x‖ ^ 2 ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (k x))
  have hν : ν univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hik (Eventually.of_forall hk0), hk1,
      ENNReal.ofReal_one]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (k x) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hifν : Integrable f ν := by
    apply (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (hk0 _)] using hif
  have hi2ν : Integrable (fun x => ‖f x‖ ^ 2) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul] using hi2
  have hconv : ConvexOn ℝ univ (fun y : F => ‖y‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have h := hconv.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hifν hi2ν
  rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal hfinite,
    integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal hfinite] at h
  simpa only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul] using h

/-- Young's L² contraction for a nonnegative compact continuous probability kernel.
The input need only belong to L²; no global L¹ or compact-support hypothesis is used. -/
theorem memLp_two_convolution_probability_kernel {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Continuous k) (hck : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x)
    (hk1 : ∫ x, k x = 1) (hf : MemLp f 2 volume) :
    MemLp (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume ∧
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume ≤ eLpNorm f 2 volume ∧
      (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hik : Integrable k := hk.integrable_of_hasCompactSupport hck
  have hiloc := hf.locallyIntegrable (by norm_num)
  have hi2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hc := hck.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hiloc
  have hbar := hik.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hi2
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2 ≤
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖ ^ 2)) x := by
    apply norm_integral_smul_sq_le_of_probability_kernel hk.measurable hik hk0 hk1
      (hck.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hiloc x)
      (hck.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hi2.locallyIntegrable x)
  have hic2 : Integrable (fun x => ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2) :=
    hbar.mono' (hc.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hpoint x)
  have hmc : MemLp (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hic2
  have hbound : (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2) ≤
      ∫ x, ‖f x‖ ^ 2 := by
    calc
      _ ≤ ∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖ ^ 2)) x :=
        integral_mono hic2 hbar hpoint
      _ = (∫ x, k x) * ∫ x, ‖f x‖ ^ 2 :=
        integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hik hi2
      _ = _ := by rw [hk1, one_mul]
  refine ⟨hmc, ?_, hbound⟩
  have hLp : lpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume ≤
      lpNorm f 2 volume := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hmc.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact Real.rpow_le_rpow (integral_nonneg fun x => sq_nonneg _) hbound (by positivity)
  rw [← ofReal_lpNorm hmc, ← ofReal_lpNorm hf]
  exact ENNReal.ofReal_le_ofReal hLp

/-- A normalized smooth bump preserves whole-space H¹, contracts both L² norms,
and has the convolution of the original weak gradient as its classical gradient. -/
theorem HasH1GradientOn.bump_convolution {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ (⊤ : ℕ∞) (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) ∧
      (∀ x, gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x) ∧
      HasH1GradientOn (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) univ ∧
      eLpNorm (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume ≤
        eLpNorm f 2 volume ∧
      eLpNorm (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) 2 volume ≤
        eLpNorm G 2 volume := by
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hbf := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmf
  have hbG := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmG
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (locallyIntegrableOn_univ.mp hf.locallyIntegrable_function)
  have hgrad := hf.toHasWeakGradientOn.gradient_convolution (k := φ.normed volume)
    φ.contDiff_normed φ.hasCompactSupport_normed
  have hw := hasWeakGradientOn_of_contDiffOn isOpen_univ
    (hcont.of_le (by simp)).contDiffOn
  rw [funext hgrad] at hw
  exact ⟨hcont, hgrad, ⟨hw,
    by simpa only [Measure.restrict_univ] using hbf.1,
    by simpa only [Measure.restrict_univ] using hbG.1⟩, hbf.2.1, hbG.2.1⟩

end LiquidDrop
