module

public import NoCompromise.Sobolev.H1Approximation
public import NoCompromise.Sobolev.H1Algebra
public import NoCompromise.BV.CoareaCoordinates

@[expose] public section

/-!
# The flat L² trace of H¹ functions

The trace is constructed by averaging the function and its normal weak derivative
on the upper unit slab. The fundamental theorem of calculus identifies this
average with boundary restriction for smooth functions. Its L² bound makes the
boundary restrictions of smooth H¹ approximants converge in L².
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Averaging over a probability factor contracts the L² norm. -/
lemma memLp_two_integral_probability {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ ∧
      lpNorm (fun x => ∫ y, f (x, y) ∂ν) 2 μ ≤ lpNorm f 2 (μ.prod ν) := by
  have hi2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hm := hf.aestronglyMeasurable.integral_prod_right'
  have hbound : ∀ᵐ x ∂μ,
      ‖∫ y, f (x, y) ∂ν‖ ^ 2 ≤ ∫ y, ‖f (x, y)‖ ^ 2 ∂ν := by
    filter_upwards [hi2.prod_right_ae, hf.aestronglyMeasurable.prodMk_left] with x hi hx
    have hmx : MemLp (fun y => f (x, y)) 2 ν :=
      (memLp_two_iff_integrable_sq_norm hx).mpr hi
    simpa only [one_smul, one_mul] using
      norm_integral_smul_sq_le_of_probability_kernel
        (μ := ν) (k := fun _ => (1 : ℝ)) measurable_const (integrable_const 1)
        (fun _ => zero_le_one) (by simp) (by simpa using hmx.integrable (by norm_num))
        (by simpa using hi)
  have hj : Integrable (fun x => ‖∫ y, f (x, y) ∂ν‖ ^ 2) μ :=
    hi2.integral_prod_left.mono' (hm.norm.pow 2) (hbound.mono fun x hx => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)
  have hmem := (memLp_two_iff_integrable_sq_norm hm).mpr hj
  refine ⟨hmem, ?_⟩
  rw [lpNorm_two_eq_sqrt_integral_norm_sq hmem, lpNorm_two_eq_sqrt_integral_norm_sq hf]
  apply Real.sqrt_le_sqrt
  exact (integral_mono_ae hj hi2.integral_prod_left hbound).trans_eq
    (integral_prod _ hi2).symm

/-- Product coordinates preserve Euclidean volume, with the normal coordinate last. -/
lemma graphAppendN_measurePreserving (k : ℕ) :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin k) × ℝ => graphAppendN p.1 p.2)
      (volume.prod volume) volume := by
  have h := MeasurePreserving.symm
    (euclideanLastEquiv k).toHomeomorph.toMeasurableEquiv
    (euclideanLastEquiv_measurePreserving k)
  exact h.comp Measure.measurePreserving_swap

/-- The unit normal interval, viewed as a probability space. -/
def flatTraceInterval : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance flatTraceInterval_isProbabilityMeasure : IsProbabilityMeasure flatTraceInterval :=
  ⟨by simp [flatTraceInterval]⟩

/-- The explicit normal average used to realize the flat trace. -/
def flatTraceIntegrand {k : ℕ} (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (p : EuclideanSpace ℝ (Fin k) × ℝ) : ℝ :=
  f (graphAppendN p.1 p.2) + (p.2 - 1) * G (graphAppendN p.1 p.2) (Fin.last k)

def flatTraceFunction {k : ℕ} (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∫ t, flatTraceIntegrand f G (x, t) ∂flatTraceInterval

/-- Pullback to the upper unit slab does not increase the L² norm. -/
lemma memLp_two_graphAppendN {k : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin (k + 1)) → F} (hf : MemLp f 2 volume) :
    MemLp (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (graphAppendN p.1 p.2)) 2
      (volume.prod flatTraceInterval) ∧
    lpNorm (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (graphAppendN p.1 p.2)) 2
      (volume.prod flatTraceInterval) ≤ lpNorm f 2 volume := by
  have hfull := hf.comp_measurePreserving (graphAppendN_measurePreserving k)
  have hle : volume.prod flatTraceInterval ≤
      (volume : Measure (EuclideanSpace ℝ (Fin k))).prod volume :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hmem := hfull.mono_measure hle
  refine ⟨hmem, ?_⟩
  change lpNorm
    (f ∘ (fun p : EuclideanSpace ℝ (Fin k) × ℝ => graphAppendN p.1 p.2)) 2 _ ≤ _
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  apply ENNReal.toReal_mono hf.eLpNorm_ne_top
  exact (eLpNorm_mono_measure _ hle).trans_eq
    (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (graphAppendN_measurePreserving k))

/-- The normal-average integrand belongs to L² and has the expected sum bound. -/
lemma memLp_flatTraceIntegrand {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume) :
    MemLp (flatTraceIntegrand f G) 2 (volume.prod flatTraceInterval) ∧
    lpNorm (flatTraceIntegrand f G) 2 (volume.prod flatTraceInterval) ≤
      lpNorm f 2 volume + lpNorm G 2 volume := by
  obtain ⟨hmf, hbf⟩ := memLp_two_graphAppendN hf
  obtain ⟨hmG, hbG⟩ := memLp_two_graphAppendN hG
  let g := fun p : EuclideanSpace ℝ (Fin k) × ℝ =>
    (p.2 - 1) * G (graphAppendN p.1 p.2) (Fin.last k)
  have hmg : AEStronglyMeasurable g (volume.prod flatTraceInterval) :=
    (measurable_snd.sub measurable_const).aestronglyMeasurable.mul
      ((EuclideanSpace.proj (Fin.last k)).continuous.comp_aestronglyMeasurable
        hmG.aestronglyMeasurable)
  have htg : ∀ᵐ p ∂(volume : Measure (EuclideanSpace ℝ (Fin k))).prod flatTraceInterval,
      ‖g p‖ ≤ ‖G (graphAppendN p.1 p.2)‖ := by
    have ht := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) (ν := flatTraceInterval)).ae
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1) measurableSet_Icc)
    filter_upwards [ht] with p hp
    have habs : |p.2 - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    calc
      _ = |p.2 - 1| * ‖G (graphAppendN p.1 p.2) (Fin.last k)‖ := norm_mul _ _
      _ ≤ 1 * ‖G (graphAppendN p.1 p.2) (Fin.last k)‖ :=
        mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ ≤ _ := by simpa using PiLp.norm_apply_le (G (graphAppendN p.1 p.2)) (Fin.last k)
  have hmemg : MemLp g 2 (volume.prod flatTraceInterval) := hmG.mono hmg htg
  have hbg : lpNorm g 2 (volume.prod flatTraceInterval) ≤ lpNorm G 2 volume := by
    rw [← toReal_eLpNorm]
    have hb : (eLpNorm g 2 (volume.prod flatTraceInterval)).toReal ≤
        (eLpNorm (fun p : EuclideanSpace ℝ (Fin k) × ℝ =>
          G (graphAppendN p.1 p.2)) 2 (volume.prod flatTraceInterval)).toReal :=
      ENNReal.toReal_mono hmG.eLpNorm_ne_top (eLpNorm_mono_ae hmg htg)
    exact hb.trans (by simpa only [toReal_eLpNorm] using hbG)
  exact ⟨hmf.add hmemg, (lpNorm_add_le hmf (by norm_num)).trans (add_le_add hbf hbg)⟩

/-- Quantitative construction of the actual L² flat trace representative. -/
theorem memLp_flatTraceFunction {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume) :
    MemLp (flatTraceFunction f G) 2 volume ∧
      lpNorm (flatTraceFunction f G) 2 volume ≤ lpNorm f 2 volume + lpNorm G 2 volume := by
  obtain ⟨hi, hb⟩ := memLp_flatTraceIntegrand hf hG
  obtain ⟨hm, hh⟩ := memLp_two_integral_probability hi
  exact ⟨hm, hh.trans hb⟩

/-- The one-dimensional FTC identifies the normal average with boundary evaluation. -/
theorem flatTraceFunction_eq_restrict_of_contDiff {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin k)) :
    flatTraceFunction f (gradient f) x = f (graphAppendN x 0) := by
  have happ : Continuous (fun t : ℝ => graphAppendN x t) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hd (t : ℝ) : HasDerivAt (fun t => f (graphAppendN x t))
      (gradient f (graphAppendN x t) (Fin.last k)) t := by
    have ht : HasDerivAt (fun t : ℝ => graphAppendN x t)
        (EuclideanSpace.single (Fin.last k) 1) t := by
      simpa only [graphAppendN, one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (EuclideanSpace.single (Fin.last k) (1 : ℝ))).const_add
          (graphBaseN k x)
    simpa only [Function.comp_def, gradient_apply_eq_fderiv_single] using
      (hf.differentiable (by norm_num) (graphAppendN x t)).hasFDerivAt.comp_hasDerivAt t ht
  have hg : Continuous (fun t => gradient f (graphAppendN x t) (Fin.last k)) :=
    (EuclideanSpace.proj (Fin.last k)).continuous.comp
      ((continuous_gradient_of_contDiff hf).comp happ)
  have h := intervalIntegral.integral_deriv_mul_eq_sub
    (u := fun t : ℝ => t - 1) (v := fun t => f (graphAppendN x t))
    (u' := fun _ => (1 : ℝ)) (v' := fun t => gradient f (graphAppendN x t) (Fin.last k))
    (a := 0) (b := 1)
    (fun t _ => (hasDerivAt_id t).sub_const 1) (fun t _ => hd t)
    (continuous_const.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
  simpa only [flatTraceFunction, flatTraceIntegrand, flatTraceInterval,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    one_mul, sub_self, zero_mul, zero_sub, neg_one_mul, neg_neg] using h

/-- The normal integrands of L² data are integrable on almost every normal segment. -/
lemma ae_integrable_flatTraceIntegrand {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume) :
    ∀ᵐ x ∂volume, Integrable (fun t => flatTraceIntegrand f G (x, t)) flatTraceInterval := by
  have hi := (memLp_flatTraceIntegrand hf hG).1
  have hi2 := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  filter_upwards [hi2.prod_right_ae, hi.aestronglyMeasurable.prodMk_left] with x hx hm
  exact ((memLp_two_iff_integrable_sq_norm hm).mpr hx).integrable (by norm_num)

lemma flatTraceFunction_sub_ae {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume)
    (hh : MemLp h 2 volume) (hH : MemLp H 2 volume) :
    flatTraceFunction (f - h) (G - H) =ᵐ[volume]
      flatTraceFunction f G - flatTraceFunction h H := by
  filter_upwards [ae_integrable_flatTraceIntegrand hf hG,
    ae_integrable_flatTraceIntegrand hh hH] with x hx hy
  have heq : (fun t => flatTraceIntegrand (f - h) (G - H) (x, t)) =
      fun t => flatTraceIntegrand f G (x, t) - flatTraceIntegrand h H (x, t) := by
    funext t
    simp only [flatTraceIntegrand, Pi.sub_apply, PiLp.sub_apply]
    ring
  change (∫ t, flatTraceIntegrand (f - h) (G - H) (x, t) ∂flatTraceInterval) = _
  rw [heq, integral_sub hx hy]
  rfl

/-- The trace is stable under strong convergence of the function and weak gradient. -/
theorem lpNorm_flatTraceFunction_sub_le {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume)
    (hh : MemLp h 2 volume) (hH : MemLp H 2 volume) :
    lpNorm (flatTraceFunction f G - flatTraceFunction h H) 2 volume ≤
      lpNorm (f - h) 2 volume + lpNorm (G - H) 2 volume := by
  have ht := memLp_flatTraceFunction (hf.sub hh) (hG.sub hH)
  have hm := ((memLp_flatTraceFunction hf hG).1.sub (memLp_flatTraceFunction hh hH).1)
  calc
    _ = lpNorm (flatTraceFunction (f - h) (G - H)) 2 volume := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (flatTraceFunction_sub_ae hf hG hh hH).symm)
    _ ≤ _ := ht.2

/-- Any strong H¹ approximation has strongly convergent flat traces. -/
theorem tendsto_flatTraceFunction {k : ℕ} {ι : Type*} {l : Filter ι}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {f' : ι → EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G' : ι → EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume)
    (hf' : ∀ j, MemLp (f' j) 2 volume) (hG' : ∀ j, MemLp (G' j) 2 volume)
    (hcf : Tendsto (fun j => lpNorm (f' j - f) 2 volume) l (𝓝 0))
    (hcG : Tendsto (fun j => lpNorm (G' j - G) 2 volume) l (𝓝 0)) :
    Tendsto (fun j => lpNorm (flatTraceFunction (f' j) (G' j) - flatTraceFunction f G)
      2 volume) l (𝓝 0) := by
  apply squeeze_zero (fun _ => lpNorm_nonneg)
    (fun j => lpNorm_flatTraceFunction_sub_le (hf' j) (hG' j) hf hG)
  simpa only [zero_add] using hcf.add hcG

/-- Boundary restrictions of the actual smooth mollifications converge to the trace in L². -/
theorem HasH1GradientOn.tendsto_flatTrace_bump_convolution {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ)
    {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1)))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => lpNorm (fun x =>
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) (graphAppendN x 0) -
        flatTraceFunction f G x) 2 volume) l (𝓝 0) := by
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmj (j) := hf.bump_convolution (φ j)
  have hconv := tendsto_flatTraceFunction hmf hmG
    (fun j => by simpa only [Measure.restrict_univ] using (hmj j).2.2.1.memLp_function)
    (fun j => by simpa only [Measure.restrict_univ] using (hmj j).2.2.1.memLp_gradient)
    (tendsto_lpNorm_bump_convolution_sub hmf hφ)
    (tendsto_lpNorm_bump_convolution_sub hmG hφ)
  convert hconv using 1
  funext j
  congr 1
  funext x
  simp only [Pi.sub_apply]
  rw [← funext (hmj j).2.1]
  exact congrArg (fun z => z - flatTraceFunction f G x)
    (flatTraceFunction_eq_restrict_of_contDiff ((hmj j).1.of_le (by simp)) x).symm

/-- The open upper unit slab. -/
def flatTraceSlab (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 1))) :=
  {x | x (Fin.last k) ∈ Ioo (0 : ℝ) 1}

lemma measurableSet_flatTraceSlab (k : ℕ) : MeasurableSet (flatTraceSlab k) :=
  measurableSet_Ioo.preimage (EuclideanSpace.proj (Fin.last k)).continuous.measurable

lemma graphAppendN_slab_measurePreserving (k : ℕ) :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin k) × ℝ => graphAppendN p.1 p.2)
      (volume.prod flatTraceInterval) (volume.restrict (flatTraceSlab k)) := by
  have h := (graphAppendN_measurePreserving k).restrict_preimage (measurableSet_flatTraceSlab k)
  have heq : (fun p : EuclideanSpace ℝ (Fin k) × ℝ => graphAppendN p.1 p.2) ⁻¹'
      flatTraceSlab k = univ ×ˢ Ioo (0 : ℝ) 1 := by
    ext p
    simp only [mem_preimage, flatTraceSlab, mem_ofPred_eq, graphAppendN_last,
      mem_prod, mem_univ, true_and]
  rw [heq, ← Measure.prod_restrict, Measure.restrict_univ, restrict_Ioo_eq_restrict_Icc] at h
  exact h

/-- Only the almost-everywhere values of the function and gradient in the upper
slab enter the trace. -/
lemma flatTraceFunction_congr_ae_on_slab {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : f =ᵐ[volume.restrict (flatTraceSlab k)] h)
    (hG : G =ᵐ[volume.restrict (flatTraceSlab k)] H) :
    flatTraceFunction f G =ᵐ[volume] flatTraceFunction h H := by
  have hp := (graphAppendN_slab_measurePreserving k).quasiMeasurePreserving
  have heq : flatTraceIntegrand f G =ᵐ[volume.prod flatTraceInterval]
      flatTraceIntegrand h H := by
    filter_upwards [hp.ae_eq_comp hf, hp.ae_eq_comp hG] with p hfp hGp
    simp only [Function.comp_def] at hfp hGp
    simp only [flatTraceIntegrand, hfp, hGp]
  filter_upwards [Measure.ae_ae_of_ae_prod heq] with x hx
  exact integral_congr_ae hx

lemma flatTraceFunction_congr_ae {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : f =ᵐ[volume] h) (hG : G =ᵐ[volume] H) :
    flatTraceFunction f G =ᵐ[volume] flatTraceFunction h H :=
  flatTraceFunction_congr_ae_on_slab (ae_restrict_of_ae hf) (ae_restrict_of_ae hG)

lemma flatTraceFunction_add_ae {k : ℕ}
    {f h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 volume) (hG : MemLp G 2 volume)
    (hh : MemLp h 2 volume) (hH : MemLp H 2 volume) :
    flatTraceFunction (f + h) (G + H) =ᵐ[volume]
      flatTraceFunction f G + flatTraceFunction h H := by
  filter_upwards [ae_integrable_flatTraceIntegrand hf hG,
    ae_integrable_flatTraceIntegrand hh hH] with x hx hy
  have heq : (fun t => flatTraceIntegrand (f + h) (G + H) (x, t)) =
      fun t => flatTraceIntegrand f G (x, t) + flatTraceIntegrand h H (x, t) := by
    funext t
    simp only [flatTraceIntegrand, Pi.add_apply, PiLp.add_apply]
    ring
  change (∫ t, flatTraceIntegrand (f + h) (G + H) (x, t) ∂flatTraceInterval) = _
  rw [heq, integral_add hx hy]
  rfl

lemma flatTraceFunction_smul {k : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))) (c : ℝ) :
    flatTraceFunction (c • f) (c • G) = c • flatTraceFunction f G := by
  funext x
  have heq : (fun t => flatTraceIntegrand (c • f) (c • G) (x, t)) =
      fun t => c * flatTraceIntegrand f G (x, t) := by
    funext t
    simp only [flatTraceIntegrand, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  change (∫ t, flatTraceIntegrand (c • f) (c • G) (x, t) ∂flatTraceInterval) = _
  rw [heq, integral_const_mul]
  rfl

/-- The trace estimate uses only L² data in the open upper unit slab. -/
theorem memLp_flatTraceFunction_on_slab {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 (volume.restrict (flatTraceSlab k)))
    (hG : MemLp G 2 (volume.restrict (flatTraceSlab k))) :
    MemLp (flatTraceFunction f G) 2 volume ∧
      lpNorm (flatTraceFunction f G) 2 volume ≤
        lpNorm f 2 (volume.restrict (flatTraceSlab k)) +
          lpNorm G 2 (volume.restrict (flatTraceSlab k)) := by
  have hs := measurableSet_flatTraceSlab k
  have hif := (memLp_indicator_iff_restrict hs).mpr hf
  have hiG := (memLp_indicator_iff_restrict hs).mpr hG
  have ht := memLp_flatTraceFunction hif hiG
  have heq := flatTraceFunction_congr_ae_on_slab
    (indicator_ae_eq_restrict (f := f) hs) (indicator_ae_eq_restrict (f := G) hs)
  have hm := ht.1.ae_eq heq
  refine ⟨hm, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae heq, toReal_eLpNorm]
  convert ht.2 using 1
  rw [← toReal_eLpNorm (f := (flatTraceSlab k).indicator f),
    ← toReal_eLpNorm (f := (flatTraceSlab k).indicator G),
    eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_indicator_eq_eLpNorm_restrict hs,
    toReal_eLpNorm, toReal_eLpNorm]

/-- A concrete smooth sequence realizes the flat trace as an L² boundary limit. -/
theorem HasH1GradientOn.exists_smooth_flatTrace_approx {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasH1GradientOn (v j) (gradient (v j)) univ) ∧
      Tendsto (fun j => lpNorm (v j - f) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun j => lpNorm (gradient (v j) - G) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun j => lpNorm (fun x => v j (graphAppendN x 0) - flatTraceFunction f G x)
        2 volume) atTop (𝓝 0) := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1))) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  refine ⟨v, fun j => ?_, tendsto_lpNorm_bump_convolution_sub hmf hφ, ?_,
    hf.tendsto_flatTrace_bump_convolution hφ⟩
  · have hj := hf.bump_convolution (φ j)
    refine ⟨hj.1, ?_⟩
    change HasH1GradientOn
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
      (gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)) univ
    rw [funext hj.2.1]
    exact hj.2.2.1
  · have hgrad (j : ℕ) := funext (hf.bump_convolution (φ j)).2.1
    simp only [v, hgrad]
    exact tendsto_lpNorm_bump_convolution_sub hmG hφ

namespace H1Space

/-- The actual L² trace class on the coordinate hyperplane. -/
def flatTrace {k : ℕ} (u : H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
  (memLp_flatTraceFunction
    (by simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_function)
    (by simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_gradient)).1.toLp
      (flatTraceFunction u u.gradientLp)

lemma coeFn_flatTrace {k : ℕ}
    (u : H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    ⇑u.flatTrace =ᵐ[volume] flatTraceFunction u u.gradientLp := MemLp.coeFn_toLp _


/-- The trace of an H¹ class is the normal average of any of its representatives. -/
lemma coeFn_flatTrace_ofFunction {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) :
    ⇑(ofFunction f G hf).flatTrace =ᵐ[volume] flatTraceFunction f G := by
  apply (coeFn_flatTrace (ofFunction f G hf)).trans
  exact flatTraceFunction_congr_ae
    (by simpa only [Measure.restrict_univ] using coeFn_ofFunction f G hf)
    (by simpa only [Measure.restrict_univ] using gradientLp_ofFunction f G hf)

/-- For a smooth H¹ function, the constructed trace agrees with classical restriction. -/
lemma coeFn_flatTrace_of_contDiff {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hf : HasH1GradientOn f (gradient f) univ) (hc : ContDiff ℝ 1 f) :
    ⇑(ofFunction f (gradient f) hf).flatTrace =ᵐ[volume]
      (fun x => f (graphAppendN x 0)) := by
  exact (coeFn_flatTrace_ofFunction hf).trans
    (Eventually.of_forall fun x => flatTraceFunction_eq_restrict_of_contDiff hc x)

lemma norm_flatTrace_le {k : ℕ}
    (u : H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    ‖u.flatTrace‖ ≤ 2 * ‖u‖ := by
  have hf : MemLp u 2 volume := by
    simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_function
  have hG : MemLp u.gradientLp 2 volume := by
    simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_gradient
  have hn : ‖u.flatTrace‖ = lpNorm (flatTraceFunction u u.gradientLp) 2 volume := by
    rw [flatTrace, Lp.norm_toLp, toReal_eLpNorm]
  rw [hn]
  apply (memLp_flatTraceFunction hf hG).2.trans
  simpa only [norm_toLp_eq_lpNorm, norm_gradientLp_eq_lpNorm, Measure.restrict_univ] using
    u.sum_norm_le

lemma flatTrace_add {k : ℕ}
    (u v : H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    (u + v).flatTrace = u.flatTrace + v.flatTrace := by
  apply Lp.ext
  have hrep := flatTraceFunction_congr_ae
    (by simpa only [Measure.restrict_univ] using coeFn_add u v)
    (by simpa only [Measure.restrict_univ] using coeFn_gradientLp_add u v)
  have hadd := flatTraceFunction_add_ae
    (by simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_function)
    (by simpa only [Measure.restrict_univ] using u.hasH1GradientOn.memLp_gradient)
    (by simpa only [Measure.restrict_univ] using v.hasH1GradientOn.memLp_function)
    (by simpa only [Measure.restrict_univ] using v.hasH1GradientOn.memLp_gradient)
  filter_upwards [coeFn_flatTrace (u + v), hrep, hadd, coeFn_flatTrace u, coeFn_flatTrace v,
    Lp.coeFn_add u.flatTrace v.flatTrace] with x h1 h2 h3 h4 h5 h6
  simp only [Pi.add_apply] at h3 h6
  exact h1.trans (h2.trans (h3.trans (by rw [← h4, ← h5, h6])))

lemma flatTrace_smul {k : ℕ} (c : ℝ)
    (u : H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    (c • u).flatTrace = c • u.flatTrace := by
  apply Lp.ext
  have hrep := flatTraceFunction_congr_ae
    (by simpa only [Measure.restrict_univ] using coeFn_smul c u)
    (by simpa only [Measure.restrict_univ] using coeFn_gradientLp_smul c u)
  filter_upwards [coeFn_flatTrace (c • u), hrep, coeFn_flatTrace u,
    Lp.coeFn_smul c u.flatTrace] with x h1 h2 h3 h4
  have hc := congrFun (flatTraceFunction_smul (u : _ → ℝ) (u.gradientLp : _ → _) c) x
  simp only [Pi.smul_apply, smul_eq_mul] at hc h4
  exact h1.trans (h2.trans (hc.trans (by rw [← h3, h4])))

/-- The flat trace is a constructed bounded linear map into actual L² classes. -/
def flatTraceCLM (k : ℕ) :
    H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1)))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
  ({ toFun := flatTrace
     map_add' := flatTrace_add
     map_smul' := flatTrace_smul } :
      H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1)))) →ₗ[ℝ]
        Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin k)))).mkContinuous 2 norm_flatTrace_le

lemma norm_flatTraceCLM_le (k : ℕ) : ‖flatTraceCLM k‖ ≤ 2 :=
  (flatTraceCLM k).opNorm_le_bound (by norm_num) norm_flatTrace_le

end H1Space

end LiquidDrop
