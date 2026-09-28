import NoCompromise.Sobolev.H1Trace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Continuous realization of the flat H¹ trace

For continuous H¹ representatives the constructed L² trace is almost everywhere
ordinary restriction to the plane. Pointwise convergence of mollification and
strong L² convergence of its boundary restrictions identify the two limits.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The flat trace of a continuous H¹ representative is its actual boundary value. -/
theorem flatTraceFunction_eq_restrict_ae_of_continuous {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    flatTraceFunction f G =ᵐ[volume] (fun x => f (graphAppendN x 0)) := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1))) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) :=
    ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) (graphAppendN x 0)
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have ht := (memLp_flatTraceFunction hmf hmG).1
  have hv (j : ℕ) : MemLp (v j) 2 volume := by
    have hj := hf.bump_convolution (φ j)
    have hm := (memLp_flatTraceFunction
      (by simpa only [Measure.restrict_univ] using hj.2.2.1.memLp_function)
      (by simpa only [Measure.restrict_univ] using hj.2.2.1.memLp_gradient)).1
    have heq : flatTraceFunction
        ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
        ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) = v j := by
      rw [← funext hj.2.1]
      exact funext (flatTraceFunction_eq_restrict_of_contDiff (hj.1.of_le (by simp)))
    rwa [heq] at hm
  have hnorm : Tendsto (fun j => lpNorm (v j - flatTraceFunction f G) 2 volume)
      atTop (𝓝 0) := hf.tendsto_flatTrace_bump_convolution hφ
  have hel : Tendsto (fun j => eLpNorm (v j - flatTraceFunction f G) 2 volume)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
    simpa only [Function.comp_def, ENNReal.ofReal_zero,
      ofReal_lpNorm ((hv _).sub ht)] using h
  have him := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hel
  obtain ⟨s, hs, hsae⟩ := him.exists_seq_tendsto_ae
  filter_upwards [hsae] with x hx
  have hpt := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) hφ hc (graphAppendN x 0)
  have hpoint := hpt.comp hs.tendsto_atTop
  exact tendsto_nhds_unique hx hpoint

/-- Continuous H¹ functions have square-integrable boundary restrictions. -/
theorem memLp_restrict_plane_of_continuous_h1 {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    MemLp (fun x => f (graphAppendN x 0)) 2 volume ∧
      lpNorm (fun x => f (graphAppendN x 0)) 2 volume ≤
        lpNorm f 2 (volume.restrict (flatTraceSlab k)) +
          lpNorm G 2 (volume.restrict (flatTraceSlab k)) := by
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have ht := memLp_flatTraceFunction_on_slab
    (hmf.mono_measure Measure.restrict_le_self) (hmG.mono_measure Measure.restrict_le_self)
  have heq := flatTraceFunction_eq_restrict_ae_of_continuous hf hc
  have hm := ht.1.ae_eq heq
  refine ⟨hm, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae heq, toReal_eLpNorm]
  exact ht.2

/-- Continuous representatives identify the class-valued trace without C¹ regularity. -/
lemma H1Space.coeFn_flatTrace_of_continuous {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    ⇑(H1Space.ofFunction f G hf).flatTrace =ᵐ[volume] (fun x => f (graphAppendN x 0)) :=
  (H1Space.coeFn_flatTrace_ofFunction hf).trans
    (flatTraceFunction_eq_restrict_ae_of_continuous hf hc)

end LiquidDrop
