import NoCompromise.Sobolev.H1TraceKernelOperators
import NoCompromise.Sobolev.H1TraceKernelApprox

/-!
# Localization preserves zero boundary trace

The statement is proved for the actual trace operator using global smooth
approximation and its agreement with continuous representatives.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma norm_Lp_le_mul_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℝ 2 μ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ A * ‖g x‖) : ‖f‖ ≤ A * ‖g‖ := by
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable f) hb 2
  have hr := ENNReal.toReal_mono (by finiteness :
    ENNReal.ofReal A * eLpNorm g 2 μ ≠ ∞) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ← Lp.norm_def] using hr

theorem HasH1GradientOn.domainTrace_cutoff_eq_zero {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (H1Space.ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict
        (frontier D)] f)
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B)
    (hzero : T (H1Space.ofFunction f G (hf.mono (subset_univ D))) = 0) :
    T (H1Space.ofFunction (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x)
      ((hf.mul_compact_cutoff MeasurableSet.univ hζ hcζ (subset_univ _)
        hbζ hbgrad).1.mono (subset_univ D))) = 0 := by
  let R := H1Space.restrictionCLM isOpen_univ hD (subset_univ D)
  let M := H1Space.cutoffCLM hζ hcζ hA hB hbζ hbgrad
  let S := T.comp (R.comp M)
  let Q := T.comp R
  have hS (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
      (J : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
      (hg : HasH1GradientOn g J univ) :
      S (H1Space.ofFunction g J hg) = T (H1Space.ofFunction (fun x => ζ x * g x)
        (fun x => ζ x • J x + g x • gradient ζ x)
        ((hg.mul_compact_cutoff MeasurableSet.univ hζ hcζ (subset_univ _)
          hbζ hbgrad).1.mono (subset_univ D))) := by
    simp only [S, R, M, ContinuousLinearMap.comp_apply, H1Space.cutoffCLM_ofFunction,
      H1Space.restrictionCLM_ofFunction]
  have hQ (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
      (J : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
      (hg : HasH1GradientOn g J univ) :
      Q (H1Space.ofFunction g J hg) =
        T (H1Space.ofFunction g J (hg.mono (subset_univ D))) := by
    simp only [Q, R, ContinuousLinearMap.comp_apply, H1Space.restrictionCLM_ofFunction]
  have hbound (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
      (J : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
      (hg : HasH1GradientOn g J univ) (hcg : Continuous g) :
      ‖S (H1Space.ofFunction g J hg)‖ ≤ A * ‖Q (H1Space.ofFunction g J hg)‖ := by
    rw [hS, hQ]
    apply norm_Lp_le_mul_of_ae_bound _ _ hA
    filter_upwards [hT _ _ ((hg.mul_compact_cutoff MeasurableSet.univ hζ hcζ
      (subset_univ _) hbζ hbgrad).1.mono (subset_univ D)) (hζ.continuous.mul hcg),
      hT g J (hg.mono (subset_univ D)) hcg] with x hx hy
    rw [hx, hy, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbζ x) (norm_nonneg _)
  obtain ⟨V, _, _, _, _, _, v, hv, hcv, hcG⟩ :=
    hf.exists_smooth_compact_test_approximation isOpen_univ hcf (subset_univ _)
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmv (j : ℕ) : MemLp (v j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_function
  have hmvg (j : ℕ) : MemLp (gradient (v j)) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_gradient
  have hconv := H1Space.tendsto_ofFunction_restrict isOpen_univ hf (fun j => (hv j).2.2.2)
    (tendsto_lpNorm_sub_of_eLpNorm hmv hmf hcv)
    (tendsto_lpNorm_sub_of_eLpNorm hmvg hmG hcG)
  have hSconv := ((S.continuous.tendsto _).comp hconv).norm
  have hQconv := (((Q.continuous.tendsto _).comp hconv).norm).const_mul A
  rw [hQ, hzero, norm_zero, mul_zero] at hQconv
  have hle := le_of_tendsto_of_tendsto hSconv hQconv
    (Eventually.of_forall fun j => hbound _ _ (hv j).2.2.2 (hv j).1.continuous)
  rw [← hS f G hf]
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

end LiquidDrop
