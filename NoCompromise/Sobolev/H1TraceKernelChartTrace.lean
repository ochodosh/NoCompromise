import NoCompromise.Sobolev.H1TraceKernelChartGeometry
import NoCompromise.Sobolev.H1TraceKernelApprox

/-!
# Recovering the flat trace from the domain trace

For representatives compactly supported inside one boundary chart, the actual
domain trace controls the actual chart trace. Strong smooth approximation then
transfers vanishing of the former to vanishing of the latter.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma lpNorm_restrict_le_of_support {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {A B S : Set α} {f : α → F}
    {p : ℝ≥0∞} (hS : MeasurableSet S) (hs : Function.support f ⊆ S)
    (hAB : A ∩ S ⊆ B) (hfA : MemLp f p (μ.restrict A))
    (hfB : MemLp f p (μ.restrict B)) :
    lpNorm f p (μ.restrict A) ≤ lpNorm f p (μ.restrict B) := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  apply ENNReal.toReal_mono hfB.eLpNorm_ne_top
  rw [← eLpNorm_restrict_eq_of_support_subset hfA.aestronglyMeasurable hs,
    Measure.restrict_restrict hS, inter_comm S A]
  exact eLpNorm_mono_measure f (Measure.restrict_mono hAB le_rfl)

theorem norm_chartTrace_sq_le_domainTrace {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (H1Space.ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict
        (frontier D)] f)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcont : Continuous f)
    (hs : tsupport f ⊆ c.region) :
    ‖H1Space.chartTraceCLM c.boundaryPlaneChart c.lipschitz_boundaryPlaneChart
      c.lipschitz_boundaryPlaneChart_symm (H1Space.ofFunction f G hf)‖ ^ 2 ≤
        (1 + (c.lip : ℝ)) ^ k *
          ‖T (H1Space.ofFunction f G (hf.mono (subset_univ D)))‖ ^ 2 := by
  let e := c.boundaryPlaneChart
  let P := range (fun x => e (graphAppendN x 0))
  have hplane := memLp_chart_surface_of_continuous_h1 e
    c.lipschitz_boundaryPlaneChart c.lipschitz_boundaryPlaneChart_symm hf hcont
  have hparam := memLp_chart_parameter_of_surface e c.lipschitz_boundaryPlaneChart_symm
    hplane.1
  have hTr := hT f G (hf.mono (subset_univ D)) hcont
  have hbound : MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) :=
    (Lp.memLp _).ae_eq hTr
  have hle := lpNorm_restrict_le_of_support c.isOpen_region.measurableSet
    ((subset_tsupport f).trans hs) (c.plane_inter_region_subset_frontier hD hc)
    hplane.1 hbound
  have hchart := H1Space.coeFn_chartTraceCLM_of_continuous e
    c.lipschitz_boundaryPlaneChart c.lipschitz_boundaryPlaneChart_symm hf hcont
  rw [Lp.norm_def, eLpNorm_congr_ae hchart, toReal_eLpNorm,
    Lp.norm_def, eLpNorm_congr_ae hTr, toReal_eLpNorm]
  apply hparam.2.trans
  simp only [NNReal.coe_add, NNReal.coe_one]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hle 2) (by positivity)

theorem HasH1GradientOn.chartTrace_eq_zero_of_domainTrace {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (H1Space.ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict
        (frontier D)] f)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ c.region)
    (hzero : T (H1Space.ofFunction f G (hf.mono (subset_univ D))) = 0) :
    H1Space.chartTraceCLM c.boundaryPlaneChart c.lipschitz_boundaryPlaneChart
      c.lipschitz_boundaryPlaneChart_symm (H1Space.ofFunction f G hf) = 0 := by
  obtain ⟨V, _, _, _, hVU, _, v, hv, hcv, hcG⟩ :=
    hf.exists_smooth_compact_test_approximation c.isOpen_region hcf hs
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmv (j : ℕ) : MemLp (v j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_function
  have hmvg (j : ℕ) : MemLp (gradient (v j)) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_gradient
  have hfv := tendsto_lpNorm_sub_of_eLpNorm hmv hmf hcv
  have hGv := tendsto_lpNorm_sub_of_eLpNorm hmvg hmG hcG
  have hglobal := H1Space.tendsto_ofFunction_restrict isOpen_univ hf
    (fun j => (hv j).2.2.2) hfv hGv
  have hdomain := H1Space.tendsto_ofFunction_restrict hD hf
    (fun j => (hv j).2.2.2) hfv hGv
  let A := H1Space.chartTraceCLM c.boundaryPlaneChart c.lipschitz_boundaryPlaneChart
    c.lipschitz_boundaryPlaneChart_symm
  have ha := ((A.continuous.tendsto _).comp hglobal).norm.pow 2
  have hb := (((T.continuous.tendsto _).comp hdomain).norm.pow 2).const_mul
    ((1 + (c.lip : ℝ)) ^ k)
  rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hb
  have hle := le_of_tendsto_of_tendsto ha hb (Eventually.of_forall fun j =>
    norm_chartTrace_sq_le_domainTrace hD c hc T hT (hv j).2.2.2 (hv j).1.continuous
      ((hv j).2.2.1.trans (subset_closure.trans hVU)))
  apply norm_eq_zero.mp
  nlinarith only [hle, norm_nonneg (A (H1Space.ofFunction f G hf))]

end LiquidDrop
