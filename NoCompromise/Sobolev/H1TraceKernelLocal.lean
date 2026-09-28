import NoCompromise.Sobolev.H1TraceKernelInward
import NoCompromise.Sobolev.H1TraceKernelChartTrace
import NoCompromise.Sobolev.H1TraceKernelTransport
import NoCompromise.Sobolev.H1TraceKernelFlat

/-!
# The trace kernel on one Lipschitz boundary chart

Flatten, extend by zero, translate inward, and transport the strong H¹
approximation back. Every approximant has compact support in the domain.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem HasH1GradientOn.mem_h1Zero_of_chartTrace_zero {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ c.region)
    (hzero : H1Space.chartTraceCLM c.boundaryPlaneChart c.lipschitz_boundaryPlaneChart
      c.lipschitz_boundaryPlaneChart_symm (H1Space.ofFunction f G hf) = 0) :
    H1Space.ofFunction f G (hf.mono (subset_univ D)) ∈ h1ZeroSubmodule hD := by
  let e := c.boundaryPlaneChart
  let P := fun x => (fderiv ℝ e x).adjoint (G (e x))
  have hp : HasH1GradientOn (f ∘ e) P univ :=
    (hf.comp_homeomorph e c.lipschitz_boundaryPlaneChart
      c.lipschitz_boundaryPlaneChart_symm).1
  have htclm : (H1Space.ofFunction (f ∘ e) P hp).flatTrace = 0 := by
    change (H1Space.flatTraceCLM k)
      (H1Space.chartPullbackCLM e c.lipschitz_boundaryPlaneChart
        c.lipschitz_boundaryPlaneChart_symm (H1Space.ofFunction f G hf)) = 0 at hzero
    rw [H1Space.chartPullbackCLM_ofFunction e c.lipschitz_boundaryPlaneChart
      c.lipschitz_boundaryPlaneChart_symm hf] at hzero
    exact hzero
  have ht : flatTraceFunction (f ∘ e) P =ᵐ[volume] 0 := by
    have h := H1Space.coeFn_flatTrace_ofFunction hp
    rw [htclm] at h
    exact h.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  let w := U.indicator (f ∘ e)
  let J := U.indicator P
  have hw : HasH1GradientOn w J univ := by
    simpa only [smoothEpigraph] using hp.indicator_upperHalfspace_of_flatTrace_zero ht
  have hsupport : tsupport w ⊆ tsupport (f ∘ e) := by
    apply closure_mono
    intro x hx
    by_contra hn
    have hz : (f ∘ e) x = 0 := by simpa only [Function.mem_support, not_not] using hn
    exact hx (by
      change U.indicator (f ∘ e) x = 0
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU, hz]
      · exact indicator_of_notMem hxU _)
  have hcw : HasCompactSupport w :=
    (hcf.comp_homeomorph e).of_isClosed_subset (isClosed_tsupport _) hsupport
  have hsW : tsupport w ⊆ e ⁻¹' c.region := by
    intro x hx
    exact hs (tsupport_comp_subset_preimage f e.continuous (hsupport hx))
  have hsi : ∀ x ∈ tsupport w, 0 ≤ x (Fin.last k) := by
    apply closure_minimal _ (isClosed_le continuous_const
      (EuclideanSpace.proj (Fin.last k)).continuous)
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      exact hx (indicator_of_notMem hn (f ∘ e))
    exact (show 0 < x (Fin.last k) from hxU).le
  obtain ⟨a, ha, has⟩ := exists_inward_translations_of_compact (Fin.last k) hcw
    (c.isOpen_region.preimage e.continuous) hsW hsi
  have hsa (j : ℕ) : tsupport (fun x => w (x - a j)) ⊆ e ⁻¹' D := by
    intro x hx
    have hxK := tsupport_comp_subset_preimage w (continuous_id.sub continuous_const) hx
    obtain ⟨hxW, hxi⟩ := has j x hxK
    apply (c.mem_domain_iff_last_pos hc hxW).mpr
    change 0 < e.symm (e x) (Fin.last k)
    simpa only [e.symm_apply_apply] using hxi
  have hmem := hw.mem_h1Zero_of_translated_homeomorph hD e
    c.lipschitz_boundaryPlaneChart c.lipschitz_boundaryPlaneChart_symm hcw ha hsa
  have heq (x : EuclideanSpace ℝ (Fin (k + 1))) (hxD : x ∈ D) :
      (w ∘ e.symm) x = f x := by
    by_cases hx : f x = 0
    · by_cases hxU : e.symm x ∈ U <;>
        simp [Function.comp_def, w, hxU, hx]
    · have hxr := hs (subset_tsupport f hx)
      have hxU : e.symm x ∈ U := (c.mem_domain_iff_last_pos hc hxr).mp hxD
      simp only [Function.comp_def, w, indicator_of_mem hxU, e.apply_symm_apply]
  have hclass : H1Space.ofFunction (w ∘ e.symm)
      (fun x => (fderiv ℝ e.symm x).adjoint (J (e.symm x)))
      ((hw.comp_homeomorph e.symm c.lipschitz_boundaryPlaneChart_symm
        c.lipschitz_boundaryPlaneChart).1.mono (subset_univ D)) =
      H1Space.ofFunction f G (hf.mono (subset_univ D)) := by
    apply H1Space.ext_ae hD
    filter_upwards [H1Space.coeFn_ofFunction _ _
        ((hw.comp_homeomorph e.symm c.lipschitz_boundaryPlaneChart_symm
          c.lipschitz_boundaryPlaneChart).1.mono (subset_univ D)),
      H1Space.coeFn_ofFunction _ _ (hf.mono (subset_univ D)),
      ae_restrict_mem hD.measurableSet] with x hx hy hxD
    exact hx.trans ((heq x hxD).trans hy.symm)
  exact hclass ▸ hmem

theorem HasH1GradientOn.mem_h1Zero_of_local_domainTrace_zero {k : ℕ}
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
    H1Space.ofFunction f G (hf.mono (subset_univ D)) ∈ h1ZeroSubmodule hD :=
  hf.mem_h1Zero_of_chartTrace_zero hD c hc hcf hs
    (hf.chartTrace_eq_zero_of_domainTrace hD c hc T hT hcf hs hzero)

end LiquidDrop
