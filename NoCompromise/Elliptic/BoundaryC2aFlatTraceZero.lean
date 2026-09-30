module

public import NoCompromise.Elliptic.BoundaryHolderTrace
public import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals

@[expose] public section

/-!
# Zero flat trace of functions continuous up to the flat face

A function continuous on the upper part of the unit ball, C¹ in the open half ball with an
integrable gradient, and vanishing on the flat face has zero localized flat trace on the unit
ball. Along almost every normal segment the fundamental theorem of calculus applies to
`t ↦ (t - 1) (ζ f)(x', t)`, whose derivative is exactly the normal-average integrand.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

private lemma boundary_zero_trace_segment_hasDerivAt (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => graphAppendN x t)
      (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) t := by
  simpa only [graphAppendN, one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (EuclideanSpace.single (Fin.last 2) (1 : ℝ))).const_add
      (graphBaseN 2 x)

private lemma boundary_zero_trace_segment_continuous (x : EuclideanSpace ℝ (Fin 2)) :
    Continuous (fun t : ℝ => graphAppendN x t) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- Continuity of the localized function on the closed upper halfspace. -/
private lemma boundary_zero_trace_continuousOn {f ζ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (ball 0 1 ∩ {x | 0 ≤ x (Fin.last 2)}))
    (hζ : Continuous ζ) (hsζ : tsupport ζ ⊆ ball 0 1) :
    ContinuousOn (fun x => ζ x * f x) {x | 0 ≤ x (Fin.last 2)} := by
  intro p hp
  by_cases hpb : p ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  · have h1 : ContinuousWithinAt (fun x => ζ x * f x)
        ({x | 0 ≤ x (Fin.last 2)} ∩ ball 0 1) p := by
      rw [inter_comm]
      exact hζ.continuousWithinAt.mul (hf p ⟨hpb, hp⟩)
    exact (continuousWithinAt_inter (isOpen_ball.mem_nhds hpb)).mp h1
  · apply ContinuousAt.continuousWithinAt
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hpb (hsζ h))
    apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- Along a normal segment, the localized function has the normal component of the localized
field as derivative at every positive height. -/
private lemma boundary_zero_trace_hasDerivAt {f ζ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hC1 : ContDiffOn ℝ 1 f (boundaryHalfBall 1))
    (hG : EqOn G (gradient f) (boundaryHalfBall 1))
    (hζ : ContDiff ℝ 1 ζ) (hsζ : tsupport ζ ⊆ ball 0 1)
    (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => ζ (graphAppendN x t) * f (graphAppendN x t))
      ((ζ (graphAppendN x t) • G (graphAppendN x t) +
        f (graphAppendN x t) • gradient ζ (graphAppendN x t)) (Fin.last 2)) t := by
  by_cases hpb : graphAppendN x t ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  · have hpU : graphAppendN x t ∈ boundaryHalfBall 1 := by
      refine ⟨hpb, ?_⟩
      change 0 < graphAppendN x t (Fin.last 2)
      rw [graphAppendN_last]
      exact ht
    have hfd : DifferentiableAt ℝ f (graphAppendN x t) :=
      (hC1.contDiffAt ((isOpen_boundaryHalfBall 1).mem_nhds hpU)).differentiableAt one_ne_zero
    have hζd : DifferentiableAt ℝ ζ (graphAppendN x t) := hζ.differentiable one_ne_zero _
    have hd := (hζd.hasFDerivAt.mul hfd.hasFDerivAt).comp_hasDerivAt t
      (boundary_zero_trace_segment_hasDerivAt x t)
    refine hd.congr_deriv ?_
    rw [hG hpU]
    simp only [add_apply, smul_apply, smul_eq_mul,
      PiLp.add_apply, PiLp.smul_apply, gradient_apply_eq_fderiv_single]
  · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hpb (hsζ h))
    have hζp : ζ (graphAppendN x t) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hpb (hsζ h))
    have hgp : gradient ζ (graphAppendN x t) = 0 :=
      gradient_eq_zero_of_notMem_tsupport (fun h => hpb (hsζ h))
    have hev := ((boundary_zero_trace_segment_continuous x).tendsto t).eventually hz
    refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hev] with s hs
      simp only [Pi.zero_apply] at hs
      simp [hs]
    · simp [hζp, hgp]

/-- The normal component of the localized field is integrable on the half ball. -/
private lemma boundary_zero_trace_integrableOn {f ζ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContinuousOn f (ball 0 1 ∩ {x | 0 ≤ x (Fin.last 2)}))
    (hC1 : ContDiffOn ℝ 1 f (boundaryHalfBall 1))
    (hG : EqOn G (gradient f) (boundaryHalfBall 1))
    (hGi : IntegrableOn (fun x => ‖G x‖) (boundaryHalfBall 1))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ ball 0 1) :
    IntegrableOn (fun x => (ζ x • G x + f x • gradient ζ x) (Fin.last 2))
      (boundaryHalfBall 1) := by
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  obtain ⟨Cz, hCz⟩ := hcζ.exists_bound_of_continuous hζ.continuous
  have hcg : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _)
  obtain ⟨Cg, hCg⟩ := hcg.exists_bound_of_continuous (continuous_gradient_of_contDiff hζ)
  have hKc : IsCompact (tsupport ζ ∩ {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x (Fin.last 2)}) :=
    hcζ.isCompact.inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  obtain ⟨Cf, hCf⟩ := hKc.exists_bound_of_continuousOn
    (hf.mono (inter_subset_inter_left _ hsζ))
  let M : ℝ := max Cf 0 * max Cg 0
  have hcont : ContinuousOn (fun x => (ζ x • G x + f x • gradient ζ x) (Fin.last 2))
      (boundaryHalfBall 1) := by
    have hGc : ContinuousOn G (boundaryHalfBall 1) :=
      (continuousOn_gradient_of_contDiffOn hU hC1).congr hG
    exact (EuclideanSpace.proj (Fin.last 2)).continuous.comp_continuousOn
      ((hζ.continuous.continuousOn.smul hGc).add
        (hC1.continuousOn.smul (continuous_gradient_of_contDiff hζ).continuousOn))
  refine Integrable.mono' ((hGi.const_mul Cz).add
    (integrableOn_const (C := M) (boundaryHalfBall_volume_lt_top 1).ne))
    (hcont.aestronglyMeasurable hU.measurableSet) ?_
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  have h1 : ‖(ζ x • G x + f x • gradient ζ x) (Fin.last 2)‖ ≤
      ‖ζ x‖ * ‖G x‖ + ‖f x‖ * ‖gradient ζ x‖ := by
    refine (PiLp.norm_apply_le _ _).trans ?_
    simpa only [norm_smul] using norm_add_le (ζ x • G x) (f x • gradient ζ x)
  have h2 : ‖ζ x‖ * ‖G x‖ ≤ Cz * ‖G x‖ := mul_le_mul_of_nonneg_right (hCz x) (norm_nonneg _)
  have h3 : ‖f x‖ * ‖gradient ζ x‖ ≤ M := by
    by_cases hxs : x ∈ tsupport ζ
    · have hfx : ‖f x‖ ≤ max Cf 0 :=
        (hCf x ⟨hxs, le_of_lt (show 0 < x (Fin.last 2) from hx.2)⟩).trans (le_max_left _ _)
      exact mul_le_mul hfx ((hCg x).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
    · rw [gradient_eq_zero_of_notMem_tsupport hxs, norm_zero, mul_zero]
      exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  change _ ≤ Cz * ‖G x‖ + M
  linarith

/-- An integrable function on the half ball vanishing off the ball is integrable along almost
every normal unit segment. -/
private lemma boundary_zero_trace_ae_integrable {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : IntegrableOn F (boundaryHalfBall 1)) (hz : ∀ x, x ∉ ball 0 1 → F x = 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      Integrable (fun t => F (graphAppendN x t)) flatTraceInterval := by
  classical
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hI : Integrable (U.indicator F) := by
    have he : U.indicator F = (boundaryHalfBall 1).indicator F := by
      funext x
      by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1
      · by_cases hxU : x ∈ U
        · rw [indicator_of_mem hxU, indicator_of_mem (show x ∈ boundaryHalfBall 1 from ⟨hx, hxU⟩)]
        · rw [indicator_of_notMem hxU, indicator_of_notMem (fun h => hxU h.2)]
      · rw [indicator_apply, indicator_apply, hz x hx]
        simp
    rw [he, integrable_indicator_iff (isOpen_boundaryHalfBall 1).measurableSet]
    exact hF
  have hcomp := (graphAppendN_measurePreserving 2).integrable_comp_of_integrable hI
  have hle : volume.prod flatTraceInterval ≤
      (volume : Measure (EuclideanSpace ℝ (Fin 2))).prod volume :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hae := (hcomp.mono_measure hle).prod_right_ae
  have hpos : ∀ᵐ t ∂flatTraceInterval, 0 < t := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 :=
      compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [ae_restrict_of_ae h0,
      ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht htI
    exact lt_of_le_of_ne htI.1 (Ne.symm ht)
  filter_upwards [hae] with x hx
  refine hx.congr ?_
  filter_upwards [hpos] with t ht
  have htU : graphAppendN x t ∈ U := by
    change 0 < graphAppendN x t (Fin.last 2)
    rw [graphAppendN_last]
    exact ht
  simp only [Function.comp_apply, indicator_of_mem htU]

/-- The one-dimensional computation: the normal average of `g + (t - 1) g'` is `g 0`. -/
private lemma boundary_zero_trace_ftc {g h : ℝ → ℝ}
    (hc : ContinuousOn g (Icc 0 1)) (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (h t) t)
    (hi : IntegrableOn h (Icc 0 1)) :
    ∫ t in Icc (0 : ℝ) 1, (g t + (t - 1) * h t) = g 0 := by
  have hF : ContinuousOn (fun t => (t - 1) * g t) (Icc 0 1) :=
    (continuousOn_id.sub continuousOn_const).mul hc
  have hFd : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => (t - 1) * g t) (g t + (t - 1) * h t) t := by
    intro t ht
    have h1 := ((hasDerivAt_id t).sub_const 1).fun_mul (hd t ht)
    simpa only [id_eq, one_mul] using h1
  have hint : IntervalIntegrable (fun t => g t + (t - 1) * h t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hc.integrableOn_compact isCompact_Icc).add
      (hi.continuousOn_mul (continuousOn_id.sub continuousOn_const) isCompact_Icc)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF hFd hint
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, h]
  ring

/-- A function continuous on the upper part of the unit ball, C¹ in the open half ball with
integrable gradient `G`, and vanishing on the flat face has zero localized flat trace. -/
theorem hasZeroFlatTraceOn_of_continuousOn {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContinuousOn f (Metric.ball 0 1 ∩ {x | 0 ≤ x (Fin.last 2)}))
    (hC1 : ContDiffOn ℝ 1 f (boundaryHalfBall 1))
    (hG : Set.EqOn G (gradient f) (boundaryHalfBall 1))
    (hGi : IntegrableOn (fun x => ‖G x‖) (boundaryHalfBall 1))
    (hface : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, x (Fin.last 2) = 0 → f x = 0) :
    HasZeroFlatTraceOn f G (Metric.ball 0 1) := by
  intro ζ hζ hcζ hsζ
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hHi := boundary_zero_trace_integrableOn hf hC1 hG hGi hζ1 hcζ hsζ
  have hHz : ∀ x, x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 →
      (ζ x • G x + f x • gradient ζ x) (Fin.last 2) = 0 := by
    intro x hx
    have h1 : ζ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
    have h2 : gradient ζ x = 0 := gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
    simp [h1, h2]
  have hgc := boundary_zero_trace_continuousOn hf hζ.continuous hsζ
  filter_upwards [boundary_zero_trace_ae_integrable hHi hHz] with x hx
  have hcont : ContinuousOn (fun t => ζ (graphAppendN x t) * f (graphAppendN x t))
      (Icc 0 1) := by
    refine hgc.comp (boundary_zero_trace_segment_continuous x).continuousOn ?_
    intro t ht
    change 0 ≤ graphAppendN x t (Fin.last 2)
    rw [graphAppendN_last]
    exact ht.1
  have key := boundary_zero_trace_ftc hcont
    (fun t ht => boundary_zero_trace_hasDerivAt hC1 hG hζ1 hsζ x ht.1) hx
  have h0 : ζ (graphAppendN x 0) * f (graphAppendN x 0) = 0 := by
    by_cases hb : graphAppendN x 0 ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1
    · rw [hface _ hb (graphAppendN_last x 0), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hb (hsζ h)), zero_mul]
  exact key.trans h0

end LiquidDrop
