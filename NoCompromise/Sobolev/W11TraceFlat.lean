module

public import NoCompromise.Sobolev.H1Trace

@[expose] public section

/-!
# The L¹ normal-average trace

The flat normal-average formula is bounded in L¹ by the L¹ norms of the
function and its weak gradient. For smooth functions it is actual restriction
to the boundary plane, by the one-dimensional fundamental theorem of calculus.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient
namespace LiquidDrop

structure HasW11GradientOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop extends HasWeakGradientOn f G U where
  integrable_function : IntegrableOn f U
  integrable_gradient : IntegrableOn G U

lemma integrable_graphAppendN {k : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin (k + 1)) → F} (hf : Integrable f) :
    Integrable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (graphAppendN p.1 p.2))
      (volume.prod flatTraceInterval) ∧
    (∫ p : EuclideanSpace ℝ (Fin k) × ℝ, ‖f (graphAppendN p.1 p.2)‖
        ∂volume.prod flatTraceInterval) ≤ ∫ x, ‖f x‖ := by
  have hmp := graphAppendN_measurePreserving k
  have hfull := hmp.integrable_comp_of_integrable hf
  have hle : volume.prod flatTraceInterval ≤
      (volume : Measure (EuclideanSpace ℝ (Fin k))).prod volume :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  refine ⟨hfull.mono_measure hle, ?_⟩
  have hm := hf.norm.aestronglyMeasurable
  rw [← hmp.map_eq] at hm
  have heq := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at heq
  exact (integral_mono_measure hle (Eventually.of_forall fun _ => norm_nonneg _)
    hfull.norm).trans_eq heq.symm

lemma integrable_flatTraceIntegrand {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : Integrable f) (hG : Integrable G) :
    Integrable (flatTraceIntegrand f G) (volume.prod flatTraceInterval) ∧
    (∫ p, ‖flatTraceIntegrand f G p‖ ∂volume.prod flatTraceInterval) ≤
      (∫ x, ‖f x‖) + ∫ x, ‖G x‖ := by
  obtain ⟨hif, hbf⟩ := integrable_graphAppendN hf
  obtain ⟨hiG, hbG⟩ := integrable_graphAppendN hG
  let g := fun p : EuclideanSpace ℝ (Fin k) × ℝ =>
    (p.2 - 1) * G (graphAppendN p.1 p.2) (Fin.last k)
  have hmg : AEStronglyMeasurable g (volume.prod flatTraceInterval) :=
    (measurable_snd.sub measurable_const).aestronglyMeasurable.mul
      ((EuclideanSpace.proj (Fin.last k)).continuous.comp_aestronglyMeasurable hiG.1)
  have hb : ∀ᵐ p ∂(volume : Measure (EuclideanSpace ℝ (Fin k))).prod flatTraceInterval,
      ‖g p‖ ≤ ‖G (graphAppendN p.1 p.2)‖ := by
    have ht := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) (ν := flatTraceInterval)).ae
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1) measurableSet_Icc)
    filter_upwards [ht] with p hp
    have habs : |p.2 - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    calc
      ‖g p‖ = |p.2 - 1| * ‖G (graphAppendN p.1 p.2) (Fin.last k)‖ := norm_mul _ _
      _ ≤ 1 * ‖G (graphAppendN p.1 p.2) (Fin.last k)‖ :=
        mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ ≤ ‖G (graphAppendN p.1 p.2)‖ := by
        simpa only [one_mul] using PiLp.norm_apply_le (G (graphAppendN p.1 p.2)) (Fin.last k)
  have hig : Integrable g (volume.prod flatTraceInterval) := hiG.norm.mono' hmg hb
  have hii : Integrable (flatTraceIntegrand f G) (volume.prod flatTraceInterval) := hif.add hig
  refine ⟨hii, ?_⟩
  calc
    _ ≤ ∫ p, ‖f (graphAppendN p.1 p.2)‖ + ‖G (graphAppendN p.1 p.2)‖
        ∂volume.prod flatTraceInterval := integral_mono_ae hii.norm (hif.norm.add hiG.norm)
      (hb.mono fun p hp => (norm_add_le _ _).trans (add_le_add_right hp _))
    _ = (∫ p, ‖f (graphAppendN p.1 p.2)‖ ∂volume.prod flatTraceInterval) +
        ∫ p, ‖G (graphAppendN p.1 p.2)‖ ∂volume.prod flatTraceInterval :=
      integral_add hif.norm hiG.norm
    _ ≤ _ := add_le_add hbf hbG

theorem integrable_flatTraceFunction {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : Integrable f) (hG : Integrable G) :
    Integrable (flatTraceFunction f G) ∧
      (∫ x, ‖flatTraceFunction f G x‖) ≤ (∫ x, ‖f x‖) + ∫ x, ‖G x‖ := by
  obtain ⟨hi, hb⟩ := integrable_flatTraceIntegrand hf hG
  refine ⟨hi.integral_prod_left, ?_⟩
  calc
    _ ≤ ∫ x, ∫ t, ‖flatTraceIntegrand f G (x, t)‖ ∂flatTraceInterval :=
      integral_mono_ae hi.integral_prod_left.norm hi.integral_norm_prod_left
        (Eventually.of_forall fun _ => norm_integral_le_integral_norm _)
    _ = ∫ p, ‖flatTraceIntegrand f G p‖ ∂volume.prod flatTraceInterval :=
      (integral_prod _ hi.norm).symm
    _ ≤ _ := hb

theorem integrable_restrict_plane_of_contDiff_w11 {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hf : ContDiff ℝ 1 f)
    (hif : Integrable f) (hiG : Integrable (gradient f)) :
    Integrable (fun x => f (graphAppendN x 0)) ∧
      (∫ x, ‖f (graphAppendN x 0)‖) ≤ (∫ x, ‖f x‖) + ∫ x, ‖gradient f x‖ := by
  simpa only [funext (flatTraceFunction_eq_restrict_of_contDiff hf)] using
    integrable_flatTraceFunction hif hiG

end LiquidDrop
