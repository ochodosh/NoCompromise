module

public import NoCompromise.Sobolev.W11Bounds
public import NoCompromise.Sobolev.W11TraceApprox
public import NoCompromise.Sobolev.H1TraceChart

@[expose] public section

/-!
# L¹ boundary estimates in a bi-Lipschitz chart

The actual continuous boundary restriction agrees almost everywhere with the
normal-average trace. Hausdorff distortion transfers its L¹ estimate from the
parameter plane to the chart surface.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

theorem memLp_chart_restrict_of_continuous_w11 {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasW11GradientOn f G univ) (hc : Continuous f) :
    MemLp (fun x => f (e (graphAppendN x 0))) 1 volume ∧
      lpNorm (fun x => f (e (graphAppendN x 0))) 1 volume ≤
        (max 1 (C : ℝ) * (K : ℝ) ^ (k + 1)) *
          (lpNorm f 1 volume + lpNorm G 1 volume) := by
  have hp := hf.comp_homeomorph_on_lpNorm isOpen_univ isOpen_univ e he hi
    (fun _ _ => mem_univ _)
  have hmf : MemLp (f ∘ e) 1 volume := by
    simpa only [Measure.restrict_univ] using hp.1.memLp_function
  have hmG : MemLp (fun x => (fderiv ℝ e x).adjoint (G (e x))) 1 volume := by
    simpa only [Measure.restrict_univ] using hp.1.memLp_gradient
  have ht := integrable_flatTraceFunction (memLp_one_iff_integrable.mp hmf)
    (memLp_one_iff_integrable.mp hmG)
  have heq := flatTraceFunction_eq_restrict_ae_of_continuous_w11 hp.1 (hc.comp e.continuous)
  have hm := memLp_one_iff_integrable.mpr (ht.1.congr heq)
  simp only [Function.comp_def] at hm heq ht hmf
  refine ⟨hm, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae heq, toReal_eLpNorm]
  have hb : lpNorm (flatTraceFunction (fun x => f (e x))
      (fun x => (fderiv ℝ e x).adjoint (G (e x)))) 1 volume ≤
      lpNorm (fun x => f (e x)) 1 volume +
      lpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 1 volume := by
    rw [lpNorm_one_eq_integral_norm ht.1.1, lpNorm_one_eq_integral_norm hmf.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hmG.aestronglyMeasurable]
    exact ht.2
  exact hb.trans (by simpa only [Measure.restrict_univ, Function.comp_def] using hp.2)

lemma memLp_one_surface_of_lipschitz_parameter {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hp : LipschitzWith C p) (hm : MeasurableEmbedding p)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : MemLp (f ∘ p) 1 volume) :
    MemLp f 1 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) ∧
      lpNorm f 1 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) ≤
        (C : ℝ) ^ k * lpNorm (f ∘ p) 1 volume := by
  let ν : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.euclideanHausdorffMeasure k).comap p
  have hle := normalizedHausdorffMeasure_comap_le hp hm
  have hc : (C : ℝ≥0∞) ^ k ≠ ∞ := by finiteness
  have hmem : MemLp (f ∘ p) 1 ν := (hf.smul_measure hc).mono_measure hle
  have hsurface : MemLp f 1 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) := by
    rw [← hm.map_comap]
    exact hm.memLp_map_measure_iff.mpr hmem
  refine ⟨hsurface, ?_⟩
  rw [lpNorm_one_eq_integral_norm hsurface.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hf.aestronglyMeasurable, ← hm.map_comap, hm.integral_map]
  have hibig := (memLp_one_iff_integrable.mp hf).norm.smul_measure hc
  calc
    _ ≤ ∫ x, ‖f (p x)‖ ∂((C : ℝ≥0∞) ^ k • volume) :=
      integral_mono_measure hle (Eventually.of_forall fun _ => norm_nonneg _) hibig
    _ = _ := by rw [integral_smul_measure]; simp only [ENNReal.toReal_pow,
      ENNReal.coe_toReal, smul_eq_mul, Function.comp_def]

theorem memLp_chart_surface_of_continuous_w11 {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasW11GradientOn f G univ) (hc : Continuous f) :
    MemLp f 1 ((Measure.euclideanHausdorffMeasure k).restrict
      (range (fun x => e (graphAppendN x 0)))) ∧
      lpNorm f 1 ((Measure.euclideanHausdorffMeasure k).restrict
        (range (fun x => e (graphAppendN x 0)))) ≤
      (C : ℝ) ^ k *
        ((max 1 (C : ℝ) * (K : ℝ) ^ (k + 1)) *
          (lpNorm f 1 volume + lpNorm G 1 volume)) := by
  have hp : LipschitzWith C (fun x => e (graphAppendN x 0)) := by
    simpa only [graphAppendN, zero_smul, add_zero, Function.comp_def, mul_one] using
      he.comp (isometry_graphBaseN k).lipschitzWith
  have hm : MeasurableEmbedding (fun x => e (graphAppendN x 0)) := by
    simpa only [graphAppendN, zero_smul, add_zero, Function.comp_def] using
      e.isClosedEmbedding.measurableEmbedding.comp
        (isometry_graphBaseN k).isClosedEmbedding.measurableEmbedding
  obtain ⟨hparam, hb⟩ := memLp_chart_restrict_of_continuous_w11 e he hi hf hc
  obtain ⟨hmem, hbound⟩ := memLp_one_surface_of_lipschitz_parameter hp hm hparam
  refine ⟨hmem, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg C.coe_nonneg k)
  exact hb

end LiquidDrop
