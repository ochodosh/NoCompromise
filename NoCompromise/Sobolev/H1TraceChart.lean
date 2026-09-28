import NoCompromise.Sobolev.H1TraceContinuous
import NoCompromise.Sobolev.H1Chain
import Mathlib.MeasureTheory.Measure.Comap

/-!
# H¹ traces in bi-Lipschitz coordinates

The chart trace is the constructed flat trace applied to the actual H¹ pullback.
Its bound depends only on the Lipschitz constants of the chart and its inverse.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Linear pullback on scalar representatives. -/
def h1ChartPullback {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun f := f ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quantitative weak chain rule bounds actual chart pullback. -/
lemma h1ChartPullback_bound {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G univ) :
    ∃ H, HasH1GradientOn (h1ChartPullback e f) H univ ∧
      lpNorm (h1ChartPullback e f) 2 (volume.restrict univ) +
        lpNorm H 2 (volume.restrict univ) ≤
          (max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) *
            (lpNorm f 2 (volume.restrict univ) + lpNorm G 2 (volume.restrict univ)) := by
  have h := hf.comp_homeomorph_on_lpNorm isOpen_univ isOpen_univ e he hi
    (fun _ _ => mem_univ _)
  exact ⟨_, h⟩

namespace H1Space

/-- The genuine H¹ pullback operator for a bi-Lipschitz homeomorphism. -/
def chartPullbackCLM {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    H1Space (univ : Set (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      H1Space (univ : Set (EuclideanSpace ℝ (Fin n))) :=
  liftBoundedLinearMap isOpen_univ (h1ChartPullback e)
    (max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) (by positivity)
    (h1ChartPullback_bound e he hi) isOpen_univ

lemma norm_chartPullbackCLM_le {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    ‖chartPullbackCLM e he hi‖ ≤ 2 * (max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) :=
  norm_liftBoundedLinearMap_le isOpen_univ (h1ChartPullback e)
    (max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) (by positivity)
    (h1ChartPullback_bound e he hi) isOpen_univ

lemma chartPullbackCLM_ofFunction {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) :
    chartPullbackCLM e he hi (ofFunction f G hf) =
      ofFunction (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x)))
        (hf.comp_homeomorph e he hi).1 := by
  rw [chartPullbackCLM, liftBoundedLinearMap_ofFunction]
  apply ext_ae isOpen_univ
  exact (coeFn_ofH1Function _ _).trans (coeFn_ofFunction _ _ _).symm

/-- The L² trace in the base coordinates of a bi-Lipschitz chart. -/
def chartTraceCLM {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    H1Space (univ : Set (EuclideanSpace ℝ (Fin (k + 1)))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
  (flatTraceCLM k).comp (chartPullbackCLM e he hi)

lemma norm_chartTraceCLM_le {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    ‖chartTraceCLM e he hi‖ ≤
      4 * (max 1 (C : ℝ) * (K : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2)) := by
  calc
    _ ≤ ‖flatTraceCLM k‖ * ‖chartPullbackCLM e he hi‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (2 * (max 1 (C : ℝ) * (K : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2))) :=
      mul_le_mul (norm_flatTraceCLM_le k) (norm_chartPullbackCLM_le e he hi)
        (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Continuous H¹ representatives have their actual pointwise boundary values
in every bi-Lipschitz chart, without differentiability assumptions on that chart. -/
lemma coeFn_chartTraceCLM_of_continuous {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    ⇑(chartTraceCLM e he hi (ofFunction f G hf)) =ᵐ[volume]
      (fun x => f (e (graphAppendN x 0))) := by
  change ⇑(chartPullbackCLM e he hi (ofFunction f G hf)).flatTrace =ᵐ[volume] _
  rw [chartPullbackCLM_ofFunction e he hi hf]
  exact coeFn_flatTrace_of_continuous (hf.comp_homeomorph e he hi).1 (hc.comp e.continuous)

end H1Space

/-- Restriction of continuous H¹ representatives to a chart plane is L², with
an explicit bound in the base coordinates. -/
theorem memLp_chart_restrict_of_continuous_h1 {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    MemLp (fun x => f (e (graphAppendN x 0))) 2 volume ∧
      lpNorm (fun x => f (e (graphAppendN x 0))) 2 volume ≤
        (max 1 (C : ℝ) * (K : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2)) *
          (lpNorm f 2 volume + lpNorm G 2 volume) := by
  have hp := hf.comp_homeomorph_on_lpNorm isOpen_univ isOpen_univ e he hi
    (fun _ _ => mem_univ _)
  have hmf : MemLp (f ∘ e) 2 volume := by
    simpa only [Measure.restrict_univ] using hp.1.memLp_function
  have hmG : MemLp (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 volume := by
    simpa only [Measure.restrict_univ] using hp.1.memLp_gradient
  have ht := memLp_flatTraceFunction hmf hmG
  have heq := flatTraceFunction_eq_restrict_ae_of_continuous hp.1 (hc.comp e.continuous)
  have hm := ht.1.ae_eq heq
  simp only [Function.comp_def] at hm heq ht
  refine ⟨hm, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae heq, toReal_eLpNorm]
  exact ht.2.trans (by simpa only [Measure.restrict_univ, Function.comp_def] using hp.2)

/-- A Lipschitz parametrization distorts normalized Hausdorff measure by its
Lipschitz constant to the source dimension. -/
lemma normalizedHausdorffMeasure_image_le_lipschitz {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hp : LipschitzWith C p) (S : Set (EuclideanSpace ℝ (Fin k))) :
    Measure.euclideanHausdorffMeasure k (p '' S) ≤ (C : ℝ≥0∞) ^ k * volume S := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume k]
  simp_rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul' le_rfl
      (hp.lipschitzOnWith.hausdorffMeasure_image_le (d := k) (by positivity))
    _ = _ := by rw [ENNReal.rpow_natCast]; ac_rfl

/-- Hausdorff measure pulled back to an embedded Lipschitz parameter domain is
bounded above by a constant multiple of Lebesgue measure. -/
lemma normalizedHausdorffMeasure_comap_le {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hp : LipschitzWith C p) (hm : MeasurableEmbedding p) :
    (Measure.euclideanHausdorffMeasure k).comap p ≤ (C : ℝ≥0∞) ^ k • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.comap_apply _ hm.injective (fun _ h => hm.measurableSet_image.mpr h) _ hS,
    Measure.smul_apply, smul_eq_mul]
  exact normalizedHausdorffMeasure_image_le_lipschitz hp S

/-- Parametric L² control bounds actual normalized Hausdorff L² restriction.
The squared norm formulation keeps the exact surface distortion factor. -/
lemma memLp_surface_of_lipschitz_parameter {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hp : LipschitzWith C p) (hm : MeasurableEmbedding p)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : MemLp (f ∘ p) 2 volume) :
    MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) ∧
      lpNorm f 2 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) ^ 2 ≤
        (C : ℝ) ^ k * lpNorm (f ∘ p) 2 volume ^ 2 := by
  let ν : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.euclideanHausdorffMeasure k).comap p
  have hle := normalizedHausdorffMeasure_comap_le hp hm
  have hc : (C : ℝ≥0∞) ^ k ≠ ∞ := by finiteness
  have hmem : MemLp (f ∘ p) 2 ν := (hf.smul_measure hc).mono_measure hle
  have hsurface : MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (range p)) := by
    rw [← hm.map_comap]
    exact hm.memLp_map_measure_iff.mpr hmem
  refine ⟨hsurface, ?_⟩
  rw [lpNorm_two_sq_eq_integral_norm_sq hsurface,
    lpNorm_two_sq_eq_integral_norm_sq hf, ← hm.map_comap,
    hm.integral_map]
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hibig := hi.smul_measure hc
  calc
    _ ≤ ∫ x, ‖f (p x)‖ ^ 2 ∂((C : ℝ≥0∞) ^ k • volume) :=
      integral_mono_measure hle (Eventually.of_forall fun _ => sq_nonneg _) hibig
    _ = _ := by rw [integral_smul_measure]; simp only [ENNReal.toReal_pow,
      ENNReal.coe_toReal, smul_eq_mul, Function.comp_def]

lemma isometry_graphBaseN (k : ℕ) : Isometry (graphBaseN k) := by
  have hnorm (x : EuclideanSpace ℝ (Fin k)) : ‖graphBaseN k x‖ = ‖x‖ := by
    have hproj : graphProjectionN k (graphBaseN k x) = x := by ext i; simp
    have h := norm_sq_graphProjectionN (graphBaseN k x)
    rw [hproj, graphBaseN_last, zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, ← map_sub, hnorm]

/-- The actual Hausdorff L² bound on the complete image of a chart plane. -/
theorem memLp_chart_surface_of_continuous_h1 {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hc : Continuous f) :
    MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict
      (range (fun x => e (graphAppendN x 0)))) ∧
      lpNorm f 2 ((Measure.euclideanHausdorffMeasure k).restrict
        (range (fun x => e (graphAppendN x 0)))) ^ 2 ≤
      (C : ℝ) ^ k *
        ((max 1 (C : ℝ) * (K : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2)) *
          (lpNorm f 2 volume + lpNorm G 2 volume)) ^ 2 := by
  have hp : LipschitzWith C (fun x => e (graphAppendN x 0)) := by
    simpa only [graphAppendN, zero_smul, add_zero, Function.comp_def, mul_one] using
      he.comp (isometry_graphBaseN k).lipschitzWith
  have hm : MeasurableEmbedding (fun x => e (graphAppendN x 0)) := by
    simpa only [graphAppendN, zero_smul, add_zero, Function.comp_def] using
      e.isClosedEmbedding.measurableEmbedding.comp
        (isometry_graphBaseN k).isClosedEmbedding.measurableEmbedding
  obtain ⟨hparam, hb⟩ := memLp_chart_restrict_of_continuous_h1 e he hi hf hc
  obtain ⟨hmem, hbound⟩ := memLp_surface_of_lipschitz_parameter hp hm hparam
  refine ⟨hmem, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg C.coe_nonneg k)
  exact pow_le_pow_left₀ lpNorm_nonneg hb 2

end LiquidDrop
