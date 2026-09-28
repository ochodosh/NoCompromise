import NoCompromise.Sobolev.H1TraceChart

/-!
# The reverse measure comparison for boundary charts

A Lipschitz left inverse bounds parameter volume by surface measure. This is
the direction needed to recover a flat trace from the domain boundary trace.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma normalizedHausdorffMeasure_image_le_lipschitz_dim {n m k : ℕ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {K : ℝ≥0}
    (hq : LipschitzWith K q) (S : Set (EuclideanSpace ℝ (Fin n))) :
    Measure.euclideanHausdorffMeasure k (q '' S) ≤
      (K : ℝ≥0∞) ^ k * Measure.euclideanHausdorffMeasure k S := by
  simp_rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul' le_rfl
      (hq.lipschitzOnWith.hausdorffMeasure_image_le (d := k) (by positivity))
    _ = _ := by rw [ENNReal.rpow_natCast]; ac_rfl

lemma volume_le_smul_normalizedHausdorffMeasure_comap {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {q : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k)} {K : ℝ≥0}
    (hm : MeasurableEmbedding p) (hq : LipschitzWith K q)
    (hqp : Function.LeftInverse q p) :
    volume ≤ (K : ℝ≥0∞) ^ k • (Measure.euclideanHausdorffMeasure k).comap p := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.comap_apply _ hm.injective (fun _ h => hm.measurableSet_image.mpr h) _ hS]
  have himage : q '' (p '' S) = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [hqp y] using hy
    · intro hx
      exact ⟨p x, mem_image_of_mem p hx, hqp x⟩
  have h := normalizedHausdorffMeasure_image_le_lipschitz_dim (k := k) hq (p '' S)
  simpa only [himage, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using h

/-- Surface L² control bounds the true parameter L² norm when the
parametrization admits a Lipschitz left inverse. -/
lemma memLp_parameter_of_lipschitz_inverse {k m : ℕ}
    {p : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {q : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k)} {K : ℝ≥0}
    (hm : MeasurableEmbedding p) (hq : LipschitzWith K q)
    (hqp : Function.LeftInverse q p) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (range p))) :
    MemLp (f ∘ p) 2 volume ∧
      lpNorm (f ∘ p) 2 volume ^ 2 ≤
        (K : ℝ) ^ k * lpNorm f 2
          ((Measure.euclideanHausdorffMeasure k).restrict (range p)) ^ 2 := by
  let ν := (Measure.euclideanHausdorffMeasure k).comap p
  have hle := volume_le_smul_normalizedHausdorffMeasure_comap hm hq hqp
  have hc : (K : ℝ≥0∞) ^ k ≠ ∞ := by finiteness
  have hfν : MemLp (f ∘ p) 2 ν := by
    rw [← hm.map_comap] at hf
    exact hm.memLp_map_measure_iff.mp hf
  have hmem : MemLp (f ∘ p) 2 volume := (hfν.smul_measure hc).mono_measure hle
  refine ⟨hmem, ?_⟩
  rw [lpNorm_two_sq_eq_integral_norm_sq hmem, lpNorm_two_sq_eq_integral_norm_sq hf,
    ← hm.map_comap, hm.integral_map]
  have hi := (memLp_two_iff_integrable_sq_norm hfν.aestronglyMeasurable).mp hfν
  calc
    _ ≤ ∫ x, ‖f (p x)‖ ^ 2 ∂((K : ℝ≥0∞) ^ k • ν) :=
      integral_mono_measure hle (Eventually.of_forall fun _ => sq_nonneg _)
        (hi.smul_measure hc)
    _ = _ := by rw [integral_smul_measure]; simp only [ENNReal.toReal_pow,
      ENNReal.coe_toReal, smul_eq_mul, ν]

end LiquidDrop
