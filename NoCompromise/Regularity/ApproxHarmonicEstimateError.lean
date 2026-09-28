import NoCompromise.Regularity.ApproxHarmonicAlgebra
import NoCompromise.Sobolev.Extension

/-! # Integrated nonlinear graph error and bad-planar-set error -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- All graph flux integrands are genuinely integrable on bounded planar sets. -/
lemma integrableOn_approxHarmonic_flux
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A)
    {M : ℝ} (hM : 0 ≤ M) (hζ : ∀ p, ‖gradient ζ p‖ ≤ M) :
    IntegrableOn (fun p => inner ℝ (gradient f p) (gradient ζ p)) A volume ∧
      IntegrableOn (fun p => inner ℝ (gradient f p) (gradient ζ p) /
        Real.sqrt (1 + ‖gradient f p‖ ^ 2)) A volume ∧
      IntegrableOn (fun p => ‖gradient f p‖ ^ 2) A volume := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hA.measure_lt_top⟩
  have hm : Measurable (fun p => inner ℝ (gradient f p) (gradient ζ p)) :=
    (measurable_gradient f).inner (measurable_gradient ζ)
  have hb (p) : |inner ℝ (gradient f p) (gradient ζ p)| ≤ (K : ℝ) * M :=
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hζ p) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (norm_gradient_le_of_lipschitz hf p) hM))
  refine ⟨Integrable.of_bound hm.aestronglyMeasurable.restrict ((K : ℝ) * M)
    (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p), ?_, ?_⟩
  · have hq : Measurable (fun p => inner ℝ (gradient f p) (gradient ζ p) /
        Real.sqrt (1 + ‖gradient f p‖ ^ 2)) :=
      hm.div (measurable_const.add ((measurable_gradient f).norm.pow_const 2)).sqrt
    apply Integrable.of_bound hq.aestronglyMeasurable.restrict ((K : ℝ) * M)
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : 1 ≤ Real.sqrt (1 + ‖gradient f p‖ ^ 2) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith [sq_nonneg ‖gradient f p‖]
    exact (div_le_self (abs_nonneg _) hs).trans (hb p)
  · have hs : AEStronglyMeasurable (fun p => ‖gradient f p‖ ^ 2) volume :=
      ((measurable_gradient f).norm.pow_const 2).aestronglyMeasurable
    apply Integrable.of_bound hs.restrict ((K : ℝ) ^ 2)
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitz hf p) 2

/-- The actual graph flux differs from its linearization by the Dirichlet
energy times a uniform bound on the test gradient. -/
theorem approxHarmonic_integral_nonlinear_error
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : Bornology.IsBounded A) {M : ℝ} (hM : 0 ≤ M)
    (hζ : ∀ p, ‖gradient ζ p‖ ≤ M) :
    |(∫ p in A, inner ℝ (gradient f p) (gradient ζ p)) -
      ∫ p in A, inner ℝ (gradient f p) (gradient ζ p) /
        Real.sqrt (1 + ‖gradient f p‖ ^ 2)| ≤
      M * ∫ p in A, ‖gradient f p‖ ^ 2 := by
  obtain ⟨hi, hq, hs⟩ := integrableOn_approxHarmonic_flux hf hA hM hζ
  rw [← integral_sub hi hq]
  have hb := norm_integral_le_of_norm_le (hs.const_mul M) (ae_of_all _ fun p =>
    show ‖inner ℝ (gradient f p) (gradient ζ p) -
      inner ℝ (gradient f p) (gradient ζ p) / Real.sqrt (1 + ‖gradient f p‖ ^ 2)‖ ≤
      M * ‖gradient f p‖ ^ 2 from by
        rw [Real.norm_eq_abs]
        apply (approxHarmonic_nonlinear_error _ _
          ((norm_gradient_le_of_lipschitz hf p).trans hK)).trans
        nlinarith [mul_le_mul_of_nonneg_left (hζ p) (sq_nonneg ‖gradient f p‖)])
  simpa only [Real.norm_eq_abs, integral_const_mul] using hb

/-- The extension contribution over any bad planar set is bounded by its
actual volume times the two gradient bounds. -/
theorem approxHarmonic_bad_base_integral
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A)
    {M : ℝ} (hM : 0 ≤ M) (hζ : ∀ p, ‖gradient ζ p‖ ≤ M) :
    |∫ p in A, inner ℝ (gradient f p) (gradient ζ p)| ≤
      (K : ℝ) * M * volume.real A := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hA.measure_lt_top⟩
  have hb : ∀ᵐ p ∂volume.restrict A,
      ‖inner ℝ (gradient f p) (gradient ζ p)‖ ≤ (K : ℝ) * M := ae_of_all _ fun p => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hζ p) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (norm_gradient_le_of_lipschitz hf p) hM))
  have he := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ, mul_comm]
    using he

end LiquidDrop
