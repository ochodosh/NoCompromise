import NoCompromise.Regularity.DeformationCompression

/-! # The compression bound in terms of the actual source perimeter measure -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LiquidDrop

lemma lintegral_compression_weight (μ : Measure AmbientSpace) (A : Set AmbientSpace)
    (σ τ c : ℝ) :
    (∫⁻ x in A, ENNReal.ofReal (1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2) ∂μ) =
      μ A + ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
        ∫⁻ x in A, ENNReal.ofReal ((x 2 - c) ^ 2) ∂μ := by
  have hk : 0 ≤ Real.pi ^ 2 / (τ - σ) ^ 2 := by positivity
  have he (x : AmbientSpace) :
      ENNReal.ofReal (1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2) =
        1 + ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ENNReal.ofReal ((x 2 - c) ^ 2) := by
    have hr : Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2 =
        (Real.pi ^ 2 / (τ - σ) ^ 2) * (x 2 - c) ^ 2 := by ring
    rw [hr, ENNReal.ofReal_add zero_le_one (mul_nonneg hk (sq_nonneg _)),
      ENNReal.ofReal_one, ENNReal.ofReal_mul hk]
  simp_rw [he]
  rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, one_mul, Measure.restrict_apply_univ]

theorem perimeter_verticalCompression_le_source_measure
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℝ) (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter
      (verticalCompression (compressionBeta σ τ ε) c '' E))
    (hmF : NullMeasurableSet
      (verticalCompression (compressionBeta σ τ ε) c '' E) volume)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (verticalCompression (compressionBeta σ τ ε) c '' E) hF hmF
      (verticalCompression (compressionBeta σ τ ε) c '' A) ≤
      canonicalPerimeterMeasure E hE hmE A +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in A, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  rw [← lintegral_compression_weight]
  have hbound := perimeter_verticalCompression_le hσ hst hε hε1 c E hE hmE hF hmF hA
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    Measure.restrict_restrict hA]
  exact hbound

end LiquidDrop
