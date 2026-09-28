import NoCompromise.Regularity.CompressionJacobian
import NoCompromise.Variation.TransportC1

/-! # Perimeter transport under the genuine compression diffeomorphism -/

noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped ENNReal Gradient
namespace LiquidDrop

def verticalCompressionHomeomorph (β : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hβ : ContDiff ℝ 1 β) (hn : ∀ x, β x ≠ 0) (c : ℝ) :
    AmbientSpace ≃ₜ AmbientSpace where
  toFun := verticalCompression β c
  invFun := verticalCompression (fun x => (β x)⁻¹) c
  left_inv := verticalCompression_inverse β hn c
  right_inv := verticalCompression_inverse_right β hn c
  continuous_toFun := (contDiff_verticalCompression hβ c).continuous
  continuous_invFun := (contDiff_verticalCompression (hβ.inv hn) c).continuous

@[simp] lemma verticalCompressionHomeomorph_apply
    (β : EuclideanSpace ℝ (Fin 2) → ℝ) (hβ : ContDiff ℝ 1 β)
    (hn : ∀ x, β x ≠ 0) (c : ℝ) (x : AmbientSpace) :
    verticalCompressionHomeomorph β hβ hn c x = verticalCompression β c x := rfl

@[simp] lemma verticalCompressionHomeomorph_symm_apply
    (β : EuclideanSpace ℝ (Fin 2) → ℝ) (hβ : ContDiff ℝ 1 β)
    (hn : ∀ x, β x ≠ 0) (c : ℝ) (x : AmbientSpace) :
    (verticalCompressionHomeomorph β hβ hn c).symm x =
      verticalCompression (fun y => (β y)⁻¹) c x := rfl

lemma compressionBeta_ne_zero {σ τ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) : compressionBeta σ τ ε x ≠ 0 :=
  ne_of_gt (hε.trans_le (compressionBeta_bounds σ τ hε.le hε1 x).1)

/-- The compression preserves locally finite perimeter on the entire ambient space. -/
theorem hasLocallyFinitePerimeter_verticalCompression
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : ℝ) (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    HasLocallyFinitePerimeter (verticalCompression (compressionBeta σ τ ε) c '' E) := by
  let Φ := verticalCompressionHomeomorph (compressionBeta σ τ ε)
    (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c
  exact hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Φ
    (contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c)
    (contDiff_verticalCompression
      ((contDiff_compressionBeta hσ hst ε).inv (compressionBeta_ne_zero hε hε1)) c)
    E hE hmE

/-- A pointwise cofactor bound for the actual compression derivative. -/
lemma norm_compression_cofactor_le {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (c : ℝ) (x : AmbientSpace)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ‖cofactor3 (fderiv ℝ (verticalCompression (compressionBeta σ τ ε) c) x) ν‖ ≤
      1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2 := by
  rw [compression_cofactor hσ hst]
  have hu : ‖graphProjectionN 2 ν‖ ^ 2 + (ν 2) ^ 2 = 1 := by
    simpa only [hν, one_pow, show (Fin.last 2 : Fin 3) = 2 from rfl] using
      (norm_sq_graphProjectionN ν).symm
  have hb := compressionBeta_bounds σ τ hε hε1 (graphProjectionN 2 x)
  have hs := compression_normal_sq_le (t := x 2 - c) (hε.trans hb.1) hb.2
    (div_nonneg (sq_nonneg Real.pi) (sq_nonneg (τ - σ)))
    (compressionBeta_gradient_bound hσ hst hε hε1 (graphProjectionN 2 x)) hu
  rw [← norm_graphAppendN_sq] at hs
  have hnonneg : 0 ≤ Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2 := by positivity
  have heq : Real.pi ^ 2 / (τ - σ) ^ 2 * (x 2 - c) ^ 2 =
      Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2 := by ring
  rw [heq] at hs
  nlinarith [sq_nonneg (‖graphAppendN
    (compressionBeta σ τ ε (graphProjectionN 2 x) • graphProjectionN 2 ν -
      ((x 2 - c) * ν 2) • gradient (compressionBeta σ τ ε) (graphProjectionN 2 x))
    (ν 2)‖ - (1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2))]

/-- The genuine perimeter of the compressed set is controlled by the source
perimeter and its quadratic height moment, on every Borel image. -/
theorem perimeter_verticalCompression_le
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
      ∫⁻ x in A ∩ reducedBoundary E hE hmE,
        ENNReal.ofReal (1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2)
          ∂hausdorffMeasure2 3 := by
  let Φ := verticalCompressionHomeomorph (compressionBeta σ τ ε)
    (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c
  have heq := perimeter_transport_of_C1_diffeomorphism Φ
    (contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c)
    (contDiff_verticalCompression
      ((contDiff_compressionBeta hσ hst ε).inv (compressionBeta_ne_zero hε hε1)) c)
    E hE hmE hF hmF hA
  change canonicalPerimeterMeasure
    (verticalCompression (compressionBeta σ τ ε) c '' E) hF hmF
    (verticalCompression (compressionBeta σ τ ε) c '' A) = _ at heq
  rw [heq]
  apply setLIntegral_mono' (hA.inter (measurableSet_reducedBoundary E hE hmE))
  intro x hx
  exact ENNReal.ofReal_le_ofReal
    (norm_compression_cofactor_le hσ hst hε.le hε1 c x
      (norm_reducedNormal E hE hmE hx.2))

end LiquidDrop
