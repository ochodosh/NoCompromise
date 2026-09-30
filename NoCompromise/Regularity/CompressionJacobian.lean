module

public import NoCompromise.Regularity.CompressionProfileTheorem
public import NoCompromise.Regularity.CompressionEstimate
public import NoCompromise.Regularity.CompressionBilipschitz

@[expose] public section

/-! # The actual compression Jacobian and inverse, blueprint lemma -/

noncomputable section
open Set InnerProductSpace Metric
open scoped Gradient NNReal
namespace LiquidDrop

lemma compression_differential {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) (ε c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (verticalCompression (compressionBeta σ τ ε) c)
      (compressionLinear (compressionBeta σ τ ε (graphProjectionN 2 x)) (x 2 - c)
        (gradient (compressionBeta σ τ ε) (graphProjectionN 2 x))) x :=
  hasFDerivAt_verticalCompression
    (((contDiff_compressionBeta hσ h ε).differentiable (by norm_num) _).hasGradientAt)

/-- Exact cofactor formula for the genuine derivative, with no assumed derivative
matrix or supplied area estimate. -/
theorem compression_cofactor {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) (ε c : ℝ)
    (x ν : EuclideanSpace ℝ (Fin 3)) :
    cofactor3 (fderiv ℝ (verticalCompression (compressionBeta σ τ ε) c) x) ν =
      graphAppendN
        (compressionBeta σ τ ε (graphProjectionN 2 x) • graphProjectionN 2 ν -
          ((x 2 - c) * ν 2) • gradient (compressionBeta σ τ ε) (graphProjectionN 2 x))
        (ν 2) := by
  rw [(compression_differential hσ h ε c x).fderiv, cofactor3_compressionLinear]

/-- The exact squared plane Jacobian and the universal quadratic area bound. -/
theorem compression_jacobian {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) {ν : EuclideanSpace ℝ (Fin 3)} (hν : ‖ν‖ = 1)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    let J := jacobian2Linear ((fderiv ℝ (verticalCompression (compressionBeta σ τ ε) c) x).comp
      (normalPlaneInclusion ν e).toContinuousLinearMap)
    J ^ 2 = ‖compressionBeta σ τ ε (graphProjectionN 2 x) • graphProjectionN 2 ν -
      ((x 2 - c) * ν 2) • gradient (compressionBeta σ τ ε) (graphProjectionN 2 x)‖ ^ 2 +
      (ν 2) ^ 2 ∧ J ≤ 1 + Real.pi ^ 2 * (x 2 - c) ^ 2 / (τ - σ) ^ 2 := by
  dsimp only
  rw [(compression_differential hσ h ε c x).fderiv]
  refine ⟨compression_jacobian_sq _ _ _ hν e, ?_⟩
  have hb := compressionBeta_bounds σ τ hε hε1 (graphProjectionN 2 x)
  have he := compression_jacobian_bound (hε.trans hb.1) hb.2
    (div_nonneg (sq_nonneg Real.pi) (sq_nonneg (τ - σ))) (x 2 - c)
    (compressionBeta_gradient_bound hσ h hε hε1 (graphProjectionN 2 x)) hν e
  convert he using 1
  ring

/-- Both maps are globally C¹ inverses. On every bounded set, hence on each
transition annulus inside a finite-height cylinder, both Lipschitz bounds hold. -/
theorem compression_inverse_and_bilipschitz {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) :
    let T := verticalCompression (compressionBeta σ τ ε) c
    let I := verticalCompression (fun y => (compressionBeta σ τ ε y)⁻¹) c
    ContDiff ℝ 1 T ∧ ContDiff ℝ 1 I ∧
      Function.LeftInverse I T ∧ Function.RightInverse I T ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin 3)), Bornology.IsBounded S →
        ∃ L M : ℝ≥0, LipschitzOnWith L T S ∧
          ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ M * dist (T x) (T y) := by
  have hn (x : EuclideanSpace ℝ (Fin 2)) : compressionBeta σ τ ε x ≠ 0 :=
    ne_of_gt (hε.trans_le (compressionBeta_bounds σ τ hε.le hε1 x).1)
  have hc := contDiff_compressionBeta hσ h ε
  exact ⟨contDiff_verticalCompression hc c, contDiff_verticalCompression (hc.inv hn) c,
    verticalCompression_inverse _ hn c, verticalCompression_inverse_right _ hn c,
    fun _ hS => verticalCompression_bilipschitz_on_bounded hc hn c hS⟩

end LiquidDrop
