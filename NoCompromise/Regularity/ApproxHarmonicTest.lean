module

public import NoCompromise.Regularity.FluxDefectTests
public import NoCompromise.Regularity.FirstVariation
public import NoCompromise.Area.Graph

@[expose] public section

/-! # Vertical test fields for the graph first variation -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma tangentialDivergence_neg_normal (X ν : AmbientSpace → AmbientSpace) (z : AmbientSpace) :
    tangentialDivergence X (fun x => -ν x) z = tangentialDivergence X ν z := by
  simp [tangentialDivergence]

lemma fderiv_vertical_tensor_apply
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hψ : ContDiff ℝ 1 ψ) (z v : AmbientSpace) :
    fderiv ℝ (fun x : AmbientSpace => ζ (graphProjectionN 2 x) * ψ (x 2)) z v =
      ψ (z 2) * fderiv ℝ ζ (graphProjectionN 2 z) (graphProjectionN 2 v) +
        ζ (graphProjectionN 2 z) * deriv ψ (z 2) * v 2 := by
  have hz := ((hζ.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp z
    (graphProjectionN 2).hasFDerivAt
  have hp := ((hψ.differentiable one_ne_zero).differentiableAt.hasDerivAt).comp_hasFDerivAt z
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).hasFDerivAt
  change (fderiv ℝ ((ζ ∘ graphProjectionN 2) *
    (ψ ∘ (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ))) z) v = _
  rw [(hz.mul hp).fderiv]
  simp [ContinuousLinearMap.comp_apply, EuclideanSpace.proj,
    mul_assoc, mul_comm, mul_left_comm, add_comm]

/-- At a height where the cutoff is flat, the tangential derivative has the
usual vertical-variation form, for either choice of normal orientation. -/
lemma tangentialDivergence_vertical_tensor
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hψ : ContDiff ℝ 1 ψ)
    (ν : AmbientSpace → AmbientSpace) (z : AmbientSpace)
    (hp : ψ (z 2) = 1) (hdp : deriv ψ (z 2) = 0) :
    tangentialDivergence
      (fun x : AmbientSpace => (ζ (graphProjectionN 2 x) * ψ (x 2)) •
        EuclideanSpace.single 2 1) ν z =
      -(ν z 2 * fderiv ℝ ζ (graphProjectionN 2 z) (graphProjectionN 2 (ν z))) := by
  have hc : ContDiff ℝ 1 (fun x : AmbientSpace =>
      ζ (graphProjectionN 2 x) * ψ (x 2)) :=
    (hζ.comp (graphProjectionN 2).contDiff).mul
      (hψ.comp (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).contDiff)
  have hdiv : divergenceN (fun x : AmbientSpace =>
      (ζ (graphProjectionN 2 x) * ψ (x 2)) • EuclideanSpace.single 2 1) z = 0 := by
    simp only [divergenceN, fderiv_smul_const (hc.differentiable one_ne_zero z),
      ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, smul_eq_mul]
    simp [fderiv_vertical_tensor_last hζ hψ, hdp]
  rw [tangentialDivergence, hdiv,
    fderiv_smul_const (hc.differentiable one_ne_zero z),
    ContinuousLinearMap.smulRight_apply, real_inner_smul_right,
    EuclideanSpace.inner_single_right, fderiv_vertical_tensor_apply hζ hψ, hp, hdp]
  simp [mul_comm]

end LiquidDrop
