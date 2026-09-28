import NoCompromise.Regularity.CompressionLinear
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # The genuine vertical compression map and its inverse -/

noncomputable section
open Set InnerProductSpace
open scoped Gradient
namespace LiquidDrop

def verticalCompression (β : EuclideanSpace ℝ (Fin 2) → ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  graphAppendN (graphProjectionN 2 x) (c + β (graphProjectionN 2 x) * (x 2 - c))

@[simp] lemma verticalCompression_projection (β : EuclideanSpace ℝ (Fin 2) → ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    graphProjectionN 2 (verticalCompression β c x) = graphProjectionN 2 x := by
  simp only [verticalCompression, graphProjectionN_append]

@[simp] lemma verticalCompression_height (β : EuclideanSpace ℝ (Fin 2) → ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    verticalCompression β c x 2 = c + β (graphProjectionN 2 x) * (x 2 - c) :=
  graphAppendN_last _ _

lemma verticalCompression_inverse (β : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hβ : ∀ x, β x ≠ 0) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    verticalCompression (fun y => (β y)⁻¹) c (verticalCompression β c x) = x := by
  unfold verticalCompression
  rw [graphProjectionN_append]
  have hl (p : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : graphAppendN p s (2 : Fin 3) = s :=
    graphAppendN_last p s
  rw [hl]
  have he : c + (β (graphProjectionN 2 x))⁻¹ *
      (c + β (graphProjectionN 2 x) * (x 2 - c) - c) = x 2 := by
    field_simp [hβ (graphProjectionN 2 x)]
    ring
  rw [he]
  exact graphAppendN_projection x

lemma verticalCompression_inverse_right (β : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hβ : ∀ x, β x ≠ 0) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    verticalCompression β c (verticalCompression (fun y => (β y)⁻¹) c x) = x := by
  simpa only [inv_inv] using verticalCompression_inverse (fun y => (β y)⁻¹)
    (fun y => inv_ne_zero (hβ y)) c x

lemma contDiff_verticalCompression {β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hβ : ContDiff ℝ 1 β) (c : ℝ) : ContDiff ℝ 1 (verticalCompression β c) := by
  unfold verticalCompression graphAppendN
  have hp : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) => β (graphProjectionN 2 x)) :=
    hβ.comp (graphProjectionN 2).contDiff
  have hz : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) => x 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff
  exact (graphBaseN 2).contDiff.comp (graphProjectionN 2).contDiff |>.add
    ((contDiff_const.add (hp.mul (hz.sub contDiff_const))).smul contDiff_const)

lemma hasFDerivAt_verticalCompression {β : EuclideanSpace ℝ (Fin 2) → ℝ} {c : ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} {p : EuclideanSpace ℝ (Fin 2)}
    (hβ : HasGradientAt β p (graphProjectionN 2 x)) :
    HasFDerivAt (verticalCompression β c)
      (compressionLinear (β (graphProjectionN 2 x)) (x 2 - c) p) x := by
  have hp := hβ.hasFDerivAt.comp x (graphProjectionN 2).hasFDerivAt
  have hz := ((EuclideanSpace.proj (2 : Fin 3) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const c
  have hv := (hp.mul hz).const_add c
  have ha := ((graphBaseN 2).hasFDerivAt.comp x (graphProjectionN 2).hasFDerivAt).add
    (hv.smul_const (EuclideanSpace.single (Fin.last 2) (1 : ℝ)))
  convert! ha using 1
  ext v i
  rw [compressionLinear_apply]
  fin_cases i <;>
    simp [graphAppendN, graphBaseN, graphProjectionN, toDual_apply_apply,
      Fin.sum_univ_two, PiLp.inner_apply]
  ring

end LiquidDrop
