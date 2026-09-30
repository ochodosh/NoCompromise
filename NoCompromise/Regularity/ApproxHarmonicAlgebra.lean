module

public import NoCompromise.Area.Graph
public import NoCompromise.BV.CoareaCoordinates

@[expose] public section

/-! # The graph first-variation density and its quadratic error -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma approxHarmonic_graphUnitNormal_projection (p : EuclideanSpace ℝ (Fin 2)) :
    graphProjectionN 2 (graphUnitNormal p) =
      -(Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • p := by
  ext i
  fin_cases i <;>
    simp [graphProjectionN_apply, graphUnitNormal, graphNormalVector]

lemma approxHarmonic_graphUnitNormal_vertical (p : EuclideanSpace ℝ (Fin 2)) :
    graphUnitNormal p 2 = (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ := by
  simp [graphUnitNormal]

lemma approxHarmonic_vertical_density (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    -(graphUnitNormal p 2 * L (graphProjectionN 2 (graphUnitNormal p))) =
      L p / (1 + ‖p‖ ^ 2) := by
  have hs : 0 < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [approxHarmonic_graphUnitNormal_projection, approxHarmonic_graphUnitNormal_vertical,
    map_smul, smul_eq_mul]
  have he := Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖p‖ ^ 2)
  field_simp
  nlinarith only [congrArg (fun t : ℝ => L p * t) he]

lemma approxHarmonic_weighted_vertical_density (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    -(graphUnitNormal p 2 * L (graphProjectionN 2 (graphUnitNormal p))) *
        Real.sqrt (1 + ‖p‖ ^ 2) = L p / Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [approxHarmonic_vertical_density]
  have hs : Real.sqrt (1 + ‖p‖ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have he := Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖p‖ ^ 2)
  field_simp
  nlinarith only [congrArg (fun t : ℝ => L p * t) he]

/-- The difference between the minimal-surface flux and the linear gradient
is quadratic on the unit slope ball. -/
lemma approxHarmonic_nonlinear_error (p q : EuclideanSpace ℝ (Fin 2))
    (hp : ‖p‖ ≤ 1) :
    |inner ℝ p q - inner ℝ p q / Real.sqrt (1 + ‖p‖ ^ 2)| ≤ ‖p‖ ^ 2 * ‖q‖ := by
  let s := Real.sqrt (1 + ‖p‖ ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs1 : 1 ≤ s := by
    dsimp [s]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖p‖])
  have hs2 : s ^ 2 = 1 + ‖p‖ ^ 2 := Real.sq_sqrt (by positivity)
  have he : 1 - s⁻¹ = (s - 1) / s := by field_simp
  have hnon : 0 ≤ 1 - s⁻¹ := by rw [he]; positivity
  have hbound : 1 - s⁻¹ ≤ ‖p‖ ^ 2 := by
    rw [he, div_le_iff₀ hs]
    nlinarith [mul_nonneg (sq_nonneg ‖p‖) (sub_nonneg.mpr hs1)]
  have hi : |inner ℝ p q| ≤ ‖q‖ :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg q])
  calc
    _ = |inner ℝ p q| * (1 - s⁻¹) := by
      rw [show inner ℝ p q - inner ℝ p q / s = inner ℝ p q * (1 - s⁻¹) by ring,
        abs_mul, abs_of_nonneg hnon]
    _ ≤ ‖q‖ * ‖p‖ ^ 2 := mul_le_mul hi hbound hnon (norm_nonneg q)
    _ = _ := by ring

end LiquidDrop
