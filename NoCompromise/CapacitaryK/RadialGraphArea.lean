import NoCompromise.CapacitaryK.Calculus
import NoCompromise.BV.SphericalSlicing

/-!
# Area of a C¹ radial graph over the unit sphere

For a positive C¹ radial function `ρ`, the radial graph `θ ↦ ρ θ • θ + z` over the unit sphere
has area element `ρ * sqrt (ρ² + |∇_T ρ|²)` against the unit-sphere area. We also record the
algebraic identification of this factor in terms of an implicit-function gradient.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal InnerProductSpace Gradient

namespace LiquidDrop.CapacitaryK

/-- The radial area factor in terms of an implicit-function gradient `G`. -/
theorem radial_graph_jacobian_of_implicit {ρ : ℝ} {θ G T : E3} (hθ : ‖θ‖ = 1) (hρ : 0 < ρ)
    (hG : ⟪G, θ⟫_ℝ ≠ 0) (hT : T = -(ρ / ⟪G, θ⟫_ℝ) • (G - ⟪G, θ⟫_ℝ • θ)) :
    ρ * Real.sqrt (ρ ^ 2 + ‖T - ⟪T, θ⟫_ℝ • θ‖ ^ 2) = ρ ^ 2 * ‖G‖ / |⟪G, θ⟫_ℝ| := by
  set c := ⟪G, θ⟫_ℝ with hc
  have hθθ : ⟪θ, θ⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hθ, one_pow]
  have hTθ : ⟪T, θ⟫_ℝ = 0 := by
    rw [hT, inner_smul_left, inner_sub_left, inner_smul_left, hθθ, ← hc]
    simp
  have hnorm : ‖G - c • θ‖ ^ 2 = ‖G‖ ^ 2 - c ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, hθ, inner_smul_right, ← hc, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hTn : ‖T - ⟪T, θ⟫_ℝ • θ‖ ^ 2 = ρ ^ 2 / c ^ 2 * (‖G‖ ^ 2 - c ^ 2) := by
    rw [hTθ, zero_smul, sub_zero, hT, norm_smul, mul_pow, hnorm, Real.norm_eq_abs, sq_abs,
      neg_sq, div_pow]
  have hc2 : 0 < c ^ 2 := by positivity
  have hsum : ρ ^ 2 + ‖T - ⟪T, θ⟫_ℝ • θ‖ ^ 2 = (ρ * ‖G‖ / |c|) ^ 2 := by
    rw [hTn, div_pow, mul_pow, sq_abs]
    field_simp
    ring
  rw [hsum, Real.sqrt_sq (by positivity)]
  ring

end LiquidDrop.CapacitaryK
