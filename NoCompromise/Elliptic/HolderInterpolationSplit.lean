import NoCompromise.Elliptic.HolderInterpolationGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The two-scale Hölder estimate

Small distances use a Lipschitz estimate and large distances use a uniform estimate.
Both scales in the derivative interpolation are chosen before the function.
-/

noncomputable section
open Metric Set

namespace LiquidDrop

/-- Splitting distances at a positive scale interpolates uniform and Lipschitz bounds. -/
theorem holderInterpolation_quotient_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α t A M : ℝ} (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t)
    (hA : 0 ≤ A) (hM : 0 ≤ M) {g : E → F} {U : Set E}
    (hval : ∀ x ∈ U, ‖g x‖ ≤ A)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ M * ‖x - y‖)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖g x - g y‖ / ‖x - y‖ ^ α ≤ M * t ^ (1 - α) + 2 * A / t ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, zero_div]
    positivity
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hden : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
  have htden : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  by_cases hdt : ‖x - y‖ ≤ t
  · calc
      ‖g x - g y‖ / ‖x - y‖ ^ α ≤ (M * ‖x - y‖) / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right (hlip x hx y hy) hden.le
      _ = M * ‖x - y‖ ^ (1 - α) := by rw [Real.rpow_sub hd, Real.rpow_one]; ring
      _ ≤ M * t ^ (1 - α) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hdt (sub_pos.mpr hα1).le) hM
      _ ≤ M * t ^ (1 - α) + 2 * A / t ^ α := le_add_of_nonneg_right (by positivity)
  · have hnum : ‖g x - g y‖ ≤ 2 * A :=
      (norm_sub_le _ _).trans (by linarith [hval x hx, hval y hy])
    calc
      ‖g x - g y‖ / ‖x - y‖ ^ α ≤ (2 * A) / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right hnum hden.le
      _ ≤ 2 * A / t ^ α := div_le_div_of_nonneg_left (by positivity) htden
        (Real.rpow_le_rpow ht.le (le_of_not_ge hdt) hα.le)
      _ ≤ M * t ^ (1 - α) + 2 * A / t ^ α := le_add_of_nonneg_left (by positivity)

/-- The two scales can make the Hessian coefficient arbitrarily small on the same ball. -/
theorem holderInterpolation_exists_scales {α ε R : ℝ}
    (hα1 : α < 1) (hε : 0 < ε) (hR : 0 < R) :
    ∃ s t : ℝ, 0 < s ∧ s < R ∧ 0 < t ∧
      2 * s * (1 + 2 / t ^ α) + t ^ (1 - α) ≤ ε := by
  let t := (ε / 2) ^ (1 - α)⁻¹
  have ht : 0 < t := Real.rpow_pos_of_pos (half_pos hε) _
  have htEq : t ^ (1 - α) = ε / 2 :=
    Real.rpow_inv_rpow (half_pos hε).le (sub_pos.mpr hα1).ne'
  let L := 1 + 2 / t ^ α
  have hL : 0 < L := by dsimp [L]; positivity
  let s := min (R / 2) (ε / (4 * L))
  have hs : 0 < s := lt_min (half_pos hR) (div_pos hε (by positivity))
  have hsR : s < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hsL : s * (4 * L) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 4 * L)).mp (min_le_right _ _)
  refine ⟨s, t, hs, hsR, ht, ?_⟩
  change 2 * s * L + t ^ (1 - α) ≤ ε
  rw [htEq]
  nlinarith

end LiquidDrop
