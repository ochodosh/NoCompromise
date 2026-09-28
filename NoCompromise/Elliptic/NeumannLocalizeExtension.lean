import NoCompromise.Elliptic.BoundaryNormalChartCoefficient
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional

/-!
# Global bi-Lipschitz extensions near a regular point

Extend the Lipschitz difference from the derivative and use the quantitative
inverse function theorem. The extension need only be Lipschitz away from the
neighborhood where it agrees with the given C¹ map.
-/

noncomputable section

open Set Filter Metric
open scoped Topology NNReal

namespace LiquidDrop

/-- The input translation and nonzero dilation used for normal coordinates. -/
def neumannLocalizeDilation (b : AmbientSpace) {ρ : ℝ} (hρ : ρ ≠ 0) :
    AmbientSpace ≃ₜ AmbientSpace :=
  (Homeomorph.smulOfNeZero ρ hρ).trans (Homeomorph.addLeft b)

lemma neumannLocalizeDilation_lipschitz (b : AmbientSpace) {ρ : ℝ} (hρ : ρ ≠ 0) :
    LipschitzWith ‖ρ‖₊ (neumannLocalizeDilation b hρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (b + ρ • x) (b + ρ • y) ≤ ‖ρ‖ * dist x y
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul]

lemma neumannLocalizeDilation_symm_lipschitz (b : AmbientSpace) {ρ : ℝ} (hρ : ρ ≠ 0) :
    LipschitzWith ‖ρ⁻¹‖₊ (neumannLocalizeDilation b hρ).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (ρ⁻¹ • (-b + x)) (ρ⁻¹ • (-b + y)) ≤ ‖ρ⁻¹‖ * dist x y
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub, norm_smul]

/-- A C¹ map with invertible derivative agrees with a global bi-Lipschitz
homeomorphism on an open neighborhood of the regular point. -/
theorem neumannLocalize_exists_bilipschitz_extension
    {f : AmbientSpace → AmbientSpace} {p : AmbientSpace}
    (hf : ContDiffAt ℝ 1 f p) (hreg : (fderiv ℝ f p).IsInvertible) :
    ∃ (e : AmbientSpace ≃ₜ AmbientSpace) (C K : ℝ≥0) (U : Set AmbientSpace),
      LipschitzWith C e ∧ LipschitzWith K e.symm ∧ IsOpen U ∧ p ∈ U ∧ EqOn f e U := by
  obtain ⟨L, hL⟩ := hreg
  have hd : HasFDerivAt f (L : AmbientSpace →L[ℝ] AmbientSpace) p := by
    rw [hL]
    exact (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hstrict := hf.hasStrictFDerivAt' hd one_ne_zero
  obtain ⟨c, hc, hsmall⟩ := exists_pos_mul_lt
    (inv_pos.mpr L.nnnorm_symm_pos) (lipschitzExtensionConstant AmbientSpace)
  obtain ⟨s, hsp, hs⟩ := hstrict.approximates_deriv_on_nhds (Or.inr hc)
  obtain ⟨u, hu, huf⟩ := hs.lipschitzOnWith.extend_finite_dimension
  let g : AmbientSpace → AmbientSpace := fun x => L x + u x
  have hfg : EqOn f g s := by
    intro x hx
    simp only [g, ← huf hx, Pi.sub_apply, ContinuousLinearEquiv.coe_coe]
    abel
  have hg : ApproximatesLinearOn g (L : AmbientSpace →L[ℝ] AmbientSpace) univ
      (lipschitzExtensionConstant AmbientSpace * c) := by
    apply LipschitzOnWith.approximatesLinearOn
    rw [lipschitzOnWith_univ]
    have heq : g - ⇑(L : AmbientSpace →L[ℝ] AmbientSpace) = u := by
      funext x
      change L x + u x - L x = u x
      abel
    rw [heq]
    exact hu
  let e : AmbientSpace ≃ₜ AmbientSpace := hg.toHomeomorph g (Or.inr hsmall)
  have he : (e : AmbientSpace → AmbientSpace) = g := rfl
  have heLip : LipschitzWith
      (‖(L : AmbientSpace →L[ℝ] AmbientSpace)‖₊ + lipschitzExtensionConstant AmbientSpace * c)
      e := by
    rw [he]
    exact (L : AmbientSpace →L[ℝ] AmbientSpace).lipschitzWith.add hu
  have heAnti : AntilipschitzWith
      (‖(L.symm : AmbientSpace →L[ℝ] AmbientSpace)‖₊⁻¹ -
        lipschitzExtensionConstant AmbientSpace * c)⁻¹ e := by
    intro x y
    exact hg.antilipschitz (Or.inr hsmall) ⟨x, mem_univ x⟩ ⟨y, mem_univ y⟩
  obtain ⟨U, hUs, hU, hpU⟩ := _root_.mem_nhds_iff.mp hsp
  exact ⟨e, _, _, U, heLip, heAnti.to_rightInverse e.apply_symm_apply,
    hU, hpU, fun x hx => hfg (hUs hx)⟩

end LiquidDrop
