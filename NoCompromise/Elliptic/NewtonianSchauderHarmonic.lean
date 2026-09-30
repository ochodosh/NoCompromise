module

public import NoCompromise.Elliptic.NewtonianSchauderNorm
public import NoCompromise.Elliptic.HarmonicDerivative
public import NoCompromise.Elliptic.HarmonicAlgebra

@[expose] public section

/-!
# The harmonic remainder in the Schauder estimate

The already proved second- and third-derivative harmonic estimates give a
uniform and a Lipschitz bound for the Hessian. Their elementary interpolation
gives its Hölder norm; no new harmonic regularity theorem is used as a premise.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma schauder_norm_fderiv_two (u : E₃ → ℝ) (x : E₃) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ = ‖iteratedFDeriv ℝ 2 u x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ u), norm_iteratedFDeriv_fderiv]

lemma schauder_norm_fderiv_three (u : E₃ → ℝ) (x : E₃) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ = ‖iteratedFDeriv ℝ 3 u x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (fderiv ℝ u)),
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

/-- Quantitative Hölder control of the Hessian of the smooth harmonic remainder.
The constant precedes the function. Global smoothness is supplied by the frozen
interior harmonic representative theorem in the final assembly. -/
theorem exists_schauder_harmonic_hessian_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (u : E₃ → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
      HasDistributionalLaplacianOn u (fun _ => 0) (ball 0 (2 / 3)) →
      MemLp u ∞ (volume.restrict (ball 0 (2 / 3))) →
      HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ u)) (ball 0 (1 / 2)) ∧
        holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball 0 (1 / 2)) ≤
          C * lpNorm u ∞ (volume.restrict (ball 0 (2 / 3))) := by
  obtain ⟨C₂, hC₂, hb₂⟩ := harmonic_derivative_estimate_top (n := 3) (k := 2)
    (by norm_num) (by norm_num : (1 / 2 : ℝ) < 2 / 3)
  obtain ⟨C₃, hC₃, hb₃⟩ := harmonic_derivative_estimate_top (n := 3) (k := 3)
    (by norm_num) (by norm_num : (1 / 2 : ℝ) < 2 / 3)
  refine ⟨3 * C₂ + C₃, by positivity, fun u hu hd hm => ?_⟩
  let L := lpNorm u ∞ (volume.restrict (ball (0 : E₃) (2 / 3)))
  have hL : 0 ≤ L := lpNorm_nonneg
  obtain ⟨hm₂, hh₂⟩ := hb₂ 0 u hd hu.continuous.continuousOn hm
  obtain ⟨hm₃, hh₃⟩ := hb₃ 0 u hd hu.continuous.continuousOn hm
  have hc₂ : ContinuousOn (iteratedFDeriv ℝ 2 u) (ball (0 : E₃) (1 / 2)) :=
    ContinuousOn.continuousOn_iteratedFDeriv hu.contDiffOn isOpen_ball (by simp)
  have hc₃ : ContinuousOn (iteratedFDeriv ℝ 3 u) (ball (0 : E₃) (1 / 2)) :=
    ContinuousOn.continuousOn_iteratedFDeriv hu.contDiffOn isOpen_ball (by simp)
  have hval : ∀ x ∈ ball (0 : E₃) (1 / 2), ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C₂ * L := by
    intro x hx
    rw [schauder_norm_fderiv_two]
    exact (holderInterpolation_norm_le_lpNorm_top isOpen_ball hc₂ hm₂ x hx).trans hh₂
  have hder : ∀ x ∈ ball (0 : E₃) (1 / 2),
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C₃ * L := by
    intro x hx
    rw [schauder_norm_fderiv_three]
    exact (holderInterpolation_norm_le_lpNorm_top isOpen_ball hc₃ hm₃ x hx).trans hh₃
  have hs : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by simp)).fderiv_right (m := 1) (by norm_num)
  have hlip : ∀ x ∈ ball (0 : E₃) (1 / 2), ∀ y ∈ ball (0 : E₃) (1 / 2),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C₃ * L * ‖x - y‖ := by
    intro x hx y hy
    exact (convex_ball (0 : E₃) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hs.differentiable one_ne_zero z) hder hy hx
  have hquot : ∀ x ∈ ball (0 : E₃) (1 / 2), ∀ y ∈ ball (0 : E₃) (1 / 2),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ / ‖x - y‖ ^ α ≤
        C₃ * L + 2 * (C₂ * L) := by
    intro x hx y hy
    simpa only [Real.one_rpow, mul_one, div_one] using
      holderInterpolation_quotient_le hα hα1 (by norm_num : (0 : ℝ) < 1)
        (mul_nonneg hC₂.le hL) (mul_nonneg hC₃.le hL) hval hlip hx hy
  refine ⟨HasFiniteHolderNormOn.of_bounds (mul_nonneg hC₂.le hL) (by positivity) hval hquot,
    (holderNorm_le (mul_nonneg hC₂.le hL) (by positivity) hval hquot).trans_eq ?_⟩
  dsimp [L]
  ring

end LiquidDrop
