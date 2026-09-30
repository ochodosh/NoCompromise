module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# A `C²` function with vanishing Hessian on a convex open set is affine

Last analytic step toward local flatness of the punctured boundary of a minimising cone
(`lem:cone-link-great-circle`, chapter 25): once the Hessian of the boundary graph vanishes, the
graph is a piece of an affine plane.
-/

noncomputable section
open Set

namespace LiquidDrop

/-- A `C²` function with vanishing second derivative on a convex open set is affine there. -/
theorem affine_of_fderiv_fderiv_eq_zero {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hcU : Convex ℝ U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (h : ∀ x ∈ U, fderiv ℝ (fderiv ℝ f) x = 0)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ U) :
    ∀ x ∈ U, f x = f x₀ + fderiv ℝ f x₀ (x - x₀) := by
  have hd1 : DifferentiableOn ℝ f U := hf.differentiableOn (by norm_num)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have hdDf : DifferentiableOn ℝ (fderiv ℝ f) U := hDf.differentiableOn (by norm_num)
  -- the derivative is constant
  have hconst : ∀ x ∈ U, fderiv ℝ f x = fderiv ℝ f x₀ := by
    intro x hx
    have hz : ∀ y ∈ U, fderivWithin ℝ (fderiv ℝ f) U y = 0 := by
      intro y hy
      rw [fderivWithin_of_isOpen hU hy]
      exact h y hy
    exact hcU.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) hdDf hz hx hx₀
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x - fderiv ℝ f x₀ (x - x₀)
  have hg : ∀ y ∈ U, HasFDerivAt g (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y := by
    intro y hy
    have h1 : HasFDerivAt f (fderiv ℝ f y) y :=
      (hd1.differentiableAt (hU.mem_nhds hy)).hasFDerivAt
    have h2 : HasFDerivAt (fun x => fderiv ℝ f x₀ (x - x₀)) (fderiv ℝ f x₀) y :=
      (fderiv ℝ f x₀).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀) |>.congr_fderiv
        (by ext; simp)
    have h3 := h1.sub h2
    rwa [hconst y hy, sub_self] at h3
  have hgd : DifferentiableOn ℝ g U := fun y hy => (hg y hy).differentiableAt.differentiableWithinAt
  intro x hx
  have hz : ∀ y ∈ U, fderivWithin ℝ g U y = 0 := by
    intro y hy
    rw [fderivWithin_of_isOpen hU hy]
    exact (hg y hy).fderiv
  have hgx : g x = g x₀ := hcU.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) hgd hz hx hx₀
  simp only [g, sub_self, map_zero, sub_zero] at hgx
  linarith

end LiquidDrop
