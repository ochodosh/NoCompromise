import NoCompromise.Elliptic.HolderInterpolationNorm
import NoCompromise.Elliptic.HolderInterpolationSplit
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Hölder interpolation on the same ball

The C^(0,α) norm is the uniform norm plus the difference-quotient seminorm.
The first and second derivatives are Fréchet derivatives with their operator norms.
The function norm on the right is the actual Lebesgue L∞ norm on the same open ball.
For each fixed 0 < α < 1, positive radius, and positive ε, the constant is chosen
before the function. No extension to a larger ball is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace LiquidDrop

/-- A stronger same-ball estimate uses only the uniform Hessian norm. -/
theorem holder_interpolation_uniform_hessian {n : ℕ} {α ε R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hR : 0 < R)
    (c : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 u (ball c R) → MemLp u ∞ (volume.restrict (ball c R)) →
      BddAbove (insert 0 ((fun x => ‖fderiv ℝ (fderiv ℝ u) x‖) '' ball c R)) →
      HasFiniteHolderNormOn α (fderiv ℝ u) (ball c R) ∧
      holderNorm α (fderiv ℝ u) (ball c R) ≤
        ε * holderUniformNorm (fderiv ℝ (fderiv ℝ u)) (ball c R) +
          C * lpNorm u ∞ (volume.restrict (ball c R)) := by
  obtain ⟨s, t, hs, hsR, ht, hsmall⟩ := holderInterpolation_exists_scales hα1 hε hR
  let C := (4 / s) * (1 + 2 / t ^ α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu hmu hH
  let M₀ := lpNorm u ∞ (volume.restrict (ball c R))
  let M := holderUniformNorm (fderiv ℝ (fderiv ℝ u)) (ball c R)
  have hM₀ : 0 ≤ M₀ := lpNorm_nonneg
  have hM : 0 ≤ M :=
    holderUniformNorm_nonneg (f := fderiv ℝ (fderiv ℝ u)) hH
  have hval : ∀ x ∈ ball c R, ‖u x‖ ≤ M₀ :=
    holderInterpolation_norm_le_lpNorm_top isOpen_ball hu.continuousOn hmu
  have hHbound : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M :=
    fun _ hx => norm_le_holderUniformNorm (f := fderiv ℝ (fderiv ℝ u)) hH hx
  let A := (4 / s) * M₀ + (2 * s) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfirst : ∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ A :=
    fun _ hx => holderInterpolation_fderiv_le hu hs hsR hM hM₀ hval hHbound hx
  let B := M * t ^ (1 - α) + 2 * A / t ^ α
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hquot : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖fderiv ℝ u x - fderiv ℝ u y‖ / ‖x - y‖ ^ α ≤ B := by
    intro x hx y hy
    exact holderInterpolation_quotient_le hα hα1 ht hA hM hfirst
      (fun _ hx _ hy => holderInterpolation_fderiv_sub_le hu hHbound hy hx) hx hy
  refine ⟨HasFiniteHolderNormOn.of_bounds hA hB hfirst hquot, ?_⟩
  calc
    holderNorm α (fderiv ℝ u) (ball c R) ≤ A + B := holderNorm_le hA hB hfirst hquot
    _ = (2 * s * (1 + 2 / t ^ α) + t ^ (1 - α)) * M + C * M₀ := by
      dsimp [A, B, C]
      ring
    _ ≤ ε * M + C * M₀ := add_le_add (mul_le_mul_of_nonneg_right hsmall hM) le_rfl

/-- The requested same-ball interpolation with the full C^(0,α) Hessian norm. -/
theorem holder_interpolation_of_memLp {n : ℕ} {α ε R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hR : 0 < R)
    (c : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 u (ball c R) → MemLp u ∞ (volume.restrict (ball c R)) →
      HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ u)) (ball c R) →
      HasFiniteHolderNormOn α (fderiv ℝ u) (ball c R) ∧
      holderNorm α (fderiv ℝ u) (ball c R) ≤
        ε * holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R) +
          C * lpNorm u ∞ (volume.restrict (ball c R)) := by
  obtain ⟨C, hC, hb⟩ := holder_interpolation_uniform_hessian hα hα1 hε hR c
  refine ⟨C, hC, ?_⟩
  intro u hu hmu hH
  obtain ⟨hfirst, hbound⟩ := hb u hu hmu hH.uniform_bounded
  exact ⟨hfirst, hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left hH.uniformNorm_le hε.le) le_rfl)⟩

/-- Explicit C^(2,α) membership: C² regularity and finite Hölder norms of all three orders. -/
structure HasC2HolderOn {n : ℕ} (α : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  contDiff : ContDiffOn ℝ 2 u U
  function_holder : HasFiniteHolderNormOn α u U
  derivative_holder : HasFiniteHolderNormOn α (fderiv ℝ u) U
  hessian_holder : HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ u)) U

lemma HasC2HolderOn.memLp_top {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC2HolderOn α u U) (hU : IsOpen U) : MemLp u ∞ (volume.restrict U) := by
  apply memLp_top_of_bound (hu.contDiff.continuousOn.aestronglyMeasurable hU.measurableSet)
    (holderUniformNorm u U)
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact norm_le_holderUniformNorm hu.function_holder.uniform_bounded hx

/-- Blueprint `lem:holder-interp`: the domain is the same positive-radius ball on both sides. -/
theorem holder_interpolation {n : ℕ} {α ε R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hR : 0 < R)
    (c : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC2HolderOn α u (ball c R) →
      holderNorm α (fderiv ℝ u) (ball c R) ≤
        ε * holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R) +
          C * lpNorm u ∞ (volume.restrict (ball c R)) := by
  obtain ⟨C, hC, hb⟩ := holder_interpolation_of_memLp hα hα1 hε hR c
  exact ⟨C, hC, fun u hu =>
    (hb u hu.contDiff (hu.memLp_top isOpen_ball) hu.hessian_holder).2⟩

end LiquidDrop
