module

public import NoCompromise.Sobolev.WeakCompactness
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

@[expose] public section

/-!
# Coercive quadratic minimization from Hilbert representation

A bounded linear map with a proved inverse norm bound has closed range. Riesz
representation on that closed Hilbert subspace solves the variational equation.
The quadratic energy identity then gives existence, uniqueness, and bounds,
without invoking a packaged elliptic solvability or Lax–Milgram theorem.
-/

noncomputable section
open Set InnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A coercive gradient map represents every bounded variational functional. -/
theorem exists_unique_gradient_riesz
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ u, ‖u‖ ≤ C * ‖A u‖)
    (ℓ : E →L[ℝ] ℝ) : ∃! u : E, ∀ v : E, inner ℝ (A u) (A v) = ℓ v := by
  have ha : AntilipschitzWith ⟨C, hC⟩ A :=
    ContinuousLinearMap.antilipschitz_of_bound A hA
  have hclosed : IsClosed (A.range : Set F) := ha.isClosed_range A.uniformContinuous
  let : CompleteSpace A.range := hclosed.completeSpace_coe
  let e₀ : E ≃ₗ[ℝ] A.range := LinearEquiv.ofInjective A.toLinearMap ha.injective
  let e : E ≃L[ℝ] A.range := e₀.toContinuousLinearEquivOfBounds ‖A‖ C
    (fun u => A.le_opNorm u) (fun w => by
      have h := hA (e₀.symm w)
      have he : A (e₀.symm w) = (w : F) := congrArg Subtype.val (e₀.apply_symm_apply w)
      change ‖e₀.symm w‖ ≤ C * ‖(w : F)‖
      simpa only [he] using h)
  let w : A.range := (toDual ℝ A.range).symm (ℓ.comp e.symm.toContinuousLinearMap)
  let u := e.symm w
  have hu (v : E) : inner ℝ (A u) (A v) = ℓ v := by
    have h := toDual_symm_apply (x := e v) (y := ℓ.comp e.symm.toContinuousLinearMap)
    change inner ℝ w (e v) = ℓ (e.symm (e v)) at h
    rw [e.symm_apply_apply] at h
    have he : A u = (w : F) := congrArg Subtype.val (e.apply_symm_apply w)
    change inner ℝ (A u) (e v : F) = _
    rw [he]
    exact h
  refine ⟨u, hu, fun v hv => ?_⟩
  apply ha.injective
  apply sub_eq_zero.mp
  rw [← inner_self_eq_zero (𝕜 := ℝ)]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hv v, hv u, hu v, hu u]
  ring

/-- The coercive variational solution has the elementary energy estimate. -/
lemma norm_le_of_gradient_riesz
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ u, ‖u‖ ≤ C * ‖A u‖)
    (ℓ : E →L[ℝ] ℝ) {u : E} (hu : ∀ v, inner ℝ (A u) (A v) = ℓ v) :
    ‖A u‖ ≤ C * ‖ℓ‖ ∧ ‖u‖ ≤ C ^ 2 * ‖ℓ‖ := by
  have hi : ‖A u‖ ^ 2 = ℓ u := by simpa only [real_inner_self_eq_norm_sq] using hu u
  have hl : ℓ u ≤ ‖ℓ‖ * ‖u‖ := (le_abs_self _).trans (ℓ.le_opNorm u)
  have hmul := mul_le_mul_of_nonneg_left (hA u) (norm_nonneg ℓ)
  have hAu : ‖A u‖ ≤ C * ‖ℓ‖ := by
    by_cases hz : ‖A u‖ = 0
    · rw [hz]
      exact mul_nonneg hC (norm_nonneg _)
    · have hp : 0 < ‖A u‖ := (norm_nonneg _).lt_of_ne (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [hi, hl, hmul]
  refine ⟨hAu, (hA u).trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hAu hC]

/-- The stationary quadratic energy differs from its minimum by exactly half
the squared gradient norm of the difference. -/
lemma quadratic_energy_gap_of_gradient_riesz
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (ℓ : E →L[ℝ] ℝ) {u : E}
    (hu : ∀ v, inner ℝ (A u) (A v) = ℓ v) (v : E) :
    (1 / 2 : ℝ) * ‖A v‖ ^ 2 - ℓ v =
      ((1 / 2 : ℝ) * ‖A u‖ ^ 2 - ℓ u) + (1 / 2 : ℝ) * ‖A (v - u)‖ ^ 2 := by
  have hv : inner ℝ (A v) (A u) = ℓ v := (real_inner_comm _ _).trans (hu v)
  have hs := norm_sub_sq_real (A v) (A u)
  rw [hv, ← map_sub] at hs
  have hi : ‖A u‖ ^ 2 = ℓ u := by simpa only [real_inner_self_eq_norm_sq] using hu u
  nlinarith only [hs, hi]

/-- Concrete quadratic minimization, including the weak equation, unique
minimizer characterization, and a quantitative solution bound. -/
theorem exists_unique_coercive_quadratic_minimizer
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) (hA : ∀ u, ‖u‖ ≤ C * ‖A u‖)
    (ℓ : E →L[ℝ] ℝ) :
    ∃ u : E, (∀ v, inner ℝ (A u) (A v) = ℓ v) ∧
      (∀ v, (1 / 2 : ℝ) * ‖A u‖ ^ 2 - ℓ u ≤ (1 / 2 : ℝ) * ‖A v‖ ^ 2 - ℓ v) ∧
      (∀ v, ((1 / 2 : ℝ) * ‖A v‖ ^ 2 - ℓ v ≤
        (1 / 2 : ℝ) * ‖A u‖ ^ 2 - ℓ u) ↔ v = u) ∧
      ‖A u‖ ≤ C * ‖ℓ‖ ∧ ‖u‖ ≤ C ^ 2 * ‖ℓ‖ := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_gradient_riesz A hC hA ℓ
  refine ⟨u, hu, fun v => ?_, fun v => ?_, norm_le_of_gradient_riesz A hC hA ℓ hu⟩
  · rw [quadratic_energy_gap_of_gradient_riesz A ℓ hu v]
    nlinarith [sq_nonneg ‖A (v - u)‖]
  · constructor
    · intro hv
      rw [quadratic_energy_gap_of_gradient_riesz A ℓ hu v] at hv
      have hz : ‖A (v - u)‖ = 0 := by nlinarith [sq_nonneg ‖A (v - u)‖]
      have h := hA (v - u)
      rw [hz, mul_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    · rintro rfl
      exact le_rfl

end LiquidDrop
