import NoCompromise.Regularity.HarmonicBlowupNormalizedCompactness
import NoCompromise.Regularity.HarmonicBlowupUniformH1

/-!
# Uniform harmonic approximation of actual normalized functions

Energy and residual constants are fixed before the approximation tolerance.
All height functions with those quantitative bounds are included, independently
of their values, additive constants, or choice of graph clamp.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Uniform normalized harmonic approximation from true energy and residual
bounds. The conclusion holds on the entire half disk, hence also its quarter disk. -/
theorem harmonicBlowup_uniform_normalized {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ Cb > 0, ∀ τ : ℝ, 0 < τ → ∃ ε > 0, ε ≤ 1 ∧
      ∀ (f : EuclideanSpace ℝ (Fin 2) → ℝ)
        (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (_hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ),
        0 < a → a ^ 2 ≤ ε →
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖G x‖ ^ 2) ≤ C * a ^ 2 →
        (∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 (1 / 2) → ∀ M : ℝ, 0 ≤ M →
            (∀ x, ‖gradient φ x‖ ≤ M) →
            |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
              inner ℝ (G x) (gradient φ x)| ≤ D * a ^ 2 * M) →
        ∃ h : EuclideanSpace ℝ (Fin 2) → ℝ,
          ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 2)) ∧
          HasH1GradientOn h (gradient h) (ball 0 (1 / 2)) ∧
          HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 2)) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), laplacianN h x = 0) ∧
          (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
            ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) ≤ Cb ∧
          (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
            |harmonicBlowupFunction f a x - h x| ^ 2) ≤ τ := by
  obtain ⟨B, hB, hbound⟩ := harmonicBlowup_normalized_bound hC
  refine ⟨B ^ 2, sq_pos_of_pos hB, fun τ hτ => ?_⟩
  obtain ⟨δ, hδ, huniform⟩ := harmonicBlowup_uniform_h1 B hτ
  have hD1 : 0 < D + 1 := by linarith
  let ε := min 1 ((δ / (D + 1)) ^ 2)
  have hε : 0 < ε := lt_min zero_lt_one (sq_pos_of_pos (div_pos hδ hD1))
  refine ⟨ε, hε, min_le_left _ _, fun f G hf a ha hsmall he hres => ?_⟩
  have haδ : a ≤ δ / (D + 1) :=
    (sq_le_sq₀ ha.le (div_nonneg hδ.le hD1.le)).mp
      (hsmall.trans (min_le_right _ _))
  have hDa : D * a ≤ δ := by
    have hh := (le_div_iff₀ hD1).mp haδ
    nlinarith
  let u := harmonicBlowupClass f G hf a
  have hresu (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 (1 / 2))
      (M : ℝ) (hM : 0 ≤ M) (hMb : ∀ x, ‖gradient φ x‖ ≤ M) :
      |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ (u.gradientLp x) (gradient φ x)| ≤ δ * M :=
    (harmonicBlowup_normalized_residual_bound hf ha D M φ
      (hres φ hφ hcφ hsφ M hM hMb)).trans (mul_le_mul_of_nonneg_right hDa hM)
  obtain ⟨h, hc, hh1, hd, hz, henergy, herr⟩ :=
    huniform u (hbound f G hf a ha he) hresu
  refine ⟨h, hc, hh1, hd, hz, henergy, ?_⟩
  convert herr using 1
  apply integral_congr_ae
  filter_upwards [harmonicBlowupClass_coeFn f G hf a] with x hx
  rw [hx]

end LiquidDrop
