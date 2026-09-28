import NoCompromise.Regularity.HarmonicBlowupCompactness

/-!
# Uniform harmonic approximation from small actual residuals

The norm bound is fixed before the tolerance. A contradiction sequence and
actual Rellich compactness yield a smooth harmonic approximant with that same
energy bound. The assertion applies to every H¹ class with the stated test
residuals, so no choice of graph extension enters its constants.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Uniform harmonic approximation on the whole half disk for norm-bounded
actual H¹ functions with sufficiently small compact-test residuals. -/
theorem harmonicBlowup_uniform_h1 (B : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > 0, ∀ u : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)),
      ‖u‖ ≤ B →
      (∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 (1 / 2) →
        ∀ M : ℝ, 0 ≤ M → (∀ x, ‖gradient φ x‖ ≤ M) →
          |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
            inner ℝ (u.gradientLp x) (gradient φ x)| ≤ δ * M) →
      ∃ h : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 2)) ∧
        HasH1GradientOn h (gradient h) (ball 0 (1 / 2)) ∧
        HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 2)) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), laplacianN h x = 0) ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
          ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) ≤ B ^ 2 ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), |u x - h x| ^ 2) ≤ τ := by
  classical
  by_contra! hbad
  choose u hu hr hfail using fun j : ℕ => hbad (1 / ((j : ℝ) + 1)) (by positivity)
  have hres (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 (1 / 2)) :
      Tendsto (fun j => ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ ((u j).gradientLp x) (gradient φ x)) atTop (𝓝 0) :=
    harmonicBlowup_test_residual_tendsto u
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hr hφ hcφ hsφ
  obtain ⟨v, σ, h, _, _, _, _, hc, _, _, hh1, hdist, hz, henergy, ht⟩ :=
    harmonicBlowup_compactness 0 (by norm_num : (0 : ℝ) < 1 / 2) u hu hres
  obtain ⟨j, hj⟩ := (ht.eventually (Iio_mem_nhds hτ)).exists
  exact (not_lt_of_ge hj.le) (hfail (σ j) h hc hh1 hdist hz henergy)

end LiquidDrop
