module

public import NoCompromise.Regularity.HarmonicBlowupCompactness
public import NoCompromise.Regularity.HarmonicBlowupNormalization

@[expose] public section

/-!
# Compactness after the actual excess normalization

A Dirichlet bound of order `a²` gives a uniform H¹ bound after subtracting the
average and dividing by `a`. Actual test residuals of order `a²` become order
`a`, and therefore vanish. All conclusions concern genuine functions and the
constructed Hilbert classes of those functions.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- The exact normalization divides the actual test residual by its scale. -/
lemma harmonicBlowup_normalized_residual_bound
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) {a : ℝ} (ha : 0 < a)
    (C M : ℝ) (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hb : |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      inner ℝ (G x) (gradient φ x)| ≤ C * a ^ 2 * M) :
    |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      inner ℝ ((harmonicBlowupClass f G hf a).gradientLp x) (gradient φ x)| ≤
        (C * a) * M := by
  rw [harmonicBlowupClass_gradient_pairing, abs_mul, abs_inv, abs_of_pos ha]
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ha.le)
  convert hh using 1 <;> first | rfl | (field_simp [ha.ne'])

/-- Genuine normalized-graph compactness from quantitative energy and test
residuals. The energy bound is fixed before the sequence and does not depend
on additive constants or graph-height clamps. -/
theorem harmonicBlowup_normalized_compactness {C : ℝ} (hC : 0 ≤ C) :
    ∃ B > 0, ∀ (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
      (G : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (hf : ∀ j, HasH1GradientOn (f j) (G j) (ball 0 (1 / 2)))
      (a : ℕ → ℝ), (∀ j, 0 < a j) → Tendsto a atTop (𝓝 0) →
      (∀ j, (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖G j x‖ ^ 2) ≤
        C * (a j) ^ 2) →
      ∀ D : ℝ,
      (∀ j (φ : EuclideanSpace ℝ (Fin 2) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ ball 0 (1 / 2) → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖gradient φ x‖ ≤ M) →
          |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
            inner ℝ (G j x) (gradient φ x)| ≤ D * (a j) ^ 2 * M) →
      ∃ (v : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) (σ : ℕ → ℕ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ),
        StrictMono σ ∧ ‖v‖ ≤ B ∧
        (∀ ℓ : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) →L[ℝ] ℝ,
          Tendsto (fun j => ℓ (harmonicBlowupClass (f (σ j)) (G (σ j)) (hf (σ j)) (a (σ j))))
            atTop (𝓝 (ℓ v))) ∧
        Tendsto (fun j => (harmonicBlowupClass (f (σ j)) (G (σ j)) (hf (σ j))
          (a (σ j))).toLp) atTop (𝓝 v.toLp) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 2)) ∧
        h =ᵐ[volume.restrict (ball 0 (1 / 2))] v ∧
        gradient h =ᵐ[volume.restrict (ball 0 (1 / 2))] v.gradientLp ∧
        HasH1GradientOn h (gradient h) (ball 0 (1 / 2)) ∧
        HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 2)) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), laplacianN h x = 0) ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
          ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) ≤ B ^ 2 ∧
        Tendsto (fun j => ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
          |harmonicBlowupFunction (f (σ j)) (a (σ j)) x - h x| ^ 2) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := harmonicBlowup_normalized_bound hC
  refine ⟨B, hB, fun f G hf a ha hta he D hres => ?_⟩
  let u (j : ℕ) := harmonicBlowupClass (f j) (G j) (hf j) (a j)
  have hu (j : ℕ) : ‖u j‖ ≤ B := hb _ _ _ _ (ha j) (he j)
  have hr (j : ℕ) (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 (1 / 2))
      (M : ℝ) (hM : 0 ≤ M) (hMb : ∀ x, ‖gradient φ x‖ ≤ M) :
      |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ ((u j).gradientLp x) (gradient φ x)| ≤ (D * a j) * M :=
    harmonicBlowup_normalized_residual_bound (hf j) (ha j) D M φ
      (hres j φ hφ hcφ hsφ M hM hMb)
  have htres (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
      (hsφ : tsupport φ ⊆ ball 0 (1 / 2)) :=
    harmonicBlowup_test_residual_tendsto u
      (show Tendsto (fun j => D * a j) atTop (𝓝 0) by
        simpa only [mul_zero] using hta.const_mul D) hr hφ hcφ hsφ
  obtain ⟨v, σ, h, hσ, hv, hw, ht, hc, heq, hg, hh1, hd, hz, henergy, herr⟩ :=
    harmonicBlowup_compactness 0 (by norm_num : (0 : ℝ) < 1 / 2) u hu
      htres
  refine ⟨v, σ, h, hσ, hv, hw, ht, hc, heq, hg, hh1, hd, hz, henergy, ?_⟩
  apply herr.congr'
  apply Eventually.of_forall
  intro j
  apply integral_congr_ae
  filter_upwards [harmonicBlowupClass_coeFn (f (σ j)) (G (σ j)) (hf (σ j)) (a (σ j))]
    with x hx
  rw [hx]

end LiquidDrop
