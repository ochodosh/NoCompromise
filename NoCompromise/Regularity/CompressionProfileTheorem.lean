import NoCompromise.Regularity.CompressionProfile

/-! # Blueprint compression-profile lemma -/

noncomputable section
open Set InnerProductSpace
open scoped Gradient
namespace LiquidDrop

/-- Full `lem:compression-profile`, with the stronger hypothesis 0 < σ < τ
and the explicit absolute constant π² also for the regularized profile. -/
theorem compression_profile {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) :
    ContDiff ℝ 1 (compressionProfile σ τ) ∧
    LipschitzWith ⟨Real.pi / (τ - σ), (div_pos Real.pi_pos (sub_pos.mpr h)).le⟩
      (compressionProfile σ τ) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ≤ σ → compressionProfile σ τ x = 0) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), σ < ‖x‖ → ‖x‖ < τ →
      compressionProfile σ τ x = Real.sin (Real.pi * (‖x‖ - σ) / (2 * (τ - σ))) ^ 2) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), τ ≤ ‖x‖ → compressionProfile σ τ x = 1) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2),
      ‖gradient (compressionProfile σ τ) x‖ ^ 2 = Real.pi ^ 2 / (τ - σ) ^ 2 *
        compressionProfile σ τ x * (1 - compressionProfile σ τ x) ∧
      ‖gradient (compressionProfile σ τ) x‖ ^ 2 ≤ Real.pi ^ 2 / (τ - σ) ^ 2 *
        (1 - compressionProfile σ τ x ^ 2)) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ContDiff ℝ 1 (compressionBeta σ τ ε) ∧
      (∀ x, ε ≤ compressionBeta σ τ ε x ∧ compressionBeta σ τ ε x ≤ 1) ∧
      (∀ x, τ ≤ ‖x‖ → compressionBeta σ τ ε x = 1) ∧
      ∀ x, ‖gradient (compressionBeta σ τ ε) x‖ ^ 2 ≤
        Real.pi ^ 2 / (τ - σ) ^ 2 * (1 - compressionBeta σ τ ε x ^ 2) := by
  refine ⟨contDiff_compressionProfile hσ h, lipschitzWith_compressionProfile h,
    fun _ hx => compressionRadialProfile_zero h hx, ?_,
    fun _ hx => compressionRadialProfile_one h hx,
    fun x => ⟨compressionProfile_gradient_sq hσ h x,
      compressionProfile_gradient_bound hσ h x⟩, ?_⟩
  · intro x hx hx'
    simp only [compressionProfile, compressionRadialProfile, ite_eq_left hx'.le,
      ite_eq_right hx.not_ge, compressionSine]
  · intro ε hε hε1
    have hε' : ε ≤ 1 := by linarith
    refine ⟨contDiff_compressionBeta hσ h ε, compressionBeta_bounds σ τ hε.le hε', ?_,
      compressionBeta_gradient_bound hσ h hε.le hε'⟩
    intro x hx
    have he : compressionProfile σ τ x = 1 := compressionRadialProfile_one h hx
    simp only [compressionBeta, he]
    ring

end LiquidDrop
