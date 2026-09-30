module

public import NoCompromise.Sobolev.W11Calculus

@[expose] public section

/-!
# Smooth approximation in whole-space W¹,¹

Probability bump convolution gives smooth functions whose actual classical
gradients are the convolutions of the weak gradient. Both converge in L¹.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient Convolution
namespace LiquidDrop

theorem HasW11GradientOn.bump_convolution {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G univ)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ (⊤ : ℕ∞) (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) ∧
    (∀ x, gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x) ∧
    HasW11GradientOn (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) univ := by
  have hif : Integrable f := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_function
  have hiG : Integrable G := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_gradient
  have hs : ContDiff ℝ (⊤ : ℕ∞) (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hif.locallyIntegrable
  have hg := hf.toHasWeakGradientOn.gradient_convolution
    (show ContDiff ℝ 1 (φ.normed volume) from φ.contDiff_normed) φ.hasCompactSupport_normed
  refine ⟨hs, hg, ?_⟩
  refine ⟨(hasWeakGradientOn_of_contDiffOn isOpen_univ
    (hs.of_le (by simp)).contDiffOn).congr_ae EventuallyEq.rfl
      (Eventually.of_forall hg), ?_, ?_⟩
  · exact (φ.integrable_normed.integrable_convolution _ hif).integrableOn
  · exact (φ.integrable_normed.integrable_convolution _ hiG).integrableOn

theorem HasW11GradientOn.tendsto_bump_convolution {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G univ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖) l (𝓝 0) ∧
    Tendsto (fun j => ∫ x,
      ‖gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - G x‖)
      l (𝓝 0) := by
  have hif : Integrable f := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_function
  have hiG : Integrable G := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_gradient
  refine ⟨tendsto_integral_norm_bump_convolution_sub hif hφ, ?_⟩
  simp_rw [(hf.bump_convolution _).2.1]
  exact tendsto_integral_norm_bump_convolution_sub hiG hφ

end LiquidDrop
