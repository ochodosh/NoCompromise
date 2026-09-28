import NoCompromise.Elliptic.NeumannLocalizeMap
import NoCompromise.Sobolev.H1Chain

/-!
# H¹ pullback and ambient tests for a local normal chart

The global bi-Lipschitz extension constructed with the chart is used only for
the Sobolev chain rule and to define the zero extension of a pushed test.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- Pullback under a chart agreeing with a global bi-Lipschitz homeomorphism.
The gradient uses the actual derivative of the local chart. -/
theorem neumannLocalize_hasH1GradientOn
    {D : Set AmbientSpace} (hD : IsOpen D) (z : H1Space D)
    {Θ : AmbientSpace → AmbientSpace} (E : AmbientSpace ≃ₜ AmbientSpace)
    {C K : ℝ≥0} (hE : LipschitzWith C E) (hEi : LipschitzWith K E.symm)
    (hEq : EqOn Θ E (ball 0 2)) (hmaps : Θ '' boundaryHalfBall 1 ⊆ D) :
    HasH1GradientOn (fun y => z (Θ y))
      (fun y => (fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y))) (boundaryHalfBall 1) := by
  have hball : boundaryHalfBall 1 ⊆ ball (0 : AmbientSpace) 2 :=
    inter_subset_left.trans (ball_subset_ball (by norm_num))
  have hEmaps : MapsTo E (boundaryHalfBall 1) D := by
    intro y hy
    rw [← hEq (hball hy)]
    exact hmaps (mem_image_of_mem _ hy)
  have hchain := (z.hasH1GradientOn.comp_homeomorph_on
    (isOpen_boundaryHalfBall 1) hD E hE hEi hEmaps).1
  apply hchain.congr_ae
  · filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with y hy
    exact congrArg z (hEq (hball hy)).symm
  · filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with y hy
    have hnear : Θ =ᶠ[𝓝 y] E :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (hball hy)) (fun x hx => hEq hx)
    rw [← hnear.fderiv_eq, ← hnear.self_of_nhds]

/-- Pushing a compact C¹ test through the inverse of the extension gives an
ambient compact C¹ test supported in the image of the unit ball. Outside that
image it is zero, so this is the zero extension of the local pushforward. -/
theorem neumannLocalize_pushforward_test
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ 1 Θ)
    (E : AmbientSpace ≃ₜ AmbientSpace) (hEq : EqOn Θ E (ball 0 2))
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball 0 1) :
    ContDiff ℝ 1 (φ ∘ E.symm) ∧ HasCompactSupport (φ ∘ E.symm) ∧
      tsupport (φ ∘ E.symm) ⊆ Θ '' ball 0 1 ∧
      EqOn ((φ ∘ E.symm) ∘ Θ) φ (ball 0 2) := by
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hs : tsupport (φ ∘ E.symm) ⊆ Θ '' ball 0 1 := by
    intro x hx
    rw [tsupport_comp_eq_preimage] at hx
    exact ⟨E.symm x, hsφ hx, (hEq (hball (hsφ hx))).trans (E.apply_symm_apply x)⟩
  refine ⟨?_, hcφ.comp_homeomorph E.symm, hs, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : E.symm x ∈ ball 0 2
    · have hnear : Θ =ᶠ[𝓝 (E.symm x)] E :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => hEq hy)
      obtain ⟨L, hL⟩ := hreg (E.symm x) hx
      have hd : HasFDerivAt E (L : AmbientSpace →L[ℝ] AmbientSpace) (E.symm x) := by
        rw [hL]
        exact ((hΘ.differentiable one_ne_zero _).hasFDerivAt).congr_of_eventuallyEq hnear.symm
      have hi : ContDiffAt ℝ 1 E.symm x :=
        E.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) hd
          (hΘ.contDiffAt.congr_of_eventuallyEq hnear.symm)
      exact hφ.contDiffAt.comp x hi
    · have hn : x ∉ tsupport (φ ∘ E.symm) := by
        intro ht
        rw [tsupport_comp_eq_preimage] at ht
        exact hx (hball (hsφ ht))
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)
  · intro y hy
    change φ (E.symm (Θ y)) = φ y
    rw [hEq hy, E.symm_apply_apply]

end LiquidDrop
