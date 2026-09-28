import NoCompromise.Elliptic.NeumannLocalizeIntegrals
import NoCompromise.Elliptic.NeumannLocalizeCoefficient

/-!
# A global weak Neumann solution in flat normal coordinates

The equation uses the convention `Δz = f` and outward flux `h`. Positive
normal coordinates point inward, so the flat boundary datum is minus the
outward flux times the surface Jacobian.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient ENNReal NNReal

namespace LiquidDrop

lemma neumannLocalize_gradient_comp
    {Θ : AmbientSpace → AmbientSpace} {Ψ : AmbientSpace → ℝ} {y : AmbientSpace}
    (hΘ : DifferentiableAt ℝ Θ y) (hΨ : DifferentiableAt ℝ Ψ (Θ y)) :
    gradient (Ψ ∘ Θ) y = (fderiv ℝ Θ y).adjoint (gradient Ψ (Θ y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    fderiv_comp y hΨ hΘ, ContinuousLinearMap.comp_apply]

/-- The exact flat weak equation in a placed, scaled normal chart. The
geometric premises and the homeomorphism are constructed by
`C1BoundaryChart.IsChartFor.exists_neumannLocalizeMap`. -/
theorem IsWeakNeumannSolution.normal_chart_test_eq
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) (E : AmbientSpace ≃ₜ AmbientSpace)
    (hEq : EqOn (neumannLocalizeMap c a ρ) E (ball 0 2))
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    (hregion : neumannLocalizeMap c a ρ '' ball 0 2 ⊆ c.region)
    (hupper : neumannLocalizeMap c a ρ '' boundaryHalfBall 2 ⊆ D)
    (hlower : Disjoint (neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D))
    (hface : neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball 0 1) :
    let Θ := neumannLocalizeMap c a ρ
    (∫ y in boundaryHalfBall 1,
        inner ℝ (neumannLocalizeCoefficient Θ y
          ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)) =
      -(∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y) -
        ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
          (-(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
            Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) * φ (graphBaseEmbedding t) := by
  let Θ := neumannLocalizeMap c a ρ
  let Ψ := φ ∘ E.symm
  have hΘ : ContDiff ℝ 1 Θ := contDiff_neumannLocalizeMap c hψ a ρ
  obtain ⟨hΨ, hcΨ, hsΨ, hcomp⟩ := neumannLocalize_pushforward_test hΘ E hEq hreg hφ hcφ hsφ
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hside := fun y hy => neumannLocalize_mem_domain_iff hD hupper hlower hface (y := y) hy
  have hinj : InjOn Θ (boundaryHalfBall 1) := by
    intro x hx y hy heq
    apply E.injective
    rw [← hEq (hball hx.1), ← hEq (hball hy.1)]
    exact heq
  have hgrad (y : AmbientSpace) (hy : y ∈ boundaryHalfBall 1) :
      gradient φ y = (fderiv ℝ Θ y).adjoint (gradient Ψ (Θ y)) := by
    have he : Ψ ∘ Θ =ᶠ[𝓝 y] φ :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (hball hy.1)) (fun x hx => hcomp hx)
    exact he.gradient_eq.symm.trans
      (neumannLocalize_gradient_comp (hΘ.differentiable one_ne_zero _)
        (hΨ.differentiable one_ne_zero _))
  have hsinner : tsupport (fun x => inner ℝ (z.gradientLp x) (gradient Ψ x)) ⊆ tsupport Ψ := by
    apply closure_minimal ?_ (isClosed_tsupport Ψ)
    intro x hx
    by_contra hn
    apply hx
    change inner ℝ (z.gradientLp x) (gradient Ψ x) = 0
    rw [gradient_eq_zero_of_notMem_tsupport hn, inner_zero_right]
  have henergy : (∫ x in D, inner ℝ (z.gradientLp x) (gradient Ψ x)) =
      ∫ y in boundaryHalfBall 1, inner ℝ
        (neumannLocalizeCoefficient Θ y ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y))))
        (gradient φ y) := by
    rw [neumannLocalize_integral_domain hD E hEq hside (hsinner.trans hsΨ)]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (isOpen_boundaryHalfBall 1).measurableSet
      (fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt) hinj]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall 1).measurableSet
    intro y hy
    change |(fderiv ℝ Θ y).det| * inner ℝ (z.gradientLp (Θ y)) (gradient Ψ (Θ y)) =
      inner ℝ (neumannLocalizeCoefficient Θ y
        ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)
    rw [hgrad y hy]
    exact (neumannLocalize_dirichlet_pairing Θ (hreg y (hball hy.1))
      (z.gradientLp (Θ y)) (gradient Ψ (Θ y))).symm
  have hforcing : (∫ x in D, f₀ x * Ψ x) =
      ∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y := by
    rw [neumannLocalize_integral_domain hD E hEq hside
      (tsupport_mul_subset_right.trans hsΨ)]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (isOpen_boundaryHalfBall 1).measurableSet
      (fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt) hinj]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall 1).measurableSet
    intro y hy
    have hp : Ψ (Θ y) = φ y := hcomp (hball hy.1)
    change |(fderiv ℝ Θ y).det| * (f₀ (Θ y) * Ψ (Θ y)) =
      f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y
    rw [hp]
    ring
  have hboundary := neumannLocalize_boundary_integral hc a hρ E hEq hregion
    (fun y hy hfront => neumannLocalize_face_of_mem_frontier hD hupper hlower hy hfront) h₀ hsφ
  have hw := hz.ambient_test_eq hf hh hΨ hcΨ
  rw [henergy, hforcing] at hw
  dsimp only [Function.comp_def] at hw
  rw [hboundary] at hw
  simpa only [neg_mul, integral_neg, sub_neg_eq_add] using hw

/-- A global weak Neumann solution admits a flat normal chart with its actual
H¹ pullback and the exact forcing and boundary area densities. The global
extension and transformed equation are constructed from the given smooth
boundary chart. Continuous representatives are instances of the stated
almost-everywhere representative hypotheses. -/
theorem IsWeakNeumannSolution.exists_normal_chart
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0,
      let a := graphProjectionN 2 (c.placement.symm p)
      let Θ := neumannLocalizeMap c a ρ
      Θ 0 = p ∧ ContDiff ℝ 1 Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧ Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      HasH1GradientOn (fun y => z (Θ y))
        (fun y => (fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y))) (boundaryHalfBall 1) ∧
      ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ ball 0 1 →
        (∫ y in boundaryHalfBall 1,
          inner ℝ (neumannLocalizeCoefficient Θ y
            ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)) =
          -(∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y) -
            ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
              (-(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
                Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) *
                  φ (graphBaseEmbedding t) := by
  obtain ⟨ρ, hρ, h0, hΘ, hinj, hreg, hregion, hupper, hlower, hface, hopen,
    E, C, K, hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap hψ hp hpc
  refine ⟨ρ, hρ, h0, hΘ, hinj, hreg, hregion, hupper, hlower, hface, hopen, ?_, ?_⟩
  · exact neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
      ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  · intro φ hφ hcφ hsφ
    exact hz.normal_chart_test_eq hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      hφ hcφ hsφ

end LiquidDrop
