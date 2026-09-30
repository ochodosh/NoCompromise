module

public import NoCompromise.Elliptic.FrozenDecayAffine
public import NoCompromise.Elliptic.FrozenDecayIntegrals

@[expose] public section

/-! Both frozen decay inequalities on the unit ball, for the actual weak
H¹ solution, with one constant depending only on dimension and ellipticity. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The complete centered and noncentered decay estimates on the unit ball.
No smoothness of the initial representative is assumed. -/
theorem frozen_decay_unit_ball {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        HasH1GradientOn u G (ball 0 1) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball 0 1) →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) → ‖A‖ ≤ cap →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          (∫ x in ball 0 θ, ‖G x - ⨍ y in ball 0 θ, G y‖ ^ 2) ≤
            C * θ ^ (n + 2) * ∫ x in ball 0 1, ‖G x - ⨍ y in ball 0 1, G y‖ ^ 2 ∧
          (∫ x in ball 0 θ, ‖G x‖ ^ 2) ≤ C * θ ^ n * ∫ x in ball 0 1, ‖G x‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hb₀⟩ := frozen_derivative_unit_ball_bound (k := 0) hn hlam hcap
  obtain ⟨C₁, hC₁, hb₁⟩ := frozen_hessian_unit_ball_centered_bound hn hlam hcap
  let V := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let D₀ := max (C₀ ^ 2 * V) ((2 : ℝ) ^ n)
  let D₁ := max (C₁ ^ 2 * V) ((2 : ℝ) ^ (n + 2))
  refine ⟨max D₀ D₁, lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) n)
    ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro A u G hu hw hell hbound θ hθ hθ1
  obtain ⟨w, hwc, hew, heG⟩ := exists_frozen_smooth_representative hn isOpen_ball hu A hw hlam hell
  have hHw : HasH1GradientOn w G (ball 0 1) :=
    ⟨hu.toHasWeakGradientOn.congr_ae hew.symm EventuallyEq.rfl,
      hu.memLp_function.ae_eq hew.symm, hu.memLp_gradient⟩
  have hgrad : ∀ x ∈ ball 0 (1 / 2 : ℝ),
      ‖gradient w x‖ ≤ C₀ * lpNorm G 2 (volume.restrict (ball 0 1)) := by
    intro x hx
    have hh := hb₀ A w G hHw hw hell hbound hwc x hx
    have he : ‖gradient w x‖ = ‖iteratedFDeriv ℝ 1 w x‖ := by
      simpa only [norm_iteratedFDeriv_zero] using
        sobolevChain_norm_iteratedFDeriv_gradient (j := 0) w x
    rwa [he]
  have hgradC := harmonicDerivative_contDiffOn_gradient isOpen_ball hwc
  have hdiff : ∀ x ∈ ball 0 (1 / 2 : ℝ), DifferentiableAt ℝ (gradient w) x := by
    intro x hx
    exact (hgradC.contDiffAt (isOpen_ball.mem_nhds
      ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx))).differentiableAt (by simp)
  have hosc := frozen_oscillation_decay_of_unit_derivative_bound hn0 hu.memLp_gradient heG.symm
    hdiff hC₁.le (fun x hx => hb₁ A w G hHw hw hell hbound hwc _ x hx) hθ hθ1
  have henergy := frozen_energy_decay_of_unit_bound hn0 hu.memLp_gradient heG.symm
    hC₀.le hgrad hθ hθ1
  constructor
  · exact hosc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right D₀ D₁) (pow_nonneg hθ.le _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  · exact henergy.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left D₀ D₁) (pow_nonneg hθ.le _))
      (integral_nonneg (fun _ => sq_nonneg _)))

end LiquidDrop
