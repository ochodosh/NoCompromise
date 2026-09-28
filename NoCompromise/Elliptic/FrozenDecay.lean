import NoCompromise.Elliptic.FrozenDecayUnit
import NoCompromise.Elliptic.FrozenDecayScaling

/-!
# Frozen elliptic energy and oscillation decay

Both blueprint inequalities hold for the actual weak H¹ gradient on every
concentric pair of balls. The same constant works at every center and positive
radius, for every nonsymmetric constant coefficient with the prescribed
positive ellipticity and operator-norm bounds. Smoothness and the harmonic
change of variables are proved in the supporting modules.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Full frozen decay, including dimensions two and three. The constant is
uniform in the coefficient, center, radius, function, and shrinking factor. -/
theorem frozen_decay {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        HasH1GradientOn u G (ball c r) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball c r) →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) → ‖A‖ ≤ cap →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          (∫ x in ball c (θ * r), ‖G x - ⨍ y in ball c (θ * r), G y‖ ^ 2) ≤
            C * θ ^ (n + 2) * ∫ x in ball c r, ‖G x - ⨍ y in ball c r, G y‖ ^ 2 ∧
          (∫ x in ball c (θ * r), ‖G x‖ ^ 2) ≤ C * θ ^ n * ∫ x in ball c r, ‖G x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := frozen_decay_unit_ball hn0 hn hlam hcap
  refine ⟨C, hC, ?_⟩
  intro A c r hr u G hu hw hell hbound θ hθ hθ1
  obtain ⟨hu', hw'⟩ := hu.comp_frozenBallScaling c hr A hw
  obtain ⟨ho, he⟩ := hb A (u ∘ frozenBallScaling c hr)
    (fun x => r • G (frozenBallScaling c hr x)) hu' hw' hell hbound θ hθ hθ1
  change (∫ x in ball 0 θ, ‖r • G (frozenBallScaling c hr x) -
    ⨍ y in ball 0 θ, r • G (frozenBallScaling c hr y)‖ ^ 2) ≤
      C * θ ^ (n + 2) * ∫ x in ball 0 1, ‖r • G (frozenBallScaling c hr x) -
        ⨍ y in ball 0 1, r • G (frozenBallScaling c hr y)‖ ^ 2 at ho
  rw [frozen_integral_oscillation_ballScaling hn0 G c hr hθ.le,
    frozen_integral_oscillation_ballScaling hn0 G c hr (by norm_num : (0 : ℝ) ≤ 1),
    mul_one, mul_comm r θ] at ho
  change (∫ x in ball 0 θ, ‖r • G (frozenBallScaling c hr x)‖ ^ 2) ≤
    C * θ ^ n * ∫ x in ball 0 1, ‖r • G (frozenBallScaling c hr x)‖ ^ 2 at he
  rw [frozen_integral_gradient_sq_ballScaling G c hr θ,
    frozen_integral_gradient_sq_ballScaling G c hr 1, mul_one, mul_comm r θ] at he
  have hp : 0 < r ^ 2 * (r ^ n)⁻¹ := by positivity
  constructor
  · apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [ho]
  · apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [he]

/-- The same theorem for the project's quotient H¹ space and its actual weak
gradient. No choice of pointwise representative affects either side. -/
theorem frozen_decay_h1Space {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ h : H1Space (ball c r),
        IsWeakDivergenceEquationOn (fun _ => A) h.gradientLp (fun _ => 0) (ball c r) →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) → ‖A‖ ≤ cap →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          (∫ x in ball c (θ * r), ‖h.gradientLp x -
            ⨍ y in ball c (θ * r), h.gradientLp y‖ ^ 2) ≤
            C * θ ^ (n + 2) * ∫ x in ball c r, ‖h.gradientLp x -
              ⨍ y in ball c r, h.gradientLp y‖ ^ 2 ∧
          (∫ x in ball c (θ * r), ‖h.gradientLp x‖ ^ 2) ≤
            C * θ ^ n * ∫ x in ball c r, ‖h.gradientLp x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := frozen_decay hn0 hn hlam hcap
  exact ⟨C, hC, fun A c r hr h hw he hA => hb A c r hr h h.gradientLp h.hasH1GradientOn hw he hA⟩

end LiquidDrop
