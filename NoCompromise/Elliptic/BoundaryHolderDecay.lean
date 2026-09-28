import NoCompromise.Elliptic.BoundaryHolderDerivative
import NoCompromise.Elliptic.BoundaryHolderAffine
import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals

/-!
# Frozen half-ball decay with the actual zero Dirichlet trace

Energy decays cubically. The excess over normal affine functions decays with
the fifth power. This centering preserves the zero flat trace and bounds the
ordinary gradient variance from above.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Complete energy and normal-excess decay for genuine frozen half-ball H¹
solutions. Nonsymmetric coefficients and actual local zero trace are retained. -/
theorem boundary_frozen_decay_unit {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        HasH1GradientOn f G (boundaryHalfBall 1) →
        HasZeroFlatTraceOn f G (ball 0 1) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (boundaryHalfBall 1) →
        (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) → ‖A‖ ≤ cap →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) G
            (volume.restrict (boundaryHalfBall θ)) ≤
              C * θ ^ 5 * boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) G
                (volume.restrict (boundaryHalfBall 1)) ∧
          (∫ x in boundaryHalfBall θ, ‖G x‖ ^ 2) ≤
            C * θ ^ 3 * (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by
  obtain ⟨ρ₀, hρ₀, _, B₀, hB₀, hb₀⟩ := boundary_frozen_derivative_representative
    (j := 0) hlam hcap
  obtain ⟨ρ₁, hρ₁, _, B₁, hB₁, hb₁⟩ := boundary_frozen_derivative_representative
    (j := 1) hlam hcap
  let V := volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let D₀ := max (B₀ ^ 2 * V) (ρ₀⁻¹ ^ 3)
  let D₁ := max (B₁ ^ 2 * V) (ρ₁⁻¹ ^ 5)
  refine ⟨max D₀ D₁, (pow_pos (inv_pos.mpr hρ₀) 3).trans_le
    ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro A f G hf hT hw hell hb θ hθ hθ1
  let μ := volume.restrict (boundaryHalfBall 1)
  let ν := volume.restrict (boundaryHalfBall θ)
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using boundaryHalfBall_volume_lt_top 1⟩
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using boundaryHalfBall_volume_lt_top θ⟩
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  have hn : ‖n‖ = 1 := by simp [n]
  let b := boundaryNormalMean n G μ
  let f' := fun x => f x - inner ℝ (b • n) x
  let G' := fun x => G x - b • n
  obtain ⟨hf', hT', hw'⟩ := boundary_frozen_sub_normal_affine hf hT A hw b
  obtain ⟨v₀, _, _, heG₀, _, hd₀⟩ := hb₀ A f G hf hT hw hell hb
  have hgrad₀ : ∀ x ∈ ball 0 ρ₀, ‖gradient v₀ x‖ ≤ B₀ * lpNorm G 2 μ := by
    intro x hx
    have h := hd₀ x hx
    have he : ‖gradient v₀ x‖ = ‖iteratedFDeriv ℝ 1 v₀ x‖ := by
      simpa only [norm_iteratedFDeriv_zero] using
        sobolevChain_norm_iteratedFDeriv_gradient (j := 0) v₀ x
    rw [he]
    exact h
  have henergy := boundary_energy_decay_of_bound hf.memLp_gradient hρ₀ hB₀.le
    heG₀.symm hgrad₀ hθ hθ1
  obtain ⟨v₁, hv₁, _, heG₁, hz₁, hd₁⟩ := hb₁ A f' G' hf' hT' hw' hell hb
  have hgradC := harmonicDerivative_contDiffOn_gradient isOpen_ball hv₁
  have hdiff : ∀ x ∈ ball 0 ρ₁, DifferentiableAt ℝ (gradient v₁) x := by
    intro x hx
    exact (hgradC.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hgrad₁ : ∀ x ∈ ball 0 ρ₁, ‖fderiv ℝ (gradient v₁) x‖ ≤
      B₁ * lpNorm G' 2 μ := by
    intro x hx
    have h := hd₁ x hx
    have he : ‖fderiv ℝ (gradient v₁) x‖ = ‖iteratedFDeriv ℝ 2 v₁ x‖ := by
      rw [← norm_iteratedFDeriv_one, sobolevChain_norm_iteratedFDeriv_gradient]
    rw [he]
    exact h
  have hzgrad := boundary_gradient_normal_at_zero hρ₁
    ((hv₁.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ₁))).differentiableAt (by simp)) hz₁
  have hnormal := boundary_normal_decay_of_derivative_bound hf'.memLp_gradient
    hρ₁ hB₁.le heG₁.symm hdiff hgrad₁ hzgrad hθ hθ1
  have hGθ := hf.memLp_gradient.mono_measure
    (Measure.restrict_mono (boundaryHalfBall_mono hθ1.le) le_rfl)
  have hexc := boundary_normal_excess_sub_normal hGθ n hn b
  change boundaryNormalExcess n G' ν = boundaryNormalExcess n G ν at hexc
  change boundaryNormalExcess n G' ν ≤ D₁ * θ ^ 5 * boundaryNormalExcess n G μ at hnormal
  rw [hexc] at hnormal
  constructor
  · exact hnormal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right D₀ D₁) (pow_nonneg hθ.le _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  · exact henergy.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left D₀ D₁) (pow_nonneg hθ.le _))
      (integral_nonneg (fun _ => sq_nonneg _)))

end LiquidDrop
