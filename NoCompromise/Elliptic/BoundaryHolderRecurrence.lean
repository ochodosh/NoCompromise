import NoCompromise.Elliptic.BoundaryHolderRadiusDecay
import NoCompromise.Elliptic.BoundaryHolderComparisonBounds
import NoCompromise.Elliptic.BoundaryHolderTransfer
import NoCompromise.Elliptic.CampanatoGrowthStep

/-! The actual boundary energy and normal-excess recurrences, with constants
selected before the exponent, radius, coefficients, and weak solution. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Both recurrences follow from the constructed frozen solution and the proved
boundary decay. The weak gradient and the actual zero flat trace are hypotheses;
no comparison, regularity, or energy inequality is assumed. -/
theorem boundary_holder_recurrence_constants {lam cap HA HG : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ (a r : ℝ), 0 < r →
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
        HasH1GradientOn u F (boundaryHalfBall r) →
        HasZeroFlatTraceOn u F (ball 0 r) →
        IsWeakDivergenceEquationOn A F G (boundaryHalfBall r) →
        AEStronglyMeasurable A (volume.restrict (boundaryHalfBall r)) →
        (∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖A x‖ ≤ cap) →
        MemLp G 2 (volume.restrict (boundaryHalfBall r)) →
        (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A 0 ξ) ξ) → ‖A 0‖ ≤ cap →
        (∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖A x - A 0‖ ≤ HA * r ^ a) →
        (∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖G x - G 0‖ ≤ HG * r ^ a) →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          (∫ x in boundaryHalfBall (θ * r), ‖F x‖ ^ 2) ≤
            C * (θ ^ (3 : ℝ) + r ^ (2 * a)) * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
              D * r ^ (3 + 2 * a) ∧
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
              (volume.restrict (boundaryHalfBall (θ * r))) ≤
            C * θ ^ (5 : ℝ) * boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
                (volume.restrict (boundaryHalfBall r)) +
              C * r ^ (2 * a) * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
              D * r ^ (3 + 2 * a) := by
  obtain ⟨K, hK, hfrozen⟩ := boundary_frozen_decay_radius hlam hcap
  let P := (2 + 4 * K) * (2 / lam ^ 2)
  let V := volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let C := 4 * K + P * HA ^ 2 + 1
  let D := P * HG ^ 2 * V
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D, V]; positivity
  refine ⟨C, hC, D, hD, ?_⟩
  intro a r hr u F G A hu hT hw hA hbA hG hell hAc hBA hQG θ hθ hθ1
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  have hn : ‖n‖ = 1 := by simp [n]
  obtain ⟨h, hTh, hh, herr⟩ := exists_boundary_comparison_bounded_oscillation r hu hT hw
    hA hbA hG hlam hell (mul_nonneg hHA (Real.rpow_nonneg hr.le a))
      (mul_nonneg hHG (Real.rpow_nonneg hr.le a)) hBA hQG
  obtain ⟨hNdec, hEdec⟩ := hfrozen (A 0) h h.gradientLp r hr h.hasH1GradientOn hTh hh
    hell hAc θ hθ hθ1
  have hEt := boundary_transfer_energy_decay hu.memLp_gradient h.hasH1GradientOn.memLp_gradient
    hr hθ hθ1 hK.le hEdec
  have hNt := boundary_transfer_normal_decay hu.memLp_gradient h.hasH1GradientOn.memLp_gradient
    n hn hr hθ hθ1 hK.le hNdec
  have herror := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2 + 4 * K by positivity)
  have hvolume : volume.real (boundaryHalfBall r) ≤ r ^ 3 * V := by
    calc
      _ ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) r) :=
        measureReal_mono inter_subset_left
      _ = _ := frozen_real_volume_ball (by norm_num) 0 hr.le
  have hpower : r ^ (2 * a) * r ^ (3 : ℕ) = r ^ (3 + 2 * a) := by
    rw [Real.rpow_add hr, Real.rpow_ofNat]
    ring
  have he2 : (2 + 4 * K) * (∫ x in boundaryHalfBall r, ‖F x - h.gradientLp x‖ ^ 2) ≤
      P * HA ^ 2 * r ^ (2 * a) * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
        D * r ^ (3 + 2 * a) := by
    calc
      _ ≤ (2 + 4 * K) * ((2 / lam ^ 2) *
          ((HA * r ^ a) ^ 2 * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
            (HG * r ^ a) ^ 2 * volume.real (boundaryHalfBall r))) := herror
      _ ≤ (2 + 4 * K) * ((2 / lam ^ 2) *
          ((HA * r ^ a) ^ 2 * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
            (HG * r ^ a) ^ 2 * (r ^ 3 * V))) := by
        gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, campanato_square_rpow hr.le a]
        dsimp [P, D]
        rw [← hpower]
        ring
  have hc₁ : 4 * K ≤ C := by
    have hp : 0 ≤ P * HA ^ 2 := by positivity
    dsimp [C]
    linarith only [hp]
  have hc₂ : P * HA ^ 2 ≤ C := by dsimp [C]; linarith only [hK]
  have henergy : 0 ≤ ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hexcess : 0 ≤ boundaryNormalExcess n F (volume.restrict (boundaryHalfBall r)) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [mul_comm r θ] at hEt hNt
  constructor
  · have hraw : (∫ x in boundaryHalfBall (θ * r), ‖F x‖ ^ 2) ≤
        (4 * K * θ ^ (3 : ℕ) + P * HA ^ 2 * r ^ (2 * a)) *
          (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) + D * r ^ (3 + 2 * a) := by
      nlinarith only [hEt, he2]
    apply hraw.trans
    refine add_le_add ?_ le_rfl
    apply mul_le_mul_of_nonneg_right _ henergy
    rw [Real.rpow_ofNat, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hc₁ (pow_nonneg hθ.le 3))
      (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hr.le (2 * a)))
  · have hraw : boundaryNormalExcess n F (volume.restrict (boundaryHalfBall (θ * r))) ≤
        4 * K * θ ^ (5 : ℕ) * boundaryNormalExcess n F (volume.restrict (boundaryHalfBall r)) +
          P * HA ^ 2 * r ^ (2 * a) * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
          D * r ^ (3 + 2 * a) := by
      nlinarith only [hNt, he2]
    apply hraw.trans
    rw [Real.rpow_ofNat]
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ (pow_nonneg hθ.le 5)) hexcess)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hr.le (2 * a))) henergy)) le_rfl

end LiquidDrop
