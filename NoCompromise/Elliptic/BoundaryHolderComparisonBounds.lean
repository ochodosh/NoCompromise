module

public import NoCompromise.Elliptic.BoundaryHolderComparison
public import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals
public import NoCompromise.Elliptic.CampanatoGrowthComparison

@[expose] public section

/-! Oscillation bounds for the actual frozen half-ball comparison. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- No assumed frozen solution or tested energy inequality is used. The actual
replacement is constructed and its actual zero flat trace is retained. -/
theorem exists_boundary_comparison_bounded_oscillation (r : ℝ)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u F (boundaryHalfBall r))
    (hT : HasZeroFlatTraceOn u F (ball 0 r))
    (hw : IsWeakDivergenceEquationOn A F G (boundaryHalfBall r))
    (hA : AEStronglyMeasurable A (volume.restrict (boundaryHalfBall r)))
    {cap lam B Q : ℝ}
    (hbA : ∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict (boundaryHalfBall r))) (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A 0 ξ) ξ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hBA : ∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖A x - A 0‖ ≤ B)
    (hQG : ∀ᵐ x ∂volume.restrict (boundaryHalfBall r), ‖G x - G 0‖ ≤ Q) :
    ∃ h : H1Space (boundaryHalfBall r), HasZeroFlatTraceOn h h.gradientLp (ball 0 r) ∧
      IsWeakDivergenceEquationOn (fun _ => A 0) h.gradientLp (fun _ => 0) (boundaryHalfBall r) ∧
      (∫ x in boundaryHalfBall r, ‖F x - h.gradientLp x‖ ^ 2) ≤
        (2 / lam ^ 2) * (B ^ 2 * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) +
          Q ^ 2 * volume.real (boundaryHalfBall r)) := by
  let w := H1Space.ofFunction u F hu
  have he : w.gradientLp =ᵐ[volume.restrict (boundaryHalfBall r)] F :=
    H1Space.gradientLp_ofFunction u F hu
  have hTw : HasZeroFlatTraceOn w w.gradientLp (ball 0 r) :=
    hT.congr_ae isOpen_ball.measurableSet (H1Space.coeFn_ofFunction u F hu).symm he.symm
  obtain ⟨h, _, hTh, hh, herr⟩ := exists_boundary_campanato_comparison isOpen_ball
    isBounded_ball A (A 0) G (G 0) w hA hbA hG hlam hell
      (hw.congr_gradient_ae (isOpen_boundaryHalfBall r).measurableSet he.symm) hTw
  have herr' : (∫ x in boundaryHalfBall r, ‖F x - h.gradientLp x‖ ^ 2) ≤
      (2 / lam ^ 2) * (∫ x in boundaryHalfBall r, ‖A x - A 0‖ ^ 2 * ‖F x‖ ^ 2) +
      (2 / lam ^ 2) * (∫ x in boundaryHalfBall r, ‖G x - G 0‖ ^ 2) := by
    have hi₁ : (∫ x in boundaryHalfBall r, ‖F x - h.gradientLp x‖ ^ 2) =
        ∫ x in boundaryHalfBall r, ‖w.gradientLp x - h.gradientLp x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    have hi₂ : (∫ x in boundaryHalfBall r, ‖A x - A 0‖ ^ 2 * ‖F x‖ ^ 2) =
        ∫ x in boundaryHalfBall r, ‖A x - A 0‖ ^ 2 * ‖w.gradientLp x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    rwa [hi₁, hi₂]
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall r)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top r⟩
  have ha := campanato_integral_bounded_coefficient_sq hu.memLp_gradient
    (hA.sub aestronglyMeasurable_const) hB hBA
  have hg := campanato_integral_sq_le_measure (hG.sub (memLp_const (G 0))) hQ hQG
  simp only [Measure.real, Measure.restrict_apply_univ] at hg
  refine ⟨h, hTh, hh, herr'.trans ?_⟩
  have hc : 0 ≤ 2 / lam ^ 2 := by positivity
  calc
    _ ≤ (2 / lam ^ 2) * (B ^ 2 * (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2)) +
        (2 / lam ^ 2) * (Q ^ 2 * volume.real (boundaryHalfBall r)) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hc) (mul_le_mul_of_nonneg_left hg hc)
    _ = _ := by ring

end LiquidDrop
