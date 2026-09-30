module

public import NoCompromise.Regularity.HarmonicBlowupUniform
public import NoCompromise.Elliptic.HarmonicDerivative

@[expose] public section

/-!
# Center value and slope bounds for the harmonic approximation

The constant depends only on the supplied quarter-disk H¹ energy bound and is
chosen before the harmonic function. Both point estimates follow from the
proved interior harmonic derivative estimates.
-/

noncomputable section
open MeasureTheory Set Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Actual center value and slope estimates from quarter-disk harmonicity and
the genuine H¹ energy. No pointwise bound is assumed. -/
theorem harmonic_center_value_gradient_bound (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∃ Ch : ℝ, 1 ≤ Ch ∧ ∀ (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      ContinuousOn h (ball 0 (1 / 4)) →
      HasH1GradientOn h (gradient h) (ball 0 (1 / 4)) →
      HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) →
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
        |h x| ^ 2 + ‖gradient h x‖ ^ 2) ≤ Cb →
      |h 0| + ‖gradient h 0‖ ≤ Ch := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_l2_bound (n := 2) (k := 1)
    (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  refine ⟨2 * C * Real.sqrt Cb + 1, by
    have : 0 ≤ 2 * C * Real.sqrt Cb := by positivity
    linarith, fun h hc hh hd he => ?_⟩
  have hi := hh.memLp_function.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hgi := hh.memLp_gradient.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hsq : (lpNorm h 2 (volume.restrict (ball 0 (1 / 4)))) ^ 2 ≤ Cb := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hh.memLp_function]
    have hle := integral_mono hi (hi.add hgi)
      (fun x => le_add_of_nonneg_right (sq_nonneg ‖gradient h x‖))
    exact hle.trans (by simpa only [Pi.add_apply, Real.norm_eq_abs] using! he)
  have hLp : lpNorm h 2 (volume.restrict (ball 0 (1 / 4))) ≤ Real.sqrt Cb := by
    nlinarith [Real.sq_sqrt hCb, Real.sqrt_nonneg Cb,
      lpNorm_nonneg (f := h) (p := 2) (μ := volume.restrict (ball 0 (1 / 4)))]
  have hs := hd.contDiffOn_of_continuous (by norm_num : 2 < 4) isOpen_ball hc
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ ball 0 (1 / 8) :=
    mem_ball_self (by norm_num)
  have hv := hb 0 h hd hh.memLp_function hs 0 (by norm_num) 0 h0
  have hg := hb 0 h hd hh.memLp_function hs 1 le_rfl 0 h0
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hv
  rw [norm_iteratedFDeriv_one] at hg
  have hgn : ‖gradient h 0‖ = ‖fderiv ℝ h 0‖ := by
    change ‖(toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm (fderiv ℝ h 0)‖ = _
    exact LinearIsometryEquiv.norm_map _ _
  rw [hgn]
  nlinarith [mul_le_mul_of_nonneg_left hLp hC.le]

end LiquidDrop
