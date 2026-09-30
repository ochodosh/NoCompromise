module

public import NoCompromise.BV.SmoothApproxLevelCharts

@[expose] public section

/-!
# Balls have smooth boundary

A ball of positive radius is the strict superlevel set `{0 < r ^ 2 - ‖x - p‖ ^ 2}` of a
smooth function whose gradient does not vanish on the zero level (the sphere), so the
regular-level criterion `hasSmoothBoundary_superlevel_of_regular` applies.
-/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- A ball of positive radius has smooth boundary (in the one-sided rigid graph-chart
convention `HasSmoothBoundary`). -/
theorem hasSmoothBoundary_ball (p : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    HasSmoothBoundary (ball p r) := by
  set u : AmbientSpace → ℝ := fun x => r ^ 2 - ‖x - p‖ ^ 2 with hu_def
  have hball : ball p r = {x | (0 : ℝ) < u x} := by
    ext x
    simp only [mem_ball, dist_eq_norm, mem_ofPred_eq, u, sub_pos]
    constructor
    · intro h
      exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    · intro h
      exact lt_of_pow_lt_pow_left₀ 2 hr.le h
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  rw [hball]
  refine hasSmoothBoundary_superlevel_of_regular hsmooth ?_
  intro x hx hgrad
  have hd : HasFDerivAt u
      (-(2 • (innerSL ℝ (x - p)).comp (ContinuousLinearMap.id ℝ AmbientSpace))) x := by
    have h1 : HasFDerivAt (fun y : AmbientSpace => y - p)
        (ContinuousLinearMap.id ℝ AmbientSpace) x :=
      (hasFDerivAt_id x).sub_const p
    exact h1.norm_sq.const_sub (r ^ 2)
  have hfd : fderiv ℝ u x = 0 := by
    have : fderiv ℝ u x = InnerProductSpace.toDual ℝ AmbientSpace (gradient u x) := by
      simp [gradient]
    rw [this, hgrad, map_zero]
  have hnorm : ‖x - p‖ ^ 2 = r ^ 2 := by
    have : r ^ 2 - ‖x - p‖ ^ 2 = 0 := hx
    linarith
  have hval := congrArg (fun L : AmbientSpace →L[ℝ] ℝ => L (x - p)) (hd.fderiv.symm.trans hfd)
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    zero_apply, hnorm, nsmul_eq_mul, Nat.cast_ofNat] at hval
  have : 0 < r ^ 2 := by positivity
  linarith

end LiquidDrop
