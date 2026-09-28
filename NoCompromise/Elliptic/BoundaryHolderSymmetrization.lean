import NoCompromise.Elliptic.BoundaryHolderFrozen
import NoCompromise.Elliptic.FrozenDecayEstimates

/-!
# Derivatives and boundary values of smooth odd symmetrization
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_half_odd_derivative_bound {n j : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ j f x) (hfr : ContDiffAt ℝ j f (R x)) :
    ‖iteratedFDeriv ℝ j (fun y => (1 / 2 : ℝ) * (f y - f (R y))) x‖ ≤
      (1 / 2 : ℝ) * (‖iteratedFDeriv ℝ j f x‖ +
        ‖iteratedFDeriv ℝ j f (R x)‖ * ‖R.toContinuousLinearMap‖ ^ j) := by
  have hc : ContDiffAt ℝ j (f ∘ R) x := hfr.comp x R.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ j ((1 / 2 : ℝ) • (f - f ∘ R)) x‖ ≤ _
  have hsub : ContDiffAt ℝ j (f - f ∘ R) x := hf.sub hc
  rw [iteratedFDeriv_const_smul_apply (a := (1 / 2 : ℝ)) hsub, norm_smul,
    iteratedFDeriv_sub_apply hf hc]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    (frozen_norm_iteratedFDeriv_comp_linear_le R f x))

/-- A differentiable function which vanishes on the flat face has a normal
classical gradient there. This is a pointwise consequence of ordinary calculus. -/
lemma boundary_gradient_normal_at_zero {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableAt ℝ f 0)
    (hz : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin (k + 1))) r,
      x (Fin.last k) = 0 → f x = 0) :
    gradient f 0 = (gradient f 0 (Fin.last k)) • EuclideanSpace.single (Fin.last k) 1 := by
  ext i
  by_cases hi : i = Fin.last k
  · subst i
    simp
  · have he : (fun t : ℝ => f (t • EuclideanSpace.single i (1 : ℝ))) =ᶠ[𝓝 0]
        (fun _ => (0 : ℝ)) := by
      have ht : Tendsto (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ)) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ)) :=
          continuous_id.smul continuous_const
        simpa only [zero_smul] using hc.tendsto (0 : ℝ)
      filter_upwards [ht.eventually (ball_mem_nhds (0 : EuclideanSpace ℝ (Fin (k + 1))) hr)]
        with t ht
      apply hz _ ht
      simp [PiLp.smul_apply, hi]
    have hd : HasDerivAt (fun t : ℝ => f (t • EuclideanSpace.single i (1 : ℝ)))
        (gradient f 0 i) 0 := by
      have ht : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i 1) (0 : ℝ) := by
        simpa only [id_eq, one_smul] using
          (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))
      have hf' : HasFDerivAt f (fderiv ℝ f 0)
          ((fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ)) 0) := by
        simpa only [zero_smul] using hf.hasFDerivAt
      have hh := hf'.comp_hasDerivAt (0 : ℝ) ht
      simpa only [Function.comp_def, one_smul, gradient_apply_eq_fderiv_single] using hh
    have hi0 : gradient f 0 i = 0 :=
      HasDerivAt.unique (hd.congr_of_eventuallyEq he.symm) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simp [hi0, PiLp.smul_apply, hi]

end LiquidDrop
