module

public import NoCompromise.Elliptic.BoundaryNeumannQuotientBounds

@[expose] public section

/-! Positive rescaling preserves the full ambient-test conormal identity. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma IsBoundaryNeumannEquationOn.comp_scaling
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} (hr : 0 < r) (hw : IsBoundaryNeumannEquationOn A F G r) :
    IsBoundaryNeumannEquationOn (A ∘ frozenBallScaling 0 hr)
      (fun x => r • F (frozenBallScaling 0 hr x))
      (fun x => r • G (frozenBallScaling 0 hr x)) 1 := by
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr
  intro ψ hψ hcψ hsψ
  let φ := ψ ∘ e.symm
  have hφ : ContDiff ℝ 1 φ := by
    have he : ContDiff ℝ 1 e.symm := by
      change ContDiff ℝ 1 (frozenBallScaling 0 hr).symm
      rw [frozenBallScaling_symm_coe]
      exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
    exact hψ.comp he
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph e.symm
  have hsφ : tsupport φ ⊆ ball 0 r := by
    rw [tsupport_comp_eq_preimage ψ e.symm]
    intro x hx
    have hm := (frozenBallScaling_mem_ball_iff 0 (e.symm x) hr 1).mpr (hsψ hx)
    change e (e.symm x) ∈ ball 0 (r * 1) at hm
    simpa only [e.apply_symm_apply, mul_one] using hm
  have hz := hw φ hφ hcφ hsφ
  have hgrad (x) : gradient ψ x = r • gradient φ (e x) := by
    have hh := frozen_gradient_comp_ballScaling_symm 0 hr (hψ.differentiable one_ne_zero) (e x)
    change gradient φ (e x) = r⁻¹ • gradient ψ (e.symm (e x)) at hh
    rw [hh, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have heq (x) : inner ℝ (A (e x) (r • F (e x)) - r • G (e x)) (gradient ψ x) =
      r ^ 2 * inner ℝ (A (e x) (F (e x)) - G (e x)) (gradient φ (e x)) := by
    rw [map_smul, ← smul_sub, hgrad, real_inner_smul_left, real_inner_smul_right]
    ring
  change (∫ x in boundaryHalfBall 1,
    inner ℝ (A (e x) (r • F (e x)) - r • G (e x)) (gradient ψ x)) = 0
  simp_rw [heq]
  rw [integral_const_mul, boundary_integral_halfBall_comp_scaling
    (fun x => inner ℝ (A x (F x) - G x) (gradient φ x)) hr 1, mul_one,
    hz, smul_zero, mul_zero]

end LiquidDrop
