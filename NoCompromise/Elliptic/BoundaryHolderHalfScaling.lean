import NoCompromise.Elliptic.BoundaryHolderDecay
import NoCompromise.Elliptic.QuasilinearCampanatoPullback

/-! Exact half-ball integral identities and genuine weak-equation pullback under
positive similarities preserving the flat hyperplane. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_halfBall_scaling_mem {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    frozenBallScaling 0 hr x ∈ boundaryHalfBall (r * s) ↔ x ∈ boundaryHalfBall s := by
  change (frozenBallScaling 0 hr x ∈ ball 0 (r * s) ∧
    0 < (frozenBallScaling 0 hr x) (Fin.last 2)) ↔ (x ∈ ball 0 s ∧ 0 < x (Fin.last 2))
  rw [frozenBallScaling_mem_ball_iff]
  simp only [frozenBallScaling_apply, zero_add, PiLp.smul_apply, smul_eq_mul,
    mul_pos_iff_of_pos_left hr]

lemma boundary_integral_halfBall_comp_scaling {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin 3) → F) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (∫ x in boundaryHalfBall s, f (frozenBallScaling 0 hr x)) =
      (r ^ 3)⁻¹ • ∫ x in boundaryHalfBall (r * s), f x := by
  have h := frozen_integral_comp_ballScaling ((boundaryHalfBall (r * s)).indicator f) 0 hr
  have he : (fun x => (boundaryHalfBall (r * s)).indicator f (frozenBallScaling 0 hr x)) =
      (boundaryHalfBall s).indicator (fun x => f (frozenBallScaling 0 hr x)) := by
    funext x
    by_cases hx : x ∈ boundaryHalfBall s
    · simp [hx, (boundary_halfBall_scaling_mem hr x s).mpr hx]
    · simp [hx, show frozenBallScaling 0 hr x ∉ boundaryHalfBall (r * s) from
        fun ht => hx ((boundary_halfBall_scaling_mem hr x s).mp ht)]
  rw [he, integral_indicator (isOpen_boundaryHalfBall s).measurableSet,
    integral_indicator (isOpen_boundaryHalfBall (r * s)).measurableSet] at h
  exact h

lemma boundary_average_halfBall_comp_scaling {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : EuclideanSpace ℝ (Fin 3) → F) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (⨍ x in boundaryHalfBall s, f (frozenBallScaling 0 hr x)) =
      ⨍ x in boundaryHalfBall (r * s), f x := by
  have hvol := boundary_integral_halfBall_comp_scaling (fun _ => (1 : ℝ)) hr s
  simp only [integral_const, smul_eq_mul, mul_one] at hvol
  rw [average_eq, average_eq, boundary_integral_halfBall_comp_scaling, hvol,
    mul_inv, smul_smul]
  congr 1
  field_simp [hr.ne']

lemma boundary_integral_energy_scaling
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (∫ x in boundaryHalfBall s, ‖r • G (frozenBallScaling 0 hr x)‖ ^ 2) =
      r⁻¹ * ∫ x in boundaryHalfBall (r * s), ‖G x‖ ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  rw [integral_const_mul, boundary_integral_halfBall_comp_scaling (fun x => ‖G x‖ ^ 2) hr s]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

lemma boundary_normal_excess_scaling
    (n : EuclideanSpace ℝ (Fin 3))
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    boundaryNormalExcess n (fun x => r • G (frozenBallScaling 0 hr x))
      (volume.restrict (boundaryHalfBall s)) =
      r⁻¹ * boundaryNormalExcess n G (volume.restrict (boundaryHalfBall (r * s))) := by
  have hm : boundaryNormalMean n (fun x => r • G (frozenBallScaling 0 hr x))
      (volume.restrict (boundaryHalfBall s)) =
      r * boundaryNormalMean n G (volume.restrict (boundaryHalfBall (r * s))) := by
    rw [boundaryNormalMean, average_const_smul, boundary_average_halfBall_comp_scaling,
      real_inner_smul_right]
    rfl
  rw [boundaryNormalExcess, hm]
  simp only [mul_smul, ← smul_sub]
  exact boundary_integral_energy_scaling
    (fun x => G x - boundaryNormalMean n G (volume.restrict (boundaryHalfBall (r * s))) • n)
    hr s

/-- Pullback of the genuine weak equation, with both vector fields scaled by r. -/
lemma IsWeakDivergenceEquationOn.boundary_comp_scaling
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} (hr : 0 < r)
    (hw : IsWeakDivergenceEquationOn A F G (boundaryHalfBall r)) :
    IsWeakDivergenceEquationOn (A ∘ frozenBallScaling 0 hr)
      (fun x => r • F (frozenBallScaling 0 hr x))
      (fun x => r • G (frozenBallScaling 0 hr x)) (boundaryHalfBall 1) := by
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
  have hsφ : tsupport φ ⊆ boundaryHalfBall r := by
    rw [tsupport_comp_eq_preimage ψ e.symm]
    intro x hx
    have hm : e (e.symm x) ∈ boundaryHalfBall (r * 1) :=
      (boundary_halfBall_scaling_mem hr (e.symm x) 1).mpr (hsψ hx)
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
  change (∫ x, inner ℝ (A (e x) (r • F (e x)) - r • G (e x)) (gradient ψ x)) = 0
  simp_rw [heq]
  rw [integral_const_mul, frozen_integral_comp_ballScaling
    (fun x => inner ℝ (A x (F x) - G x) (gradient φ x)) 0 hr, hz, smul_zero, mul_zero]

end LiquidDrop
