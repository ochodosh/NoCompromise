import NoCompromise.Elliptic.NondivSchauderScalingNorm
import NoCompromise.Elliptic.NondivSchauderEquation

/-!
# Exact similarity pullback of the distributional equation

The coefficient field is composed with x↦c+rx, the drift is multiplied by r,
and the scalar source by r². These are actual changes of variables in the
compact-test identities; ellipticity is therefore unchanged.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsWeakNondivergenceEquationOn.mono {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakNondivergenceEquationOn A b z f U) (hVU : V ⊆ U) :
    IsWeakNondivergenceEquationOn A b z f V :=
  fun φ hφ hcφ hsφ => he φ hφ hcφ (hsφ.trans hVU)

lemma IsWeakScalarDivergenceEquationOn.congr_data {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D D' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g g' : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakScalarDivergenceEquationOn A D g U) (hD : EqOn D D' U)
    (hg : EqOn g g' U) : IsWeakScalarDivergenceEquationOn A D' g' U := by
  intro φ hφ hcφ hsφ
  have hL : (∫ x, inner ℝ (A x (D' x)) (gradient φ x)) =
      ∫ x, inner ℝ (A x (D x)) (gradient φ x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change inner ℝ (A x (D' x)) (gradient φ x) = inner ℝ (A x (D x)) (gradient φ x)
      by_cases hx : x ∈ U
      · rw [hD hx]
      · rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h))]
        simp only [inner_zero_right]
  have hR : (∫ x, φ x * g' x) = ∫ x, φ x * g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change φ x * g' x = φ x * g x
      by_cases hx : x ∈ U
      · rw [hg hx]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h))]
        simp only [zero_mul]
  rw [hL, hR]
  exact he φ hφ hcφ hsφ

/-- Scalar-source divergence identities scale directly, without an integrability
assumption outside the original ball. -/
theorem IsWeakScalarDivergenceEquationOn.comp_nondivBallScaling {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (he : IsWeakScalarDivergenceEquationOn A D g (ball c r)) :
    IsWeakScalarDivergenceEquationOn (A ∘ frozenBallScaling c hr)
      (fun x => r • D (frozenBallScaling c hr x))
      (fun x => r ^ 2 * g (frozenBallScaling c hr x)) (ball 0 1) := by
  let e := frozenBallScaling c hr
  intro ψ hψ hcψ hsψ
  let φ := ψ ∘ e.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have he' : ContDiff ℝ (⊤ : ℕ∞) e.symm := by
      change ContDiff ℝ (⊤ : ℕ∞) (frozenBallScaling c hr).symm
      rw [frozenBallScaling_symm_coe]
      exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
    exact hψ.comp he'
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph e.symm
  have hsφ : tsupport φ ⊆ ball c r := by
    rw [tsupport_comp_eq_preimage ψ e.symm]
    intro x hx
    have ht := quasilinear_ballScaling_maps_unit c hr (hsψ hx)
    change e (e.symm x) ∈ ball c r at ht
    simpa only [e.apply_symm_apply] using ht
  have htest := he φ hφ hcφ hsφ
  have hgrad (x) : gradient ψ x = r • gradient φ (e x) := by
    have ht := frozen_gradient_comp_ballScaling_symm c hr (hψ.differentiable (by simp)) (e x)
    change gradient φ (e x) = r⁻¹ • gradient ψ (e.symm (e x)) at ht
    rw [ht, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hL (x) : inner ℝ (A (e x) (r • D (e x))) (gradient ψ x) =
      r ^ 2 * inner ℝ (A (e x) (D (e x))) (gradient φ (e x)) := by
    rw [map_smul, hgrad, real_inner_smul_left, real_inner_smul_right]
    ring
  have hR (x) : ψ x * (r ^ 2 * g (e x)) = r ^ 2 * (φ (e x) * g (e x)) := by
    simp only [φ, Function.comp_apply, e.symm_apply_apply]
    ring
  change (∫ x, inner ℝ (A (e x) (r • D (e x))) (gradient ψ x)) =
    -(∫ x, ψ x * (r ^ 2 * g (e x)))
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul,
    frozen_integral_comp_ballScaling (fun x => inner ℝ (A x (D x)) (gradient φ x)) c hr,
    frozen_integral_comp_ballScaling (fun x => φ x * g x) c hr, htest]
  simp only [smul_eq_mul, mul_neg]

lemma nondiv_gradient_comp_ballScaling {n : ℕ}
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {z : EuclideanSpace ℝ (Fin n) → ℝ}
    (hz : DifferentiableAt ℝ z (frozenBallScaling c hr x)) :
    gradient (z ∘ frozenBallScaling c hr) x = r • gradient z (frozenBallScaling c hr x) := by
  simp only [gradient, nondiv_fderiv_comp_ballScaling c x hr hz, map_smul]

lemma nondivCoefficientDivergence_comp_ballScaling {n : ℕ}
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hA : DifferentiableAt ℝ A (frozenBallScaling c hr x)) :
    nondivCoefficientDivergence (A ∘ frozenBallScaling c hr) x =
      r • nondivCoefficientDivergence A (frozenBallScaling c hr x) := by
  simp only [nondivCoefficientDivergence, nondiv_fderiv_comp_ballScaling c x hr hA, map_smul]

/-- Exact distributional nondivergence pullback, with only local C¹ regularity of
A and z and continuity of b and f. -/
theorem IsWeakNondivergenceEquationOn.comp_nondivBallScaling {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hA : ContDiffOn ℝ 1 A (ball c r)) (hb : ContinuousOn b (ball c r))
    (hz : ContDiffOn ℝ 1 z (ball c r)) (hf : ContinuousOn f (ball c r))
    (he : IsWeakNondivergenceEquationOn A b z f (ball c r)) :
    IsWeakNondivergenceEquationOn (A ∘ frozenBallScaling c hr)
      (fun x => r • b (frozenBallScaling c hr x)) (z ∘ frozenBallScaling c hr)
      (fun x => r ^ 2 * f (frozenBallScaling c hr x)) (ball 0 1) := by
  let e := frozenBallScaling c hr
  have hm := quasilinear_ballScaling_maps_unit c hr
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  have hAc := hA.comp hec.contDiffOn hm
  have hzc := hz.comp hec.contDiffOn hm
  have hbc : ContinuousOn (fun x => r • b (e x)) (ball 0 1) := by
    simpa only [Function.comp_apply, Pi.smul_apply] using!
      (hb.comp e.continuous.continuousOn hm).const_smul r
  have hfc : ContinuousOn (fun x => r ^ 2 * f (e x)) (ball 0 1) :=
    continuousOn_const.mul (hf.comp e.continuous.continuousOn hm)
  apply (isWeakNondivergenceEquationOn_iff_divergence isOpen_ball hAc hbc hzc hfc).mpr
  have hd := (isWeakNondivergenceEquationOn_iff_divergence isOpen_ball hA hb hz hf).mp he
  apply (hd.comp_nondivBallScaling c hr).congr_data
  · intro x hx
    exact (nondiv_gradient_comp_ballScaling c x hr
      ((hz.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero)).symm
  · intro x hx
    have hAx := (hA.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero
    have hzx := (hz.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero
    dsimp [nondivDivergenceSource]
    rw [nondivCoefficientDivergence_comp_ballScaling c x hr hAx,
      nondiv_gradient_comp_ballScaling c x hr hzx, ← smul_sub,
      real_inner_smul_left, real_inner_smul_right]
    ring

end LiquidDrop
