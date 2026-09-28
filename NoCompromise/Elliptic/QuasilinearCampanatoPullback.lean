import NoCompromise.Elliptic.CampanatoHolder

/-! Genuine similarity pullback for variable-coefficient weak equations and
pointwise derivatives. This supports local Campanato applications on interior balls. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma quasilinear_ballScaling_dist {n : ℕ} (c x y : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    dist (frozenBallScaling c hr x) (frozenBallScaling c hr y) = r * dist x y := by
  simp only [frozenBallScaling_apply, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr]

lemma quasilinear_ballScaling_symm_dist {n : ℕ} (c x y : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    dist ((frozenBallScaling c hr).symm x) ((frozenBallScaling c hr).symm y) =
      r⁻¹ * dist x y := by
  simp only [frozenBallScaling_symm_apply, dist_eq_norm, ← smul_sub,
    sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]

lemma quasilinear_ballScaling_lipschitz {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : LipschitzWith ‖r‖₊ (frozenBallScaling c hr) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [quasilinear_ballScaling_dist c x y hr]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr, le_refl]

lemma quasilinear_ballScaling_symm_lipschitz {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : LipschitzWith ‖r⁻¹‖₊ (frozenBallScaling c hr).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [quasilinear_ballScaling_symm_dist c x y hr]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), le_refl]

lemma quasilinear_ballScaling_maps_unit {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : MapsTo (frozenBallScaling c hr) (ball 0 1) (ball c r) := by
  intro x hx
  simpa only [mul_one] using (frozenBallScaling_mem_ball_iff c x hr 1).mpr hx

/-- Genuine H¹ pullback requires no equation or constant-coefficient premise. -/
theorem HasH1GradientOn.comp_campanatoBallScaling {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hu : HasH1GradientOn u F (ball c r)) :
    HasH1GradientOn (u ∘ frozenBallScaling c hr)
      (fun x => r • F (frozenBallScaling c hr x)) (ball 0 1) := by
  have hchain := (hu.comp_homeomorph_on isOpen_ball isOpen_ball (frozenBallScaling c hr)
    (quasilinear_ballScaling_lipschitz c hr) (quasilinear_ballScaling_symm_lipschitz c hr)
    (quasilinear_ballScaling_maps_unit c hr)).1
  have hd (x) : (fderiv ℝ (frozenBallScaling c hr) x).adjoint =
      r • ContinuousLinearMap.id ℝ _ := by
    rw [frozenBallScaling_fderiv]
    simp only [map_smul, ContinuousLinearMap.adjoint_id]
  simpa only [hd, smul_apply, ContinuousLinearMap.id_apply] using hchain

/-- Both the weak gradient and the vector datum scale by r. The coefficient
field is only composed with the similarity, so its ellipticity is unchanged. -/
theorem IsWeakDivergenceEquationOn.comp_campanatoBallScaling {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hw : IsWeakDivergenceEquationOn A F G (ball c r)) :
    IsWeakDivergenceEquationOn (A ∘ frozenBallScaling c hr)
      (fun x => r • F (frozenBallScaling c hr x))
      (fun x => r • G (frozenBallScaling c hr x)) (ball 0 1) := by
  let e := frozenBallScaling c hr
  intro ψ hψ hcψ hsψ
  let φ := ψ ∘ e.symm
  have hφ : ContDiff ℝ 1 φ := by
    have he : ContDiff ℝ 1 e.symm := by
      change ContDiff ℝ 1 (frozenBallScaling c hr).symm
      rw [frozenBallScaling_symm_coe]
      exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
    exact hψ.comp he
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph e.symm
  have hsφ : tsupport φ ⊆ ball c r := by
    rw [tsupport_comp_eq_preimage ψ e.symm]
    intro x hx
    have hm : MapsTo e (ball 0 1) (ball c r) := quasilinear_ballScaling_maps_unit c hr
    simpa only [e.apply_symm_apply] using hm (hsψ hx)
  have hz := hw φ hφ hcφ hsφ
  have hgrad (x) : gradient ψ x = r • gradient φ (e x) := by
    have hh := frozen_gradient_comp_ballScaling_symm c hr (hψ.differentiable one_ne_zero) (e x)
    change gradient φ (e x) = r⁻¹ • gradient ψ (e.symm (e x)) at hh
    rw [hh, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have heq (x) : inner ℝ (A (e x) (r • F (e x)) - r • G (e x)) (gradient ψ x) =
      r ^ 2 * inner ℝ (A (e x) (F (e x)) - G (e x)) (gradient φ (e x)) := by
    rw [map_smul, ← smul_sub, hgrad, real_inner_smul_left, real_inner_smul_right]
    ring
  change (∫ x, inner ℝ (A (e x) (r • F (e x)) - r • G (e x)) (gradient ψ x)) = 0
  simp_rw [heq]
  rw [integral_const_mul, frozen_integral_comp_ballScaling
    (fun x => inner ℝ (A x (F x) - G x) (gradient φ x)) c hr, hz, smul_zero, mul_zero]

lemma quasilinear_gradient_comp_ballScaling_symm_at {n : ℕ}
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : DifferentiableAt ℝ v ((frozenBallScaling c hr).symm x)) :
    gradient (v ∘ (frozenBallScaling c hr).symm) x =
      r⁻¹ • gradient v ((frozenBallScaling c hr).symm x) := by
  have hd : HasFDerivAt (frozenBallScaling c hr).symm
      ((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _) x := by
    rw [frozenBallScaling_symm_coe]
    exact ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).const_smul r⁻¹
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left,
    (hv.hasFDerivAt.comp x hd).fderiv]
  simp

end LiquidDrop
