import NoCompromise.Elliptic.FrozenDecayIntegrals

/-! Similarity changes preserve the actual frozen weak equation. Exact
Lebesgue integral and average formulas retain the same decay constant at
all centers and positive radii. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The similarity from the unit ball to a ball of positive radius. -/
def frozenBallScaling {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.smul (Units.mk0 r hr.ne')).trans (Homeomorph.addLeft c)

lemma frozenBallScaling_apply {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : frozenBallScaling c hr x = c + r • x := rfl

lemma frozenBallScaling_symm_apply {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : (frozenBallScaling c hr).symm x = r⁻¹ • (x - c) := by
  change r⁻¹ • (-c + x) = r⁻¹ • (x - c)
  congr 1
  abel

lemma frozenBallScaling_symm_coe {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : ⇑(frozenBallScaling c hr).symm = fun x => r⁻¹ • (x - c) :=
  funext (fun x => frozenBallScaling_symm_apply c x hr)

lemma frozenBallScaling_mem_ball_iff {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    frozenBallScaling c hr x ∈ ball c (r * s) ↔ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s := by
  simp only [frozenBallScaling_apply, mem_ball, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_lt_mul_iff_right₀ hr]

lemma frozenBallScaling_fderiv {n : ℕ} (c x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (frozenBallScaling c hr) x = r • ContinuousLinearMap.id ℝ _ := by
  exact (((hasFDerivAt_id x).const_smul r).const_add c).fderiv

lemma frozen_gradient_comp_ballScaling_symm {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Differentiable ℝ φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (φ ∘ (frozenBallScaling c hr).symm) x =
      r⁻¹ • gradient φ ((frozenBallScaling c hr).symm x) := by
  have hd : HasFDerivAt (frozenBallScaling c hr).symm
      ((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _) x := by
    rw [frozenBallScaling_symm_coe]
    exact ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).const_smul r⁻¹
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left,
    ((hφ _).hasFDerivAt.comp x hd).fderiv]
  simp

lemma frozen_integral_comp_ballScaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (∫ x, f (frozenBallScaling c hr x)) = (r ^ n)⁻¹ • ∫ x, f x := by
  have h := Measure.integral_comp_smul_of_nonneg volume (fun x => f (c + x)) r (hR := hr.le)
  rw [integral_add_left_eq_self] at h
  simpa only [frozenBallScaling_apply, finrank_euclideanSpace, Fintype.card_fin] using h

lemma frozen_integral_ball_comp_ballScaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) s, f (frozenBallScaling c hr x)) =
      (r ^ n)⁻¹ • ∫ x in ball c (r * s), f x := by
  have h := frozen_integral_comp_ballScaling ((ball c (r * s)).indicator f) c hr
  have he : (fun x => (ball c (r * s)).indicator f (frozenBallScaling c hr x)) =
      (ball (0 : EuclideanSpace ℝ (Fin n)) s).indicator
        (fun x => f (frozenBallScaling c hr x)) := by
    funext x
    by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s
    · have hx' := (frozenBallScaling_mem_ball_iff c x hr s).mpr hx
      simp [hx, hx']
    · have hx' : frozenBallScaling c hr x ∉ ball c (r * s) :=
        fun ht => hx ((frozenBallScaling_mem_ball_iff c x hr s).mp ht)
      simp [hx, hx']
  rw [he, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at h
  exact h

/-- Similarity pullback preserves genuine H¹ data and the original constant
coefficient weak equation; the new gradient is `r • G(c+r x)`. -/
theorem HasH1GradientOn.comp_frozenBallScaling {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hu : HasH1GradientOn u G (ball c r))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball c r)) :
    HasH1GradientOn (u ∘ frozenBallScaling c hr)
      (fun x => r • G (frozenBallScaling c hr x)) (ball 0 1) ∧
      IsWeakDivergenceEquationOn (fun _ => A)
        (fun x => r • G (frozenBallScaling c hr x)) (fun _ => 0) (ball 0 1) := by
  let e := frozenBallScaling c hr
  have hl : LipschitzWith ‖r‖₊ e := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (c + r • x) (c + r • y) ≤ _
    rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, dist_eq_norm]
    rfl
  have hi : LipschitzWith ‖r⁻¹‖₊ e.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((frozenBallScaling c hr).symm x) ((frozenBallScaling c hr).symm y) ≤ _
    rw [frozenBallScaling_symm_apply, frozenBallScaling_symm_apply, dist_eq_norm,
      ← smul_sub, sub_sub_sub_cancel_right, norm_smul, dist_eq_norm]
    rfl
  have hm : MapsTo e (ball 0 1) (ball c r) := by
    intro x hx
    simpa only [mul_one] using (frozenBallScaling_mem_ball_iff c x hr 1).mpr hx
  have hchain := (hu.comp_homeomorph_on isOpen_ball isOpen_ball e hl hi hm).1
  have hd (x) : (fderiv ℝ e x).adjoint = r • ContinuousLinearMap.id ℝ _ := by
    rw [frozenBallScaling_fderiv]
    simp only [map_smul, ContinuousLinearMap.adjoint_id]
  simp only [hd, smul_apply, ContinuousLinearMap.id_apply] at hchain
  refine ⟨hchain, ?_⟩
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
    simpa only [e.apply_symm_apply] using hm (hsψ hx)
  have hz : (∫ x, inner ℝ (A (G x)) (gradient φ x)) = 0 := by
    simpa only [sub_zero] using hw φ hφ hcφ hsφ
  have hgrad (x) : gradient ψ x = r • gradient φ (e x) := by
    have hh := frozen_gradient_comp_ballScaling_symm c hr (hψ.differentiable one_ne_zero) (e x)
    change gradient φ (e x) = r⁻¹ • gradient ψ (e.symm (e x)) at hh
    rw [hh, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have heq (x) : inner ℝ (A (r • G (e x)) - 0) (gradient ψ x) =
      r ^ 2 * inner ℝ (A (G (e x))) (gradient φ (e x)) := by
    rw [sub_zero, map_smul, hgrad, real_inner_smul_left, real_inner_smul_right]
    ring
  change (∫ x, inner ℝ (A (r • G (e x)) - 0) (gradient ψ x)) = 0
  simp_rw [heq]
  rw [integral_const_mul, frozen_integral_comp_ballScaling
    (fun x => inner ℝ (A (G x)) (gradient φ x)) c hr, hz, smul_zero, mul_zero]

/-- Ball averages are invariant under similarity pullback. -/
lemma frozen_average_comp_ballScaling {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : EuclideanSpace ℝ (Fin n) → F) (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    (⨍ x in ball (0 : EuclideanSpace ℝ (Fin n)) s, f (frozenBallScaling c hr x)) =
      ⨍ x in ball c (r * s), f x := by
  have hreal (T : Set (EuclideanSpace ℝ (Fin n))) :
      (volume.restrict T).real univ = volume.real T := by simp [Measure.real]
  have hvol : volume.real (ball c (r * s)) =
      r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) s) := by
    rw [frozen_real_volume_ball hn _ (mul_nonneg hr.le hs),
      frozen_real_volume_ball hn _ hs, mul_pow]
    ring
  rw [average_eq, average_eq, hreal, hreal,
    frozen_integral_ball_comp_ballScaling, hvol, mul_inv, smul_smul]
  congr 1
  ring

lemma frozen_integral_gradient_sq_ballScaling {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) s, ‖r • G (frozenBallScaling c hr x)‖ ^ 2) =
      (r ^ 2 * (r ^ n)⁻¹) * ∫ x in ball c (r * s), ‖G x‖ ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  rw [integral_const_mul, frozen_integral_ball_comp_ballScaling
    (fun x => ‖G x‖ ^ 2) c hr s]
  simp only [smul_eq_mul]
  ring

lemma frozen_integral_oscillation_ballScaling {n : ℕ} (hn : 0 < n)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) s,
      ‖r • G (frozenBallScaling c hr x) -
        ⨍ y in ball (0 : EuclideanSpace ℝ (Fin n)) s, r • G (frozenBallScaling c hr y)‖ ^ 2) =
      (r ^ 2 * (r ^ n)⁻¹) *
        ∫ x in ball c (r * s), ‖G x - ⨍ y in ball c (r * s), G y‖ ^ 2 := by
  rw [average_const_smul, frozen_average_comp_ballScaling hn G c hr hs]
  simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  rw [integral_const_mul, frozen_integral_ball_comp_ballScaling
    (fun x => ‖G x - ⨍ y in ball c (r * s), G y‖ ^ 2) c hr s]
  simp only [smul_eq_mul]
  ring

end LiquidDrop
