import NoCompromise.Elliptic.QuasilinearCampanatoPullback

/-! Campanato estimates on arbitrary translated balls, with a uniform constant
chosen before the center and all equation data. Continuous input representatives
are identified pointwise with the constructed C¹ representatives. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A continuous genuine H¹ solution receives the actual C¹,α estimate on a
smaller ball. Radius dependence is explicit in the quantifier order; the constant
is independent of its center and of the coefficient and solution data. -/
theorem quasilinear_campanato_on_ball {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap HA HG M r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG)
    (hM : 0 ≤ M) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      ContinuousOn A (ball c r) → ContinuousOn G (ball c r) → ContinuousOn u (ball c r) →
      (∀ x ∈ ball c r, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball c r, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      (∀ x ∈ ball c r, ∀ y ∈ ball c r, ‖A x - A y‖ ≤ HA * dist x y ^ a) →
      (∀ x ∈ ball c r, ∀ y ∈ ball c r, ‖G x - G y‖ ≤ HG * dist x y ^ a) →
      HasH1GradientOn u F (ball c r) → IsWeakDivergenceEquationOn A F G (ball c r) →
      (∫ x in ball c r, ‖F x‖ ^ 2) ≤ M →
      ContDiffOn ℝ 1 u (ball c (r / 2)) ∧
        (∀ x ∈ ball c (r / 2), ‖gradient u x‖ ≤ C) ∧
        ∀ x ∈ ball c (r / 2), ∀ y ∈ ball c (r / 2),
          ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ a := by
  obtain ⟨L, hL, hunit⟩ := campanato_c1_holder hn0 hn ha ha1 hlam hcap
    (show 0 ≤ HA * r ^ a by positivity)
    (show 0 ≤ r * HG * r ^ a by positivity)
    (show 0 ≤ (r ^ 2 * (r ^ n)⁻¹) * M by positivity)
  let C := max (r⁻¹ * L) (r⁻¹ * L * (r⁻¹) ^ a) + 1
  have hC : 0 < C := by
    have hp : 0 < r⁻¹ * L := mul_pos (inv_pos.mpr hr) hL
    have hh := le_max_left (r⁻¹ * L) (r⁻¹ * L * (r⁻¹) ^ a)
    dsimp [C]
    linarith only [hp, hh]
  have hC₁ : r⁻¹ * L ≤ C :=
    (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hC₂ : r⁻¹ * L * (r⁻¹) ^ a ≤ C :=
    (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro c A G F u hA hG huc hbA hell hAhold hGhold hu hw henergy
  let e := frozenBallScaling c hr
  have hmaps : MapsTo e (ball 0 1) (ball c r) := quasilinear_ballScaling_maps_unit c hr
  have hA' : ContinuousOn (A ∘ e) (ball 0 1) := hA.comp e.continuous.continuousOn hmaps
  have hG' : ContinuousOn (fun x => r • G (e x)) (ball 0 1) := by
    simpa only [Pi.smul_apply, Function.comp_def] using!
      (continuousOn_const (c := r)).smul (hG.comp e.continuous.continuousOn hmaps)
  have hu' := hu.comp_campanatoBallScaling c hr
  have hw' := hw.comp_campanatoBallScaling c hr
  have hbA' : ∀ x ∈ ball 0 1, ‖A (e x)‖ ≤ cap := fun x hx => hbA _ (hmaps hx)
  have hell' : ∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A (e x) ξ) ξ :=
    fun x hx => hell _ (hmaps hx)
  have hAhold' : ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖A (e x) - A (e y)‖ ≤ (HA * r ^ a) * dist x y ^ a := by
    intro x hx y hy
    have hb := hAhold _ (hmaps hx) _ (hmaps hy)
    rw [quasilinear_ballScaling_dist c x y hr, Real.mul_rpow hr.le dist_nonneg] at hb
    simpa only [mul_assoc] using hb
  have hGhold' : ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖r • G (e x) - r • G (e y)‖ ≤ (r * HG * r ^ a) * dist x y ^ a := by
    intro x hx y hy
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hb := mul_le_mul_of_nonneg_left (hGhold _ (hmaps hx) _ (hmaps hy)) hr.le
    rw [quasilinear_ballScaling_dist c x y hr, Real.mul_rpow hr.le dist_nonneg] at hb
    simpa only [mul_assoc] using hb
  have he' : (∫ x in ball 0 1, ‖r • F (e x)‖ ^ 2) ≤ (r ^ 2 * (r ^ n)⁻¹) * M := by
    rw [frozen_integral_gradient_sq_ballScaling F c hr 1, mul_one]
    exact mul_le_mul_of_nonneg_left henergy (by positivity)
  obtain ⟨v, hv, heq, _, hb, hholder, _⟩ := hunit (A ∘ e)
    (fun x => r • G (e x)) (fun x => r • F (e x)) (u ∘ e)
    hA' hG' hbA' hell' hAhold' hGhold' hu' hw' he'
  have heqPoint : EqOn (u ∘ e) v (ball 0 (1 / 2 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq heq isOpen_ball
      ((huc.comp e.continuous.continuousOn hmaps).mono (ball_subset_ball (by norm_num)))
      hv.continuousOn
  have hmHalf : MapsTo e.symm (ball c (r / 2)) (ball 0 (1 / 2 : ℝ)) := by
    intro x hx
    apply (frozenBallScaling_mem_ball_iff c (e.symm x) hr (1 / 2)).mp
    change e (e.symm x) ∈ ball c (r * (1 / 2 : ℝ))
    simpa only [e.apply_symm_apply, mul_one_div] using hx
  have hsInv : ContDiff ℝ 1 e.symm := by
    change ContDiff ℝ 1 (frozenBallScaling c hr).symm
    rw [frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have heqBack : EqOn u (v ∘ e.symm) (ball c (r / 2)) := by
    intro x hx
    simpa only [Function.comp_apply, e.apply_symm_apply] using heqPoint (hmHalf hx)
  have hgrad (x) (hx : x ∈ ball c (r / 2)) :
      gradient u x = r⁻¹ • gradient v (e.symm x) := by
    have hnear : u =ᶠ[𝓝 x] v ∘ e.symm := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact heqBack hy
    rw [hnear.gradient_eq]
    exact quasilinear_gradient_comp_ballScaling_symm_at c x hr
      ((hv.contDiffAt (isOpen_ball.mem_nhds (hmHalf hx))).differentiableAt one_ne_zero)
  refine ⟨(hv.comp hsInv.contDiffOn hmHalf).congr heqBack, ?_, ?_⟩
  · intro x hx
    rw [hgrad x hx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hb _ (hmHalf hx)) (inv_nonneg.mpr hr.le)).trans hC₁
  · intro x hx y hy
    rw [hgrad x hx, hgrad y hy, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hxy := mul_le_mul_of_nonneg_left
      (hholder _ (hmHalf hx) _ (hmHalf hy)) (inv_nonneg.mpr hr.le)
    rw [quasilinear_ballScaling_symm_dist c x y hr,
      Real.mul_rpow (inv_nonneg.mpr hr.le) dist_nonneg] at hxy
    exact hxy.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hC₂ (Real.rpow_nonneg dist_nonneg a))

end LiquidDrop
