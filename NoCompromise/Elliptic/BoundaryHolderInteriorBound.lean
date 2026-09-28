import NoCompromise.Elliptic.QuasilinearCampanatoPullback

/-! Scale-independent interior energy control. A genuine weak solution whose
initial energy has volume growth inherits the same growth on smaller balls.
The proof normalizes the scalar function by the radius before applying the
already proved interior Campanato theorem. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsWeakDivergenceEquationOn.boundary_const_smul {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsWeakDivergenceEquationOn A F G U) (c : ℝ) :
    IsWeakDivergenceEquationOn A (fun x => c • F x) (fun x => c • G x) U := by
  intro φ hφ hcφ hsφ
  simp only [map_smul, ← smul_sub, inner_smul_left]
  rw [integral_const_mul, h φ hφ hcφ hsφ, mul_zero]

/-- The constant is independent of the source radius, as well as its center
and all actual solution data. There is no bounded-gradient premise. -/
theorem boundary_interior_energy_cubic {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (c : EuclideanSpace ℝ (Fin 3)) (R : ℝ), 0 < R → R ≤ 1 →
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        ContinuousOn A (ball c R) → ContinuousOn G (ball c R) →
        (∀ x ∈ ball c R, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball c R, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball c R) → IsWeakDivergenceEquationOn A F G (ball c R) →
        (∫ x in ball c R, ‖F x‖ ^ 2) ≤ M * R ^ (3 : ℝ) →
        ∀ r ∈ Ioc 0 (R / 2), (∫ x in ball c r, ‖F x‖ ^ 2) ≤ P * r ^ (3 : ℝ) := by
  obtain ⟨_, Q, _, hQ, hb⟩ := campanato_gradient_holder (by norm_num : 0 < 3)
    (by norm_num : 3 < 4) ha ha1 hlam hcap hHA hHG hM
  let P := Q ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
  refine ⟨P, by dsimp [P]; positivity, ?_⟩
  intro c R hR hR1 u F G A hA hG hbA hell hAh hGh hu hw henergy
  let e := frozenBallScaling c hR
  have hmaps := quasilinear_ballScaling_maps_unit c hR
  have hRpow : R ^ a ≤ 1 := Real.rpow_le_one hR.le hR1 ha.le
  have hA' : ContinuousOn (A ∘ e) (ball 0 1) := hA.comp e.continuous.continuousOn hmaps
  have hG' : ContinuousOn (G ∘ e) (ball 0 1) := hG.comp e.continuous.continuousOn hmaps
  have hAh' : ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖A (e x) - A (e y)‖ ≤ HA * dist x y ^ a := by
    intro x hx y hy
    have hh := hAh _ (hmaps hx) _ (hmaps hy)
    rw [quasilinear_ballScaling_dist c x y hR, Real.mul_rpow hR.le dist_nonneg] at hh
    apply hh.trans
    calc
      HA * (R ^ a * dist x y ^ a) = R ^ a * (HA * dist x y ^ a) := by ring
      _ ≤ 1 * (HA * dist x y ^ a) := mul_le_mul_of_nonneg_right hRpow
        (mul_nonneg hHA (Real.rpow_nonneg dist_nonneg a))
      _ = _ := one_mul _
  have hGh' : ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖G (e x) - G (e y)‖ ≤ HG * dist x y ^ a := by
    intro x hx y hy
    have hh := hGh _ (hmaps hx) _ (hmaps hy)
    rw [quasilinear_ballScaling_dist c x y hR, Real.mul_rpow hR.le dist_nonneg] at hh
    apply hh.trans
    calc
      HG * (R ^ a * dist x y ^ a) = R ^ a * (HG * dist x y ^ a) := by ring
      _ ≤ 1 * (HG * dist x y ^ a) := mul_le_mul_of_nonneg_right hRpow
        (mul_nonneg hHG (Real.rpow_nonneg dist_nonneg a))
      _ = _ := one_mul _
  have hu' : HasH1GradientOn (fun x => R⁻¹ * u (e x)) (F ∘ e) (ball 0 1) := by
    simpa only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul, Function.comp_def] using
      (hu.comp_campanatoBallScaling c hR).const_mul R⁻¹
  have hw' : IsWeakDivergenceEquationOn (A ∘ e) (F ∘ e) (G ∘ e) (ball 0 1) := by
    simpa only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul, Function.comp_def] using
      (hw.comp_campanatoBallScaling c hR).boundary_const_smul R⁻¹
  have he' : (∫ x in ball 0 1, ‖F (e x)‖ ^ 2) ≤ M := by
    rw [frozen_integral_ball_comp_ballScaling (fun x => ‖F x‖ ^ 2) c hR 1, mul_one,
      smul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr (pow_nonneg hR.le 3))
    rw [Real.rpow_ofNat] at hh
    calc
      _ ≤ (R ^ 3)⁻¹ * (M * R ^ 3) := hh
      _ = M := by field_simp
  obtain ⟨H, heq, _, hbH, _⟩ := hb (A ∘ e) (G ∘ e) (F ∘ e)
    (fun x => R⁻¹ * u (e x)) hA' hG' (fun x hx => hbA _ (hmaps hx))
    (fun x hx => hell _ (hmaps hx)) hAh' hGh' hu' hw' he'
  intro r hr
  have hratio : r / R ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith [hr.2])
  have hpos : 0 < r / R := div_pos hr.1 hR
  have hh := campanato_gradient_energy_of_ae_bounded (c := (0 : EuclideanSpace ℝ (Fin 3)))
    (r := r / R) (hu'.memLp_gradient.mono_measure
      (Measure.restrict_mono (ball_subset_ball (by norm_num : (3 / 5 : ℝ) ≤ 1)) le_rfl))
    heq hQ hbH
    (ball_subset_ball (hratio.trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 5)))
  simp only [Function.comp_def, e] at hh
  rw [frozen_integral_ball_comp_ballScaling (fun x => ‖F x‖ ^ 2) c hR (r / R),
    mul_div_cancel₀ _ hR.ne', smul_eq_mul,
    frozen_real_volume_ball (by norm_num : 0 < 3) 0 hpos.le] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg hR.le 3)
  rw [Real.rpow_ofNat]
  dsimp [P]
  convert hmul using 1 <;> first | rfl | field_simp [hR.ne']

end LiquidDrop
