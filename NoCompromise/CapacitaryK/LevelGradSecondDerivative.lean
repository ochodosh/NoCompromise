module

public import NoCompromise.CapacitaryK.LevelGradDerivatives
public import NoCompromise.CapacitaryK.LevelRadiusSecondDerivative

@[expose] public section

/-!
# Second-order angular calculus for the level gradient length

These lemmas provide third-order decay of the translated harmonic remainder and
second-order calculus for the gradient-length expansion in Chapter 31.

For `q(y) = Q(y / ‖y‖)`, the polar model is `C / ρ² + 3q / ρ⁴`.
Its Hessian is
`(-2C / ρ³ - 12q / ρ⁵) D²ρ + (6C / ρ⁴ + 60q / ρ⁶) Dρ ⊗ Dρ`
`- 12 / ρ⁵ (Dρ ⊗ Dq + Dq ⊗ Dρ) + 3 / ρ⁴ D²q`.
Substituting `D²ρ = (t / C²) D²q + D²E` gives the coefficient
`-2(t/C) / ρ³ + 3 / ρ⁴ - (t/C)⁴` after subtracting the target Hessian.
The existing coefficient cancellation controls this by `O(t⁵)`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

set_option maxSynthPendingDepth 8 in
-- Three nested continuous linear maps exceed the project synthesis-depth default.
/-- The norm of the third iterated derivative equals the norm of the triply
curried Fréchet derivative. No differentiability hypothesis is needed. -/
theorem levelGradSecond_norm_iteratedFDeriv_three (W : E3 → ℝ) (x : E3) :
    ‖iteratedFDeriv ℝ 3 W x‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ W)) x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (fderiv ℝ W)),
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

set_option maxSynthPendingDepth 8 in
-- Three nested continuous linear maps exceed the project synthesis-depth default.
/-- A harmonic `O(r⁻⁴)` remainder has a third derivative of order `O(r⁻⁷)`.
The estimate holds outside twice the original radius. -/
theorem levelGradSecond_harmonic_third_derivative_decay {W : E3 → ℝ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hΔ : ∀ x, R < ‖x‖ → laplacianN W x = 0)
    (hb : ∀ x, R ≤ ‖x‖ → |W x| ≤ M / ‖x‖ ^ 4) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x : E3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ W)) x‖ ≤ M' / ‖x‖ ^ 7 := by
  obtain ⟨c, hc, hbound⟩ := harmonic_scaled_iteratedFDeriv_bound 3
  refine ⟨128 * c * M, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hhalf : R ≤ ‖x‖ / 2 := by linarith
  have hball : ∀ y ∈ ball x (‖x‖ / 2), ‖x‖ / 2 < ‖y‖ := by
    intro y hy
    have ht := norm_sub_norm_le x y
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
    linarith
  have hsub : ball x (‖x‖ / 2) ⊆ {y | R < ‖y‖} := by
    intro y hy
    exact hhalf.trans_lt (hball y hy)
  have hlocal : ∀ y ∈ ball x (‖x‖ / 2), |W y| ≤ 16 * M / ‖x‖ ^ 4 := by
    intro y hy
    have hny : ‖x‖ / 2 ≤ ‖y‖ := (hball y hy).le
    calc
      |W y| ≤ M / ‖y‖ ^ 4 := hb y (hhalf.trans hny)
      _ ≤ M / (‖x‖ / 2) ^ 4 := div_le_div_of_nonneg_left hM (by positivity)
        (pow_le_pow_left₀ (by positivity) hny 4)
      _ = 16 * M / ‖x‖ ^ 4 := by ring
  have hd := hbound W x (‖x‖ / 2) (16 * M / ‖x‖ ^ 4) (half_pos hxpos)
    (hs.mono hsub) (fun y hy => hΔ y (hsub hy)) hlocal
  rw [levelGradSecond_norm_iteratedFDeriv_three] at hd
  exact hd.trans_eq (by ring)

/-- Harmonicity of the translated remainder in the exterior of a ball containing
the translated conductor. This exposes the harmonicity needed for third derivatives. -/
theorem levelGradSecond_translated_remainder_harmonic
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) {u v : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hQ : ∀ x : E3, laplacianN (kelvinTranslatedQuadrupole v) x = 0) :
    ∀ x, R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖ →
      laplacianN (kelvinTranslatedRemainder u v) x = 0 := by
  let z := (v 0)⁻¹ • gradient v 0
  let U : Set E3 := {x | R₀ + ‖z‖ < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hmap : ∀ x ∈ U, z + x ∈ Kᶜ := by
    intro x hx hxK
    have hxR : ‖z + x‖ ≤ R₀ := by
      simpa only [mem_closedBall, dist_zero_right] using hKR hxK
    have ht : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z + x) z
    have ht' : ‖x‖ ≤ R₀ + ‖z‖ := by linarith
    exact (not_lt_of_ge ht') hx
  have hx0 : ∀ x ∈ U, x ≠ 0 := by
    intro x hx he
    subst x
    have hz := norm_nonneg z
    change R₀ + ‖z‖ < ‖(0 : E3)‖ at hx
    rw [norm_zero] at hx
    linarith
  have hsu := capacitary_potential_contDiffOn hK hu hh
  have hΔu := kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl
    hu.continuousOn hh
  have htu : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => u (z + x)) U :=
    hsu.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  have hhu : HasDistributionalLaplacianOn (fun x => u (z + x)) (fun _ => 0) U := by
    apply hasDistributionalLaplacianOn_zero_of_contDiffOn hU (htu.of_le (by simp))
    intro x hx
    rw [laplacianN_comp_add_left]
    exact hΔu _ (hmap x hx)
  let p : E3 → ℝ := fun y => v 0 + kelvinTranslatedQuadrupole v y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := contDiff_const.add (translated_quadrupole_contDiff v)
  have hΔp : ∀ x, laplacianN p x = 0 := by
    have hd (i : Fin 3) : poissonCoordinateDerivative i p =
        poissonCoordinateDerivative i (kelvinTranslatedQuadrupole v) := by
      funext y
      simp only [p, poissonCoordinateDerivative, fderiv_const_add]
    intro x
    simpa only [laplacianN, hd] using hQ x
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTransform p) U := by
    apply hU.contDiffOn_iff.mpr
    intro x hx
    exact ((contDiffAt_id.norm ℝ (hx0 x hx)).inv (norm_ne_zero_iff.mpr (hx0 x hx))).mul
      (hp.contDiffAt.comp x (contDiffAt_kelvinInversion (hx0 x hx)))
  have hhm : HasDistributionalLaplacianOn (kelvinTransform p) (fun _ => 0) U := by
    apply hasDistributionalLaplacianOn_zero_of_contDiffOn hU (hsm.of_le (by simp))
    intro x hx
    rw [laplacianN_kelvinTransform (hx0 x hx) (hp.contDiffAt.of_le (by simp)), hΔp,
      mul_zero]
  have he : kelvinTranslatedRemainder u v = fun x => u (z + x) - kelvinTransform p x := by
    funext x
    have hm : v 0 / ‖x‖ + kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 =
        kelvinTransform p x := by
      simp only [p, kelvinTransform, kelvinInversion, kelvinTranslatedQuadrupole_smul,
        div_eq_mul_inv, inv_pow]
      ring
    rw [← hm]
    simp only [kelvinTranslatedRemainder, z, add_comm, sub_sub]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) U := by
    rw [he]
    exact htu.sub hsm
  apply kelvin_laplacianN_eq_zero_of_distributional hU hs.continuousOn
  rw [he]
  simpa only [sub_self] using hhu.sub hhm

set_option maxSynthPendingDepth 8 in
-- Three nested continuous linear maps exceed the project synthesis-depth default.
/-- Third-order translated remainder estimates under the original capacitary
hypotheses. The radius and constant are uniform in the direction. -/
theorem levelGradSecond_capacitary_translated_remainder_derivatives
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R < ‖x‖} ∧
        ∀ x : E3, R ≤ ‖x‖ →
          |kelvinTranslatedRemainder u v x| ≤ M / ‖x‖ ^ 4 ∧
          ‖fderiv ℝ (kelvinTranslatedRemainder u v) x‖ ≤ M / ‖x‖ ^ 5 ∧
          ‖fderiv ℝ (fderiv ℝ (kelvinTranslatedRemainder u v)) x‖ ≤ M / ‖x‖ ^ 6 ∧
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (kelvinTranslatedRemainder u v))) x‖ ≤
            M / ‖x‖ ^ 7 := by
  obtain ⟨v, r, hr, hv, he, _, hv0, _, _, hQΔ, _, R, M, hR, hs, hbound⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  have hΔ := levelGradSecond_translated_remainder_harmonic hK hR₀ hKR hu hh hQΔ
  let S := max R (R₀ + ‖(v 0)⁻¹ • gradient v 0‖)
  have hS : 0 < S := hR.trans_le (le_max_left _ _)
  have hsS : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v)
      {x | S < ‖x‖} :=
    hs.mono (fun x hx => by
      exact (le_max_left R (R₀ + ‖(v 0)⁻¹ • gradient v 0‖)).trans_lt hx)
  obtain ⟨N, hN, hthird⟩ := levelGradSecond_harmonic_third_derivative_decay hS
    (abs_nonneg M) hsS (fun x hx => hΔ x ((le_max_right _ _).trans_lt hx)) (by
      intro x hx
      exact (hbound x ((le_max_left _ _).trans hx)).1.trans
        (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  refine ⟨v, r, hr, hv, he, hv0, 2 * S, max |M| N, by positivity,
    (abs_nonneg M).trans (le_max_left _ _),
    hsS.mono (fun x hx => by change S < ‖x‖; change 2 * S < ‖x‖ at hx; linarith),
    fun x hx => ?_⟩
  have hxR : R ≤ ‖x‖ := by
    have := le_max_left R (R₀ + ‖(v 0)⁻¹ • gradient v 0‖)
    dsimp [S] at hx hS
    linarith
  have hMN : M ≤ max |M| N := (le_abs_self M).trans (le_max_left _ _)
  obtain ⟨hb₀, hb₁, hb₂⟩ := hbound x hxR
  exact ⟨hb₀.trans (div_le_div_of_nonneg_right hMN (by positivity)),
    hb₁.trans (div_le_div_of_nonneg_right hMN (by positivity)),
    hb₂.trans (div_le_div_of_nonneg_right hMN (by positivity)),
    (hthird x hx).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- First derivative of the polar gradient-length model. -/
theorem levelGradSecond_polar_model_fderiv {ρ q : E3 → ℝ} {x : E3} (C : ℝ)
    (hρ : DifferentiableAt ℝ ρ x) (hq : DifferentiableAt ℝ q x) (hs : ρ x ≠ 0) :
    fderiv ℝ (fun y => C * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4) x =
      (-2 * C * (ρ x)⁻¹ ^ 3 - 12 * q x * (ρ x)⁻¹ ^ 5) • fderiv ℝ ρ x +
        (3 * (ρ x)⁻¹ ^ 4) • fderiv ℝ q x := by
  have hi := (hasDerivAt_inv hs).comp_hasFDerivAt x hρ.hasFDerivAt
  have hd := ((hi.pow 2).const_mul C).add
    ((hq.hasFDerivAt.const_mul 3).mul (hi.pow 4))
  change HasFDerivAt
    (fun y => C * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4) _ x at hd
  rw [hd.fderiv]
  ext e
  simp only [add_apply, smul_apply,
    smul_eq_mul, Function.comp_apply,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, ← inv_pow]
  ring

/-- Exact second derivative of the polar gradient-length model, evaluated on
arbitrary vectors. All four product-rule terms are retained. -/
theorem levelGradSecond_polar_model_fderiv_two {ρ q : E3 → ℝ} {x : E3} (C : ℝ)
    (hρ : ContDiffAt ℝ 2 ρ x) (hq : ContDiffAt ℝ 2 q x) (hs : ρ x ≠ 0)
    (e f : E3) :
    fderiv ℝ (fderiv ℝ
      (fun y => C * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4)) x e f =
      (-2 * C * (ρ x)⁻¹ ^ 3 - 12 * q x * (ρ x)⁻¹ ^ 5) *
        fderiv ℝ (fderiv ℝ ρ) x e f +
      (6 * C * (ρ x)⁻¹ ^ 4 + 60 * q x * (ρ x)⁻¹ ^ 6) *
        fderiv ℝ ρ x e * fderiv ℝ ρ x f -
      12 * (ρ x)⁻¹ ^ 5 *
        (fderiv ℝ ρ x e * fderiv ℝ q x f + fderiv ℝ ρ x f * fderiv ℝ q x e) +
      3 * (ρ x)⁻¹ ^ 4 * fderiv ℝ (fderiv ℝ q) x e f := by
  have hρd := hρ.differentiableAt (by norm_num)
  have hqd := hq.differentiableAt (by norm_num)
  have hDρ : DifferentiableAt ℝ (fderiv ℝ ρ) x :=
    (hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDq : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hi := (hasDerivAt_inv hs).comp_hasFDerivAt x hρd.hasFDerivAt
  have hmodel : ContDiffAt ℝ 2
      (fun y => C * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4) x :=
    (contDiffAt_const.mul ((hρ.inv hs).pow 2)).add
      ((contDiffAt_const.mul hq).mul ((hρ.inv hs).pow 4))
  have hDm := (hmodel.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ
      (fun z => C * (ρ z)⁻¹ ^ 2 + 3 * q z * (ρ z)⁻¹ ^ 4) y f) =ᶠ[𝓝 x]
      (fun y => (-2 * C * (ρ y)⁻¹ ^ 3 - 12 * q y * (ρ y)⁻¹ ^ 5) *
        fderiv ℝ ρ y f + (3 * (ρ y)⁻¹ ^ 4) * fderiv ℝ q y f) := by
    filter_upwards [hρ.eventually (by norm_num), hq.eventually (by norm_num),
      hρd.continuousAt.eventually_ne hs] with y hy hz hne
    rw [levelGradSecond_polar_model_fderiv C (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num)) hne]
    rfl
  have ha := ((hi.pow 3).const_mul (-2 * C)).sub
    ((hqd.hasFDerivAt.const_mul 12).mul (hi.pow 5))
  have hb := (hi.pow 4).const_mul 3
  have hleft := hDm.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (ha.mul (hDρ.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).add
    (hb.mul (hDq.hasFDerivAt.clm_apply (hasFDerivAt_const f x)))
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    zero_apply, smul_eq_mul, Function.comp_apply,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, Pi.sub_apply, Pi.mul_apply,
    ContinuousLinearMap.flip_apply, map_zero, zero_add, ← inv_pow] at hid
  rw [hid]
  ring

/-- Quantitative second-order cancellation for the polar model. The quantities
`r₁`, `r₂`, and `r₁₂` represent radius derivatives; `q₁`, `q₂`, and `q₁₂`
represent angular coefficient derivatives. The radius Hessian error is explicit. -/
theorem levelGradSecond_polar_hessian_error_bound
    {C a ε A B K P q q₁ q₂ q₁₂ r₁ r₂ r₁₂ : ℝ}
    (hC : 0 < C) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεa : ε ≤ 2 * a) (_hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hinv : |ε - a| ≤ K * a ^ 2)
    (hq : |q| ≤ B) (hq₁ : |q₁| ≤ B) (hq₂ : |q₂| ≤ B) (hq₁₂ : |q₁₂| ≤ B)
    (hr₁ : |r₁| ≤ P * a) (hr₂ : |r₂| ≤ P * a) (hr₁₂ : |r₁₂| ≤ P * a)
    (herr : |r₁₂ - (a / C) * q₁₂| ≤ A * a ^ 2) :
    |(-2 * C * ε ^ 3 - 12 * q * ε ^ 5) * r₁₂ +
      (6 * C * ε ^ 4 + 60 * q * ε ^ 6) * r₁ * r₂ -
      12 * ε ^ 5 * (r₁ * q₂ + r₂ * q₁) + (3 * ε ^ 4 - a ^ 4) * q₁₂| ≤
      (16 * C * A + 59 * K * B + 1152 * B * P + (96 * C + 960 * B) * P ^ 2) *
        a ^ 5 := by
  have hε3 : ε ^ 3 ≤ 8 * a ^ 3 := by
    nlinarith [pow_le_pow_left₀ hε hεa 3]
  have hε4 : ε ^ 4 ≤ 16 * a ^ 4 := by
    nlinarith [pow_le_pow_left₀ hε hεa 4]
  have hε5 : ε ^ 5 ≤ 32 * a ^ 5 := by
    nlinarith [pow_le_pow_left₀ hε hεa 5]
  have hε64 : ε ^ 6 ≤ ε ^ 4 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have ha65 : a ^ 6 ≤ a ^ 5 := pow_le_pow_of_le_one ha ha1 (by norm_num)
  have hid : (-2 * C * ε ^ 3 - 12 * q * ε ^ 5) * r₁₂ +
      (6 * C * ε ^ 4 + 60 * q * ε ^ 6) * r₁ * r₂ -
      12 * ε ^ 5 * (r₁ * q₂ + r₂ * q₁) + (3 * ε ^ 4 - a ^ 4) * q₁₂ =
      -2 * C * ε ^ 3 * (r₁₂ - (a / C) * q₁₂) +
        (-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) * q₁₂ -
        12 * q * ε ^ 5 * r₁₂ +
        (6 * C * ε ^ 4 + 60 * q * ε ^ 6) * r₁ * r₂ -
        12 * ε ^ 5 * (r₁ * q₂ + r₂ * q₁) := by
    field_simp
    ring
  have h₁ : |-2 * C * ε ^ 3 * (r₁₂ - (a / C) * q₁₂)| ≤ 16 * C * A * a ^ 5 := by
    rw [abs_mul, show -2 * C * ε ^ 3 = -(2 * C * ε ^ 3) by ring,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * C * ε ^ 3)]
    calc
      _ ≤ (2 * C * (8 * a ^ 3)) * (A * a ^ 2) := by gcongr
      _ = _ := by ring
  have h₂ : |(-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) * q₁₂| ≤
      59 * K * B * a ^ 5 := by
    rw [abs_mul]
    exact (mul_le_mul (levelGrad_coefficient_cancellation ha hε hεa hK hinv)
      hq₁₂ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have h₃ : |12 * q * ε ^ 5 * r₁₂| ≤ 384 * B * P * a ^ 5 := by
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 5),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
    calc
      _ ≤ 12 * B * (32 * a ^ 5) * (P * a) := by gcongr
      _ = 384 * B * P * a ^ 6 := by ring
      _ ≤ _ := by gcongr
  have hcoef : |6 * C * ε ^ 4 + 60 * q * ε ^ 6| ≤ (6 * C + 60 * B) * ε ^ 4 := by
    calc
      _ ≤ |6 * C * ε ^ 4| + |60 * q * ε ^ 6| := abs_add_le _ _
      _ = 6 * C * ε ^ 4 + 60 * |q| * ε ^ 6 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 6 * C * ε ^ 4)]
        simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 6),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 60)]
      _ ≤ 6 * C * ε ^ 4 + 60 * B * ε ^ 4 := by gcongr
      _ = _ := by ring
  have h₄ : |(6 * C * ε ^ 4 + 60 * q * ε ^ 6) * r₁ * r₂| ≤
      (96 * C + 960 * B) * P ^ 2 * a ^ 5 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ ((6 * C + 60 * B) * ε ^ 4) * (P * a) * (P * a) := by gcongr
      _ ≤ ((6 * C + 60 * B) * (16 * a ^ 4)) * (P * a) * (P * a) := by gcongr
      _ = (96 * C + 960 * B) * P ^ 2 * a ^ 6 := by ring
      _ ≤ _ := by gcongr
  have hmix : |r₁ * q₂ + r₂ * q₁| ≤ 2 * P * B * a := by
    calc
      _ ≤ |r₁ * q₂| + |r₂ * q₁| := abs_add_le _ _
      _ ≤ (P * a) * B + (P * a) * B := by simp only [abs_mul]; gcongr
      _ = _ := by ring
  have h₅ : |12 * ε ^ 5 * (r₁ * q₂ + r₂ * q₁)| ≤ 768 * B * P * a ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 12 * ε ^ 5)]
    calc
      _ ≤ (12 * ε ^ 5) * (2 * P * B * a) := by gcongr
      _ ≤ (12 * (32 * a ^ 5)) * (2 * P * B * a) := by gcongr
      _ = 768 * B * P * a ^ 6 := by ring
      _ ≤ _ := by gcongr
  rw [hid]
  calc
    _ ≤ |-2 * C * ε ^ 3 * (r₁₂ - (a / C) * q₁₂)| +
        |(-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) * q₁₂| +
        |12 * q * ε ^ 5 * r₁₂| +
        |(6 * C * ε ^ 4 + 60 * q * ε ^ 6) * r₁ * r₂| +
        |12 * ε ^ 5 * (r₁ * q₂ + r₂ * q₁)| := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-- Operator-norm form of the second-order polar cancellation. -/
theorem levelGradSecond_polar_model_hessian_bound {ρ q : E3 → ℝ} {x : E3}
    {C a A B K P : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : 0 < ρ x) (hs1 : (ρ x)⁻¹ ≤ 1) (hsa : (ρ x)⁻¹ ≤ 2 * a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hρ : ContDiffAt ℝ 2 ρ x) (hq : ContDiffAt ℝ 2 q x)
    (hinv : |(ρ x)⁻¹ - a| ≤ K * a ^ 2)
    (hq₀ : |q x| ≤ B) (hq₁ : ‖fderiv ℝ q x‖ ≤ B)
    (hq₂ : ‖fderiv ℝ (fderiv ℝ q) x‖ ≤ B)
    (hr₁ : ‖fderiv ℝ ρ x‖ ≤ P * a)
    (hr₂ : ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ P * a)
    (herr : ‖fderiv ℝ (fderiv ℝ ρ) x -
      (a / C) • fderiv ℝ (fderiv ℝ q) x‖ ≤ A * a ^ 2) :
    ‖fderiv ℝ (fderiv ℝ
      (fun y => C * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4)) x -
        a ^ 4 • fderiv ℝ (fderiv ℝ q) x‖ ≤
      (16 * C * A + 59 * K * B + 1152 * B * P + (96 * C + 960 * B) * P ^ 2) *
        a ^ 5 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro f hf
  have hq₁e : |fderiv ℝ q x e| ≤ B := by
    simpa only [Real.norm_eq_abs, he, mul_one] using
      (fderiv ℝ q x).le_of_opNorm_le hq₁ e
  have hq₁f : |fderiv ℝ q x f| ≤ B := by
    simpa only [Real.norm_eq_abs, hf, mul_one] using
      (fderiv ℝ q x).le_of_opNorm_le hq₁ f
  have hq₂ef : |fderiv ℝ (fderiv ℝ q) x e f| ≤ B := by
    simpa only [Real.norm_eq_abs, mul_one] using
      (fderiv ℝ (fderiv ℝ q) x).le_of_opNorm₂_le_of_le hq₂ he.le hf.le
  have hr₁e : |fderiv ℝ ρ x e| ≤ P * a := by
    simpa only [Real.norm_eq_abs, he, mul_one] using
      (fderiv ℝ ρ x).le_of_opNorm_le hr₁ e
  have hr₁f : |fderiv ℝ ρ x f| ≤ P * a := by
    simpa only [Real.norm_eq_abs, hf, mul_one] using
      (fderiv ℝ ρ x).le_of_opNorm_le hr₁ f
  have hr₂ef : |fderiv ℝ (fderiv ℝ ρ) x e f| ≤ P * a := by
    simpa only [Real.norm_eq_abs, mul_one] using
      (fderiv ℝ (fderiv ℝ ρ) x).le_of_opNorm₂_le_of_le hr₂ he.le hf.le
  have herref : |fderiv ℝ (fderiv ℝ ρ) x e f -
      (a / C) * fderiv ℝ (fderiv ℝ q) x e f| ≤ A * a ^ 2 := by
    simpa only [Real.norm_eq_abs, sub_apply, smul_apply, smul_eq_mul, mul_one] using
      ContinuousLinearMap.le_of_opNorm₂_le_of_le
        (fderiv ℝ (fderiv ℝ ρ) x - (a / C) • fderiv ℝ (fderiv ℝ q) x)
        herr he.le hf.le
  have hb := levelGradSecond_polar_hessian_error_bound hC ha ha1 (inv_nonneg.mpr hs.le)
    hs1 hsa hA hB hK hP hinv hq₀ hq₁e hq₁f hq₂ef hr₁e hr₁f hr₂ef herref
  simp only [sub_apply, smul_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [levelGradSecond_polar_model_fderiv_two C hρ hq hs.ne']
  convert hb using 2
  ring

/-- First derivative of the norm of a vector field at a nonzero value. -/
theorem levelGradSecond_fderiv_norm_apply {G : E3 → E3} {x : E3}
    (hG : DifferentiableAt ℝ G x) (hG0 : G x ≠ 0) (e : E3) :
    fderiv ℝ (fun y => ‖G y‖) x e = ‖G x‖⁻¹ * ⟪G x, fderiv ℝ G x e⟫ := by
  have hd := (hG.norm ℝ hG0).hasFDerivAt
  have h₁ := hG.hasFDerivAt.norm_sq
  have h₂ := hd.mul hd
  have he : ((fun y => ‖G y‖) * fun y => ‖G y‖) = fun y => ‖G y‖ ^ 2 := by
    funext y
    simp [sq]
  rw [he] at h₂
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e) (h₂.unique h₁)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hid
  rw [eq_inv_mul_iff_mul_eq₀ (norm_ne_zero_iff.mpr hG0)]
  linarith

/-- Exact Hessian of the norm of a twice differentiable vector field. This is
the nonlinear second-order identity needed for the spatial gradient length. -/
theorem levelGradSecond_fderiv_two_norm {G : E3 → E3} {x : E3}
    (hG : ContDiffAt ℝ 2 G x) (hG0 : G x ≠ 0) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => ‖G y‖)) x e f =
      ‖G x‖⁻¹ * (⟪fderiv ℝ G x e, fderiv ℝ G x f⟫ +
        ⟪G x, fderiv ℝ (fderiv ℝ G) x e f⟫) -
      ‖G x‖⁻¹ ^ 3 * ⟪G x, fderiv ℝ G x e⟫ * ⟪G x, fderiv ℝ G x f⟫ := by
  have hGd := hG.differentiableAt (by norm_num)
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hn : ContDiffAt ℝ 2 (fun y => ‖G y‖) x := hG.norm ℝ hG0
  have hDn := (hn.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hG0)).comp_hasFDerivAt x
    (hn.differentiableAt (by norm_num)).hasFDerivAt
  have heq : (fun y => fderiv ℝ (fun z => ‖G z‖) y f) =ᶠ[𝓝 x]
      (fun y => ‖G y‖⁻¹ * ⟪G y, fderiv ℝ G y f⟫) := by
    filter_upwards [hG.eventually (by norm_num), hGd.continuousAt.eventually_ne hG0]
      with y hy hne
    exact levelGradSecond_fderiv_norm_apply (hy.differentiableAt (by norm_num)) hne f
  have hleft := hDn.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := hi.mul
    (hGd.hasFDerivAt.inner ℝ (hDG.hasFDerivAt.clm_apply (hasFDerivAt_const f x)))
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, smul_eq_mul, Function.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, map_zero, zero_add,
    ← inv_pow] at hid
  rw [levelGradSecond_fderiv_norm_apply hGd hG0 e] at hid
  rw [hid]
  ring

/-- Derivative bounds for a radial graph, with the ambient normalized extension.
Only bounded first and second radius derivatives are needed for this estimate. -/
theorem levelGradSecond_radial_map_bounds {ρ : E3 → ℝ} {θ : E3} {P : ℝ}
    (hθ : ‖θ‖ = 1) (hs : 1 ≤ ρ θ) (hP : 0 ≤ P) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hDρ : ‖fderiv ℝ ρ θ‖ ≤ P) (hDDρ : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P) :
    ‖fderiv ℝ (fun y => ρ y • (‖y‖⁻¹ • y)) θ‖ ≤ (P + 2) * ρ θ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ρ y • (‖y‖⁻¹ • y))) θ‖ ≤ (5 * P + 6) * ρ θ := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hs0 : 0 ≤ ρ θ := le_trans (by norm_num) hs
  have hPρ : P ≤ P * ρ θ := by nlinarith
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  have hDn (e : E3) (he : ‖e‖ = 1) :
      ‖fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ e‖ ≤ 2 := by
    rw [levelRadius_normalize_fderiv hθ]
    simpa only [real_inner_comm θ e, he, mul_one] using
      (levelRadius_tangent_norm_le (w := e) hθ)
  have hDDn (e f : E3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
      ‖fderiv ℝ (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y)) θ e f‖ ≤ 6 := by
    rw [levelRadius_normalize_fderiv_two hθ]
    exact levelRadius_normalize_fderiv_two_bound hθ he hf
  have hD (e : E3) (he : ‖e‖ = 1) : |fderiv ℝ ρ θ e| ≤ P := by
    simpa only [Real.norm_eq_abs, he, mul_one] using
      (fderiv ℝ ρ θ).le_of_opNorm_le hDρ e
  refine ⟨?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    rw [levelRadius_levelMap_fderiv hθ (hρ.differentiableAt (by norm_num))]
    have hPe : ‖e - ⟪θ, e⟫ • θ‖ ≤ 2 := by
      simpa only [levelRadius_normalize_fderiv hθ] using hDn e he
    calc
      _ ≤ ‖fderiv ℝ ρ θ e • θ‖ + ‖ρ θ • (e - ⟪θ, e⟫ • θ)‖ := norm_add_le _ _
      _ ≤ P + ρ θ * 2 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hθ, mul_one]
        exact add_le_add (hD e he) (mul_le_mul_of_nonneg_left hPe hs0)
      _ ≤ _ := by nlinarith
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDD : |fderiv ℝ (fderiv ℝ ρ) θ e f| ≤ P := by
      simpa only [Real.norm_eq_abs, mul_one] using
        (fderiv ℝ (fderiv ℝ ρ) θ).le_of_opNorm₂_le_of_le hDDρ he.le hf.le
    rw [levelRadius_fderiv_two_smul hρ hn]
    simp only [hθ, inv_one, one_smul]
    calc
      _ ≤ ‖ρ θ • fderiv ℝ (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y)) θ e f‖ +
          ‖fderiv ℝ ρ θ e • fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ f‖ +
          ‖fderiv ℝ ρ θ f • fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ e‖ +
          ‖fderiv ℝ (fderiv ℝ ρ) θ e f • θ‖ :=
        (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
      _ ≤ ρ θ * 6 + P * 2 + P * 2 + P := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hθ, mul_one]
        gcongr
        · exact hDDn e f he hf
        · exact hD e he
        · exact hDn f hf
        · exact hD f hf
        · exact hDn e he
      _ ≤ _ := by nlinarith

/-- A spatial Hessian error of order seven and gradient error of order six
produce an angular Hessian error of order five after composition. -/
theorem levelGradSecond_composition_hessian_bound {F : E3 → E3} {W : E3 → ℝ}
    {x : E3} {s M L N : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (_hL : 0 ≤ L) (hN : 0 ≤ N)
    (hF : ContDiffAt ℝ 2 F x) (hW : ContDiffAt ℝ 2 W (F x))
    (hDF : ‖fderiv ℝ F x‖ ≤ L * s)
    (hDDF : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ N * s)
    (hDW : ‖fderiv ℝ W (F x)‖ ≤ M / s ^ 6)
    (hDDW : ‖fderiv ℝ (fderiv ℝ W) (F x)‖ ≤ M / s ^ 7) :
    ‖fderiv ℝ (fderiv ℝ (fun y => W (F y))) x‖ ≤ M * (L ^ 2 + N) / s ^ 5 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro f hf
  have hDe : ‖fderiv ℝ F x e‖ ≤ L * s := by
    simpa only [he, mul_one] using (fderiv ℝ F x).le_of_opNorm_le hDF e
  have hDf : ‖fderiv ℝ F x f‖ ≤ L * s := by
    simpa only [hf, mul_one] using (fderiv ℝ F x).le_of_opNorm_le hDF f
  have hDD : ‖fderiv ℝ (fderiv ℝ F) x e f‖ ≤ N * s := by
    simpa only [mul_one] using
      (fderiv ℝ (fderiv ℝ F) x).le_of_opNorm₂_le_of_le hDDF he.le hf.le
  rw [levelRadius_fderiv_two_comp hF hW]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ W) (F x) (fderiv ℝ F x e) (fderiv ℝ F x f)‖ +
        ‖fderiv ℝ W (F x) (fderiv ℝ (fderiv ℝ F) x e f)‖ := norm_add_le _ _
    _ ≤ (M / s ^ 7) * (L * s) * (L * s) + (M / s ^ 6) * (N * s) :=
      add_le_add ((fderiv ℝ (fderiv ℝ W) (F x)).le_of_opNorm₂_le_of_le hDDW hDe hDf)
        ((fderiv ℝ W (F x)).le_of_opNorm_le_of_le hDW hDD)
    _ = _ := by field_simp

/-- Spatial gradient-length remainder estimates transfer to its angular Hessian
on a radial graph. The spatial estimates remain explicit hypotheses. -/
theorem levelGradSecond_radial_remainder_hessian_bound {ρ W : E3 → ℝ} {θ : E3}
    {P M : ℝ} (hθ : ‖θ‖ = 1) (hs : 1 ≤ ρ θ) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hρ : ContDiffAt ℝ 2 ρ θ) (hW : ContDiffAt ℝ 2 W (ρ θ • θ))
    (hDρ : ‖fderiv ℝ ρ θ‖ ≤ P) (hDDρ : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P)
    (hDW : ‖fderiv ℝ W (ρ θ • θ)‖ ≤ M / (ρ θ) ^ 6)
    (hDDW : ‖fderiv ℝ (fderiv ℝ W) (ρ θ • θ)‖ ≤ M / (ρ θ) ^ 7) :
    ‖fderiv ℝ (fderiv ℝ (fun y => W (ρ y • (‖y‖⁻¹ • y)))) θ‖ ≤
      M * ((P + 2) ^ 2 + (5 * P + 6)) / (ρ θ) ^ 5 := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hF : ContDiffAt ℝ 2 (fun y => ρ y • (‖y‖⁻¹ • y)) θ :=
    hρ.smul ((levelRadius_normalize_contDiffAt hθ0).of_le (by simp))
  have hW' : ContDiffAt ℝ 2 W (ρ θ • (‖θ‖⁻¹ • θ)) := by simpa only [hθ, inv_one, one_smul] using hW
  have hDW' : ‖fderiv ℝ W (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ M / (ρ θ) ^ 6 := by
    simpa only [hθ, inv_one, one_smul] using hDW
  have hDDW' : ‖fderiv ℝ (fderiv ℝ W) (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ M / (ρ θ) ^ 7 := by
    simpa only [hθ, inv_one, one_smul] using hDDW
  obtain ⟨hDF, hDDF⟩ := levelGradSecond_radial_map_bounds hθ hs hP hρ hDρ hDDρ
  exact levelGradSecond_composition_hessian_bound (by linarith) hM
    (by positivity) (by positivity) hF hW' hDF hDDF hDW' hDDW'

/-- The spatial gradient-length error whose first two derivatives must decay
with orders six and seven. The quadrupole term has degree minus four. -/
def levelGradSecond_spatialRemainder (u v : E3 → ℝ) (x : E3) : ℝ :=
  gradNorm u (x + (v 0)⁻¹ • gradient v 0) - v 0 * ‖x‖⁻¹ ^ 2 -
    3 * kelvinTranslatedQuadrupole v x * ‖x‖⁻¹ ^ 6

/-- On a positive radial graph, the spatial error is the difference between the
actual gradient length and the polar model. -/
theorem levelGradSecond_spatialRemainder_radial {u v ρ : E3 → ℝ} {y : E3}
    (hy : y ≠ 0) (hρ : 0 < ρ y) :
    levelGradSecond_spatialRemainder u v (ρ y • (‖y‖⁻¹ • y)) =
      gradNorm u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) -
        (v 0 * (ρ y)⁻¹ ^ 2 +
          3 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) * (ρ y)⁻¹ ^ 4) := by
  have hn : ‖ρ y • (‖y‖⁻¹ • y)‖ = ρ y := by
    simp [norm_smul, Real.norm_of_nonneg hρ.le, norm_ne_zero_iff.mpr hy]
  simp only [levelGradSecond_spatialRemainder, hn, kelvinTranslatedQuadrupole_smul]
  field_simp
  ring

/-- Subtracting an affine scalar multiple commutes with the second derivative. -/
theorem levelGradSecond_fderiv_two_sub_model {f q : E3 → ℝ} {x : E3} (b c : ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hq : ContDiffAt ℝ 2 q x) :
    fderiv ℝ (fderiv ℝ (fun y => f y - (b + c * q y))) x =
      fderiv ℝ (fderiv ℝ f) x - c • fderiv ℝ (fderiv ℝ q) x := by
  have he : fderiv ℝ (fun y => f y - (b + c * q y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y - c • fderiv ℝ q y) := by
    filter_upwards [hf.eventually (by norm_num), hq.eventually (by norm_num)] with y hy hz
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.sub
      (((hz.differentiableAt (by norm_num)).hasFDerivAt.const_mul c).const_add b)).fderiv
  rw [he.fderiv_eq]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    one_ne_zero).hasFDerivAt.sub
      (((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero).hasFDerivAt.const_smul c)).fderiv

/-- The second derivative is additive for twice continuously differentiable functions. -/
theorem levelGradSecond_fderiv_two_add {f g : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y + fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.add
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.add
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt).fderiv

/-- Exact Hessian decomposition of the actual level remainder into the composed
spatial error and the polar model. -/
theorem levelGradSecond_remainder_hessian_decomposition {u v ρ : E3 → ℝ} {t : ℝ}
    {θ : E3} (hθ : ‖θ‖ = 1) (hs : 0 < ρ θ) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hW : ContDiffAt ℝ 2 (levelGradSecond_spatialRemainder u v) (ρ θ • θ)) :
    fderiv ℝ (fderiv ℝ (levelGradRemainder u v t ρ)) θ =
      fderiv ℝ (fderiv ℝ (fun y =>
        levelGradSecond_spatialRemainder u v (ρ y • (‖y‖⁻¹ • y)))) θ +
      (fderiv ℝ (fderiv ℝ (fun y => v 0 * (ρ y)⁻¹ ^ 2 +
        3 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) * (ρ y)⁻¹ ^ 4)) θ -
      (t / v 0) ^ 4 • fderiv ℝ (fderiv ℝ
        (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  let q : E3 → ℝ := fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)
  let F : E3 → E3 := fun y => ρ y • (‖y‖⁻¹ • y)
  let m : E3 → ℝ := fun y => v 0 * (ρ y)⁻¹ ^ 2 + 3 * q y * (ρ y)⁻¹ ^ 4
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  have hq : ContDiffAt ℝ 2 q θ :=
    ((translated_quadrupole_contDiff v).of_le (by simp)).contDiffAt.comp θ hn
  have hm : ContDiffAt ℝ 2 m θ :=
    (contDiffAt_const.mul ((hρ.inv hs.ne').pow 2)).add
      ((contDiffAt_const.mul hq).mul ((hρ.inv hs.ne').pow 4))
  have hW' : ContDiffAt ℝ 2 (levelGradSecond_spatialRemainder u v) (F θ) := by
    simpa only [F, hθ, inv_one, one_smul] using hW
  have hcomp : ContDiffAt ℝ 2
      (fun y => levelGradSecond_spatialRemainder u v (F y)) θ := hW'.comp θ (hρ.smul hn)
  have he : levelGradRemainder u v t ρ =ᶠ[𝓝 θ]
      (fun y => levelGradSecond_spatialRemainder u v (F y) + m y -
        (t ^ 2 / v 0 + (t / v 0) ^ 4 * q y)) := by
    filter_upwards [isOpen_ne.mem_nhds hθ0,
      hρ.continuousAt.eventually (lt_mem_nhds hs)] with y hy hpos
    rw [levelGradSecond_spatialRemainder_radial hy hpos]
    dsimp [levelGradRemainder, m, q]
    rw [div_pow]
    ring
  rw [he.fderiv.fderiv_eq,
    levelGradSecond_fderiv_two_sub_model _ _ (hcomp.add hm) hq,
    levelGradSecond_fderiv_two_add hcomp hm]
  exact add_sub_assoc _ _ _

set_option maxHeartbeats 400000 in
-- The local assembly combines the explicit polar and spatial error constants.
/-- A local second angular derivative estimate for the actual level remainder.
The only gradient-length inputs are the two explicitly stated spatial error bounds. -/
theorem levelGradSecond_remainder_hessian_bound {u v ρ : E3 → ℝ} {θ : E3}
    {t A B K P M : ℝ} (hC : 0 < v 0) (ht : 0 ≤ t) (htC : t / v 0 ≤ 1)
    (hθ : ‖θ‖ = 1) (hs : 1 ≤ ρ θ) (hsa : (ρ θ)⁻¹ ≤ 2 * (t / v 0))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hρ : ContDiffAt ℝ 2 ρ θ)
    (hW : ContDiffAt ℝ 2 (levelGradSecond_spatialRemainder u v) (ρ θ • θ))
    (hinv : |(ρ θ)⁻¹ - t / v 0| ≤ K * (t / v 0) ^ 2)
    (hq₀ : |kelvinTranslatedQuadrupole v θ| ≤ B)
    (hq₁ : ‖fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ‖ ≤ B)
    (hq₂ : ‖fderiv ℝ (fderiv ℝ
      (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ‖ ≤ B)
    (hr₁ : ‖fderiv ℝ ρ θ‖ ≤ P * (t / v 0))
    (hr₂ : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P * (t / v 0))
    (herr : ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤
      A * (t / v 0) ^ 2)
    (hDW : ‖fderiv ℝ (levelGradSecond_spatialRemainder u v) (ρ θ • θ)‖ ≤
      M / (ρ θ) ^ 6)
    (hDDW : ‖fderiv ℝ (fderiv ℝ (levelGradSecond_spatialRemainder u v)) (ρ θ • θ)‖ ≤
      M / (ρ θ) ^ 7) :
    ‖fderiv ℝ (fderiv ℝ (levelGradRemainder u v t ρ)) θ‖ ≤
      ((16 * v 0 * A + 59 * K * B + 1152 * B * P + (96 * v 0 + 960 * B) * P ^ 2 +
        32 * M * ((P + 2) ^ 2 + (5 * P + 6))) / (v 0) ^ 5) * t ^ 5 := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hs0 : 0 < ρ θ := lt_of_lt_of_le zero_lt_one hs
  let q : E3 → ℝ := fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)
  have hq : ContDiffAt ℝ 2 q θ :=
    ((translated_quadrupole_contDiff v).contDiffAt.comp θ
      (levelRadius_normalize_contDiffAt hθ0)).of_le (by simp)
  have herr' : ‖fderiv ℝ (fderiv ℝ ρ) θ -
      ((t / v 0) / v 0) • fderiv ℝ (fderiv ℝ q) θ‖ ≤ A * (t / v 0) ^ 2 := by
    rw [levelRadiusRemainder_fderiv_two hθ0 hρ] at herr
    have hc : (t / v 0) / v 0 = t / (v 0) ^ 2 := by ring
    simpa only [hc] using herr
  have hq₀' : |q θ| ≤ B := by simpa only [q, hθ, inv_one, one_smul] using hq₀
  have hm := levelGradSecond_polar_model_hessian_bound hC (div_nonneg ht hC.le) htC
    hs0 ((inv_le_one₀ hs0).mpr hs) hsa hA hB hK hP hρ hq hinv hq₀' hq₁ hq₂
    hr₁ hr₂ herr'
  have hPa : P * (t / v 0) ≤ P := by nlinarith
  have hw := levelGradSecond_radial_remainder_hessian_bound hθ hs hP hM hρ hW
    (hr₁.trans hPa) (hr₂.trans hPa) hDW hDDW
  have hw' : ‖fderiv ℝ (fderiv ℝ (fun y =>
      levelGradSecond_spatialRemainder u v (ρ y • (‖y‖⁻¹ • y)))) θ‖ ≤
      (32 * M * ((P + 2) ^ 2 + (5 * P + 6))) * (t / v 0) ^ 5 := by
    apply hw.trans
    calc
      M * ((P + 2) ^ 2 + (5 * P + 6)) / (ρ θ) ^ 5 =
          M * ((P + 2) ^ 2 + (5 * P + 6)) * (ρ θ)⁻¹ ^ 5 := by rw [inv_pow]; ring
      _ ≤ M * ((P + 2) ^ 2 + (5 * P + 6)) * (2 * (t / v 0)) ^ 5 := by
        gcongr
      _ = _ := by ring
  rw [levelGradSecond_remainder_hessian_decomposition hθ hs0 hρ hW]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (fun y =>
          levelGradSecond_spatialRemainder u v (ρ y • (‖y‖⁻¹ • y)))) θ‖ +
        ‖fderiv ℝ (fderiv ℝ (fun y => v 0 * (ρ y)⁻¹ ^ 2 +
          3 * q y * (ρ y)⁻¹ ^ 4)) θ -
          (t / v 0) ^ 4 • fderiv ℝ (fderiv ℝ q) θ‖ := by
      exact norm_add_le
        (fderiv ℝ (fderiv ℝ (fun y =>
          levelGradSecond_spatialRemainder u v (ρ y • (‖y‖⁻¹ • y)))) θ)
        (fderiv ℝ (fderiv ℝ (fun y => v 0 * (ρ y)⁻¹ ^ 2 +
          3 * q y * (ρ y)⁻¹ ^ 4)) θ -
          (t / v 0) ^ 4 • fderiv ℝ (fderiv ℝ q) θ)
    _ ≤ (32 * M * ((P + 2) ^ 2 + (5 * P + 6))) * (t / v 0) ^ 5 +
        (16 * v 0 * A + 59 * K * B + 1152 * B * P +
          (96 * v 0 + 960 * B) * P ^ 2) * (t / v 0) ^ 5 := add_le_add hw' hm
    _ = _ := by rw [div_pow]; ring

end LiquidDrop.CapacitaryK
