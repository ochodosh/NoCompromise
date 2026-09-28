import NoCompromise.CapacitaryK.LevelAreaSecondDerivative
import NoCompromise.CapacitaryK.LevelGradSecondDerivative

/-!
# Radial and tangential gradient components on capacitary levels

The Coulomb term cancels identically in the tangential projection. All derivatives
below are ambient Fréchet derivatives of the normalized angular extensions.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK


/-- The normalization map has uniformly bounded first two derivatives on the sphere. -/
theorem levelAreaComp_normalize_bounds {θ : E3} (hθ : ‖θ‖ = 1) :
    ‖fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ‖ ≤ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y)) θ‖ ≤ 6 := by
  constructor
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    intro e he
    rw [levelRadius_normalize_fderiv hθ]
    simpa only [real_inner_comm θ e, he, mul_one] using
      (levelRadius_tangent_norm_le (w := e) hθ)
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    intro f hf
    rw [levelRadius_normalize_fderiv_two hθ]
    exact levelRadius_normalize_fderiv_two_bound hθ he hf

/-- The second derivative of a vector inner product, with all four product terms. -/
theorem levelAreaComp_fderiv_two_inner {G N : E3 → E3} {x : E3}
    (hG : ContDiffAt ℝ 2 G x) (hN : ContDiffAt ℝ 2 N x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => ⟪G y, N y⟫)) x e f =
      ⟪G x, fderiv ℝ (fderiv ℝ N) x e f⟫ +
        ⟪fderiv ℝ G x e, fderiv ℝ N x f⟫ +
        ⟪fderiv ℝ G x f, fderiv ℝ N x e⟫ +
        ⟪fderiv ℝ (fderiv ℝ G) x e f, N x⟫ := by
  have hGd := hG.differentiableAt (by norm_num)
  have hNd := hN.differentiableAt (by norm_num)
  have hDG := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDN := (hN.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc := ((hG.inner ℝ hN).fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => ⟪G z, N z⟫) y f) =ᶠ[𝓝 x]
      (fun y => ⟪G y, fderiv ℝ N y f⟫ + ⟪fderiv ℝ G y f, N y⟫) := by
    filter_upwards [hG.eventually (by norm_num), hN.eventually (by norm_num)] with y hy hz
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.inner ℝ
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hGd.hasFDerivAt.inner ℝ
    (hDN.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).add
      ((hDG.hasFDerivAt.clm_apply (hasFDerivAt_const f x)).inner ℝ hNd.hasFDerivAt)
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc] using hid

/-- Product bounds for a vector field paired with the unit angular direction. -/
theorem levelAreaComp_radial_bounds {G : E3 → E3} {θ : E3}
    (hθ : ‖θ‖ = 1) (hG : ContDiffAt ℝ 2 G θ) :
    |⟪G θ, ‖θ‖⁻¹ • θ⟫| ≤ ‖G θ‖ ∧
      ‖fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫) θ‖ ≤
        ‖fderiv ℝ G θ‖ + 2 * ‖G θ‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫)) θ‖ ≤
        ‖fderiv ℝ (fderiv ℝ G) θ‖ + 4 * ‖fderiv ℝ G θ‖ + 6 * ‖G θ‖ := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  obtain ⟨hn1, hn2⟩ := levelAreaComp_normalize_bounds hθ
  have hD (e : E3) (he : ‖e‖ = 1) : ‖fderiv ℝ G θ e‖ ≤ ‖fderiv ℝ G θ‖ := by
    simpa only [he, mul_one] using (fderiv ℝ G θ).le_opNorm e
  have hDn (e : E3) (he : ‖e‖ = 1) :
      ‖fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ e‖ ≤ 2 := by
    simpa only [he, mul_one] using
      (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ).le_of_opNorm_le hn1 e
  refine ⟨?_, ?_, ?_⟩
  · simpa [hθ] using abs_real_inner_le_norm (G θ) θ
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    rw [((hG.differentiableAt (by norm_num)).hasFDerivAt.inner ℝ
      (hn.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    change |⟪G θ, fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ e⟫ +
      ⟪fderiv ℝ G θ e, ‖θ‖⁻¹ • θ⟫| ≤ _
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)).trans
    simp only [hθ, inv_one, one_smul]
    calc
      _ ≤ ‖G θ‖ * 2 + ‖fderiv ℝ G θ‖ * 1 := by
        gcongr
        · exact hDn e he
        · exact hD e he
      _ = _ := by ring
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDD : ‖fderiv ℝ (fderiv ℝ G) θ e f‖ ≤ ‖fderiv ℝ (fderiv ℝ G) θ‖ := by
      simpa only [he, hf, mul_one] using (fderiv ℝ (fderiv ℝ G) θ).le_opNorm₂ e f
    have hDDn : ‖fderiv ℝ (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y)) θ e f‖ ≤ 6 := by
      rw [levelRadius_normalize_fderiv_two hθ]
      exact levelRadius_normalize_fderiv_two_bound hθ he hf
    rw [levelAreaComp_fderiv_two_inner hG hn, Real.norm_eq_abs]
    apply ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)).trans
    apply (add_le_add (add_le_add (add_le_add (abs_real_inner_le_norm _ _)
      (abs_real_inner_le_norm _ _)) (abs_real_inner_le_norm _ _))
        (abs_real_inner_le_norm _ _)).trans
    simp only [hθ, inv_one, one_smul]
    calc
      _ ≤ ‖G θ‖ * 6 + ‖fderiv ℝ G θ‖ * 2 + ‖fderiv ℝ G θ‖ * 2 +
          ‖fderiv ℝ (fderiv ℝ G) θ‖ * 1 := by
        gcongr
        · exact hD e he
        · exact hDn f hf
        · exact hD f hf
        · exact hDn e he
      _ = _ := by ring

/-- Subtraction commutes with the vector-valued second derivative at smooth points. -/
theorem levelAreaComp_fderiv_two_sub {G H : E3 → E3} {x : E3}
    (hG : ContDiffAt ℝ 2 G x) (hH : ContDiffAt ℝ 2 H x) :
    fderiv ℝ (fderiv ℝ (fun y => G y - H y)) x =
      fderiv ℝ (fderiv ℝ G) x - fderiv ℝ (fderiv ℝ H) x := by
  have he : fderiv ℝ (fun y => G y - H y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ G y - fderiv ℝ H y) := by
    filter_upwards [hG.eventually (by norm_num), hH.eventually (by norm_num)] with y hy hz
    exact fderiv_fun_sub (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num))
  rw [he.fderiv_eq, fderiv_fun_sub
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    ((hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]

/-- Projecting a field with three bounded jets onto the moving tangent plane
preserves those bounds, with a fixed numerical loss. -/
theorem levelAreaComp_tangential_bounds {G : E3 → E3} {θ : E3} {J : ℝ}
    (hθ : ‖θ‖ = 1) (hG : ContDiffAt ℝ 2 G θ)
    (hG0 : ‖G θ‖ ≤ J) (hG1 : ‖fderiv ℝ G θ‖ ≤ J)
    (hG2 : ‖fderiv ℝ (fderiv ℝ G) θ‖ ≤ J) :
    ‖G θ - ⟪G θ, ‖θ‖⁻¹ • θ⟫ • (‖θ‖⁻¹ • θ)‖ ≤ 30 * J ∧
      ‖fderiv ℝ (fun y => G y - ⟪G y, ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y)) θ‖ ≤ 30 * J ∧
      ‖fderiv ℝ (fderiv ℝ
        (fun y => G y - ⟪G y, ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y))) θ‖ ≤ 30 * J := by
  have hJ : 0 ≤ J := (norm_nonneg _).trans hG0
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  have ha := hG.inner ℝ hn
  obtain ⟨ha0, ha1, ha2⟩ := levelAreaComp_radial_bounds hθ hG
  have ha0' : |⟪G θ, ‖θ‖⁻¹ • θ⟫| ≤ J := ha0.trans hG0
  have ha1' : ‖fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫) θ‖ ≤ 3 * J := by
    linarith
  have ha2' : ‖fderiv ℝ (fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫)) θ‖ ≤ 11 * J := by
    linarith
  obtain ⟨hn1, hn2⟩ := levelAreaComp_normalize_bounds hθ
  obtain ⟨hm1, hm2⟩ := levelAreaSecond_smul_bounds ha hn
  have hn0 : ‖‖θ‖⁻¹ • θ‖ = 1 := by simp [hθ]
  rw [hn0] at hm1 hm2
  have hm1' : ‖fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y)) θ‖ ≤
      5 * J := hm1.trans (calc
        _ ≤ J * 2 + 3 * J * 1 := by gcongr
        _ = _ := by ring)
  have hm2' : ‖fderiv ℝ (fderiv ℝ
      (fun y => ⟪G y, ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y))) θ‖ ≤ 29 * J :=
    hm2.trans (calc
      _ ≤ J * 6 + 2 * (3 * J) * 2 + 11 * J * 1 := by gcongr
      _ = _ := by ring)
  have hprod : ContDiffAt ℝ 2
      (fun y => ⟪G y, ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y)) θ := ha.smul hn
  refine ⟨?_, ?_, ?_⟩
  · have hb := levelRadius_tangent_norm_le (w := G θ) hθ
    simp only [hθ, inv_one, one_smul]
    linarith
  · rw [fderiv_fun_sub (hG.differentiableAt (by norm_num))
      (hprod.differentiableAt (by norm_num))]
    apply (norm_sub_le _ _).trans
    linarith
  · rw [levelAreaComp_fderiv_two_sub hG hprod]
    apply (norm_sub_le (E := E3 →L[ℝ] E3 →L[ℝ] E3) _ _).trans
    linarith


/-- Decay of the non-Coulomb potential through third order. -/
theorem levelAreaComp_nonmonopole_bounds {Q W : E3 → ℝ} {R M : ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hM : 0 ≤ M) (hW : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hWb : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ W x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ M / ‖x‖ ^ 6 ∧
      ‖iteratedFDeriv ℝ 3 W x‖ ≤ M / ‖x‖ ^ 7) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E3, R < ‖x‖ → 1 ≤ ‖x‖ →
      ContDiffAt ℝ 3 (fun y => farQuadrupole Q y + W y) x ∧
      ‖iteratedFDeriv ℝ 1 (fun y => farQuadrupole Q y + W y) x‖ ≤ B / ‖x‖ ^ 4 ∧
      ‖iteratedFDeriv ℝ 2 (fun y => farQuadrupole Q y + W y) x‖ ≤ B / ‖x‖ ^ 5 ∧
      ‖iteratedFDeriv ℝ 3 (fun y => farQuadrupole Q y + W y) x‖ ≤ B / ‖x‖ ^ 6 := by
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds hQ hQh
  obtain ⟨D, hD, hDb⟩ := levelAreaSecond_farQuadrupole_third_derivative_bound hQ hQh
  refine ⟨B + D + M, by positivity, fun x hx hx1 => ?_⟩
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
  have hq : ContDiffAt ℝ 3 (farQuadrupole Q) x :=
    (contDiffAt_farQuadrupole hQ hx0).of_le (by simp)
  have hw : ContDiffAt ℝ 3 W x :=
    (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)).of_le
      (by simp)
  have hdec (k : ℕ) : M / ‖x‖ ^ (k + 1) ≤ M / ‖x‖ ^ k := by
    apply div_le_div_of_nonneg_left hM (by positivity)
    exact pow_le_pow_right₀ hx1 (Nat.le_succ k)
  obtain ⟨hw1, hw2, hw3⟩ := hWb x hx.le
  obtain ⟨_, hq1, hq2⟩ := hBb x hx0
  have heq (F : E3 → ℝ) : ‖iteratedFDeriv ℝ 2 F x‖ =
      ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ F), norm_iteratedFDeriv_fderiv]
  refine ⟨hq.add hw, ?_, ?_, ?_⟩
  · rw [fun_iteratedFDeriv_add_apply (hq.of_le (by norm_num)) (hw.of_le (by norm_num))]
    apply (norm_add_le _ _).trans
    simp only [norm_iteratedFDeriv_one]
    calc
      _ ≤ B / ‖x‖ ^ 4 + M / ‖x‖ ^ 4 := add_le_add hq1 (hw1.trans (hdec 4))
      _ ≤ (B + D + M) / ‖x‖ ^ 4 := by
        rw [add_div, add_div]
        have : 0 ≤ D / ‖x‖ ^ 4 := by positivity
        linarith
  · rw [fun_iteratedFDeriv_add_apply (hq.of_le (by norm_num)) (hw.of_le (by norm_num))]
    apply (norm_add_le _ _).trans
    simp only [heq]
    calc
      _ ≤ B / ‖x‖ ^ 5 + M / ‖x‖ ^ 5 := add_le_add hq2 (hw2.trans (hdec 5))
      _ ≤ (B + D + M) / ‖x‖ ^ 5 := by
        rw [add_div, add_div]
        have : 0 ≤ D / ‖x‖ ^ 5 := by positivity
        linarith
  · rw [fun_iteratedFDeriv_add_apply hq hw]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ D / ‖x‖ ^ 6 + M / ‖x‖ ^ 6 := add_le_add (hDb x hx0) (hw3.trans (hdec 6))
      _ ≤ (B + D + M) / ‖x‖ ^ 6 := by
        rw [add_div, add_div]
        have : 0 ≤ B / ‖x‖ ^ 6 := by positivity
        linarith

/-- Two angular derivatives preserve the fourth-order gradient decay. -/
theorem levelAreaComp_gradient_comp_decay {F : E3 → E3} {E : E3 → ℝ} {x : E3}
    {s L B : ℝ} (hs : 0 < s) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hF : ContDiffAt ℝ 2 F x) (hE : ContDiffAt ℝ 3 E (F x))
    (hF1 : ‖fderiv ℝ F x‖ ≤ L * s)
    (hF2 : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L * s)
    (hE1 : ‖iteratedFDeriv ℝ 1 E (F x)‖ ≤ B / s ^ 4)
    (hE2 : ‖iteratedFDeriv ℝ 2 E (F x)‖ ≤ B / s ^ 5)
    (hE3 : ‖iteratedFDeriv ℝ 3 E (F x)‖ ≤ B / s ^ 6) :
    ‖gradient E (F x)‖ ≤ B * (1 + L + L ^ 2) / s ^ 4 ∧
      ‖fderiv ℝ (fun y => gradient E (F y)) x‖ ≤ B * (1 + L + L ^ 2) / s ^ 4 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => gradient E (F y))) x‖ ≤
        B * (1 + L + L ^ 2) / s ^ 4 := by
  obtain ⟨h1, h2⟩ := levelAreaSecond_gradient_comp_bounds hF hE
  have h0 : ‖gradient E (F x)‖ ≤ B / s ^ 4 := by
    simpa only [gradient, (toDual ℝ E3).symm.norm_map, norm_iteratedFDeriv_one] using hE1
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩
  · gcongr
    nlinarith [sq_nonneg L]
  · calc
      _ ≤ (B / s ^ 5) * (L * s) := by gcongr
      _ = B * L / s ^ 4 := by field_simp
      _ ≤ _ := by gcongr; nlinarith [sq_nonneg L]
  · calc
      _ ≤ (B / s ^ 6) * (L * s) ^ 2 + (B / s ^ 5) * (L * s) := by gcongr
      _ = B * (L ^ 2 + L) / s ^ 4 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hB) (by positivity)

/-- The Coulomb gradient is radial after composition with the normalized graph. -/
theorem levelAreaComp_monopole_composition (C : ℝ) {s : ℝ} (hs : 0 < s)
    {y : E3} (hy : y ≠ 0) :
    gradient (fun x : E3 => C / ‖x‖) (s • (‖y‖⁻¹ • y)) =
      (-C * s⁻¹ ^ 2) • (‖y‖⁻¹ • y) := by
  have hn : ‖‖y‖⁻¹ • y‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy]
  have hn0 : ‖y‖⁻¹ • y ≠ 0 := by intro h; simp [h] at hn
  have hnorm : ‖s • (‖y‖⁻¹ • y)‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hn, mul_one]
  rw [gradient_monopole C (smul_ne_zero hs.ne' hn0), hnorm, smul_smul]
  congr 1
  field_simp

/-- The two components agree locally with their Coulomb and non-Coulomb parts.
In the tangential component the Coulomb term cancels before differentiation. -/
theorem levelAreaComp_components_eventuallyEq {u v ρ E : E3 → ℝ} {θ : E3}
    (hθ : ‖θ‖ = 1) (hs : 0 < ρ θ) (hρ : ContinuousAt ρ θ)
    (hE : ContDiffAt ℝ 1 E (ρ θ • θ))
    (heq : (fun x => u (x + (v 0)⁻¹ • gradient v 0)) =
      fun x => v 0 / ‖x‖ + E x) :
    levelAreaSecond_radialGradient u v ρ =ᶠ[𝓝 θ]
      (fun y => -v 0 * (ρ y)⁻¹ ^ 2 + ⟪gradient E (ρ y • (‖y‖⁻¹ • y)), ‖y‖⁻¹ • y⟫) ∧
    levelAreaSecond_tangentialGradient u v ρ =ᶠ[𝓝 θ]
      (fun y => gradient E (ρ y • (‖y‖⁻¹ • y)) -
        ⟪gradient E (ρ y • (‖y‖⁻¹ • y)), ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y)) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hF : ContinuousAt (fun y => ρ y • (‖y‖⁻¹ • y)) θ :=
    hρ.smul (levelRadius_normalize_contDiffAt hθ0).continuousAt
  have hE' : ContDiffAt ℝ 1 E (ρ θ • (‖θ‖⁻¹ • θ)) := by simpa [hθ] using hE
  have hevent := hF.eventually (hE'.eventually (by norm_num))
  have hboth : ∀ᶠ y in 𝓝 θ,
      levelAreaSecond_radialGradient u v ρ y =
        -v 0 * (ρ y)⁻¹ ^ 2 + ⟪gradient E (ρ y • (‖y‖⁻¹ • y)), ‖y‖⁻¹ • y⟫ ∧
      levelAreaSecond_tangentialGradient u v ρ y =
        gradient E (ρ y • (‖y‖⁻¹ • y)) -
          ⟪gradient E (ρ y • (‖y‖⁻¹ • y)), ‖y‖⁻¹ • y⟫ • (‖y‖⁻¹ • y) := by
    filter_upwards [isOpen_ne.mem_nhds hθ0, hρ.eventually (lt_mem_nhds hs), hevent]
      with y hy hsy hEy
    have hn : ‖‖y‖⁻¹ • y‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy]
    have hn0 : ‖y‖⁻¹ • y ≠ 0 := by intro h; simp [h] at hn
    have hmono := (contDiffAt_monopole (v 0) (smul_ne_zero hsy.ne' hn0)).differentiableAt
      (by simp)
    have hg : gradient u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) =
        (-v 0 * (ρ y)⁻¹ ^ 2) • (‖y‖⁻¹ • y) +
          gradient E (ρ y • (‖y‖⁻¹ • y)) := by
      have htrans (x : E3) : gradient (fun x => u (x + (v 0)⁻¹ • gradient v 0)) x =
          gradient u (x + (v 0)⁻¹ • gradient v 0) := by
        simp only [gradient, fderiv_comp_add_right]
      rw [← htrans, heq, levelGrad_gradient_add hmono (hEy.differentiableAt one_ne_zero),
        levelAreaComp_monopole_composition (v 0) hsy hy]
    have ha : levelAreaSecond_radialGradient u v ρ y =
        -v 0 * (ρ y)⁻¹ ^ 2 + ⟪gradient E (ρ y • (‖y‖⁻¹ • y)), ‖y‖⁻¹ • y⟫ := by
      simp only [levelAreaSecond_radialGradient, hg, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
    refine ⟨ha, ?_⟩
    rw [levelAreaSecond_tangentialGradient, hg, ha, add_smul]
    abel
  exact ⟨hboth.mono (fun _ h => h.1), hboth.mono (fun _ h => h.2)⟩


/-- Coarse first and second derivative bounds for the composed radial Coulomb term. -/
theorem levelAreaComp_monopole_radial_bounds {ρ : E3 → ℝ} {x : E3} {C P : ℝ}
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hs : 1 ≤ ρ x) (hρ : ContDiffAt ℝ 2 ρ x)
    (hρ1 : ‖fderiv ℝ ρ x‖ ≤ P) (hρ2 : ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ P) :
    ‖fderiv ℝ (fun y => -C * (ρ y)⁻¹ ^ 2) x‖ ≤ C * (6 * P ^ 2 + 2 * P) / (ρ x) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => -C * (ρ y)⁻¹ ^ 2)) x‖ ≤
        C * (6 * P ^ 2 + 2 * P) / (ρ x) ^ 2 := by
  have hs0 : 0 < ρ x := zero_lt_one.trans_le hs
  have hi : 0 ≤ (ρ x)⁻¹ := inv_nonneg.mpr hs0.le
  have hi1 : (ρ x)⁻¹ ≤ 1 := (inv_le_one₀ hs0).mpr hs
  have hi3 : (ρ x)⁻¹ ^ 3 ≤ (ρ x)⁻¹ ^ 2 := pow_le_pow_of_le_one hi hi1 (by norm_num)
  have hi4 : (ρ x)⁻¹ ^ 4 ≤ (ρ x)⁻¹ ^ 2 := pow_le_pow_of_le_one hi hi1 (by norm_num)
  have hfirst : fderiv ℝ (fun y => -C * (ρ y)⁻¹ ^ 2) x =
      (2 * C * (ρ x)⁻¹ ^ 3) • fderiv ℝ ρ x := by
    simpa using levelGradSecond_polar_model_fderiv (-C) (q := fun _ => 0)
      (hρ.differentiableAt (by norm_num)) (differentiableAt_const 0) hs0.ne'
  have hsecond (e f : E3) :
      fderiv ℝ (fderiv ℝ (fun y => -C * (ρ y)⁻¹ ^ 2)) x e f =
        (2 * C * (ρ x)⁻¹ ^ 3) * fderiv ℝ (fderiv ℝ ρ) x e f -
          (6 * C * (ρ x)⁻¹ ^ 4) * fderiv ℝ ρ x e * fderiv ℝ ρ x f := by
    simpa [sub_eq_add_neg] using levelGradSecond_polar_model_fderiv_two (-C)
      (q := fun _ => 0) hρ contDiffAt_const hs0.ne' e f
  constructor
  · rw [hfirst, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (2 * C * (ρ x)⁻¹ ^ 2) * P := by gcongr
      _ ≤ C * (6 * P ^ 2 + 2 * P) * (ρ x)⁻¹ ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg hC (sq_nonneg P)) (sq_nonneg (ρ x)⁻¹)]
      _ = _ := by rw [inv_pow, div_eq_mul_inv]
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have he' : |fderiv ℝ ρ x e| ≤ P := by
      simpa [he] using (fderiv ℝ ρ x).le_of_opNorm_le hρ1 e
    have hf' : |fderiv ℝ ρ x f| ≤ P := by
      simpa [hf] using (fderiv ℝ ρ x).le_of_opNorm_le hρ1 f
    have hef : |fderiv ℝ (fderiv ℝ ρ) x e f| ≤ P := by
      simpa [he, hf] using (fderiv ℝ (fderiv ℝ ρ) x).le_of_opNorm₂_le_of_le hρ2 he.le hf.le
    rw [hsecond, Real.norm_eq_abs]
    apply (abs_sub _ _).trans
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * C * (ρ x)⁻¹ ^ 4),
      abs_of_nonneg (by positivity : 0 ≤ 2 * C * (ρ x)⁻¹ ^ 3)]
    calc
      _ ≤ (2 * C * (ρ x)⁻¹ ^ 2) * P + (6 * C * (ρ x)⁻¹ ^ 2) * P * P := by
        gcongr
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

/-- A non-Coulomb error below half the Coulomb radial size gives a quantitative
nonvanishing estimate, including the reciprocal bound used by the area quotient. -/
theorem levelAreaComp_radial_inverse_bound {a C s J : ℝ}
    (hC : 0 < C) (hs : 0 < s)
    (herr : |a + C / s ^ 2| ≤ J / s ^ 4) (hsmall : J / s ^ 2 ≤ C / 2) :
    a ≠ 0 ∧ |a⁻¹| ≤ 2 * s ^ 2 / C := by
  have herror : J / s ^ 4 ≤ C / (2 * s ^ 2) := by
    calc
      _ = (J / s ^ 2) / s ^ 2 := by ring
      _ ≤ (C / 2) / s ^ 2 := div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  have ha : a ≤ -(C / (2 * s ^ 2)) := by
    have := (abs_le.mp herr).2
    have he : C / s ^ 2 = 2 * (C / (2 * s ^ 2)) := by ring
    linarith
  have han : a < 0 := lt_of_le_of_lt ha (neg_neg_of_pos (by positivity))
  refine ⟨han.ne, ?_⟩
  rw [abs_inv, abs_of_neg han]
  calc
    _ ≤ (C / (2 * s ^ 2))⁻¹ :=
      (inv_le_inv₀ (by linarith) (by positivity)).mpr (by linarith)
    _ = _ := by field_simp


/-- Component estimates on one large radial graph, from the non-Coulomb jets.
The hypotheses state all radius, smoothness, and smallness requirements explicitly. -/
theorem levelAreaComp_components_bounds {u v ρ E : E3 → ℝ} {θ : E3} {P J : ℝ}
    (hC : 0 < v 0) (hP : 0 ≤ P) (hJ : 0 ≤ J) (hθ : ‖θ‖ = 1) (hs : 1 ≤ ρ θ)
    (hρ : ContDiffAt ℝ 2 ρ θ)
    (hρ1 : ‖fderiv ℝ ρ θ‖ ≤ P) (hρ2 : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P)
    (hE : ContDiffAt ℝ 3 E (ρ θ • θ))
    (heq : (fun x => u (x + (v 0)⁻¹ • gradient v 0)) =
      fun x => v 0 / ‖x‖ + E x)
    (hG0 : ‖gradient E (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ J / (ρ θ) ^ 4)
    (hG1 : ‖fderiv ℝ (fun y => gradient E (ρ y • (‖y‖⁻¹ • y))) θ‖ ≤ J / (ρ θ) ^ 4)
    (hG2 : ‖fderiv ℝ (fderiv ℝ (fun y => gradient E (ρ y • (‖y‖⁻¹ • y)))) θ‖ ≤
      J / (ρ θ) ^ 4)
    (hsmall : J / (ρ θ) ^ 2 ≤ v 0 / 2) :
    levelAreaSecond_radialGradient u v ρ θ ≠ 0 ∧
      |(levelAreaSecond_radialGradient u v ρ θ)⁻¹| ≤ 2 * (ρ θ) ^ 2 / v 0 ∧
      ‖fderiv ℝ (levelAreaSecond_radialGradient u v ρ) θ‖ ≤
        (v 0 * (6 * P ^ 2 + 2 * P) + 11 * J) / (ρ θ) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_radialGradient u v ρ)) θ‖ ≤
        (v 0 * (6 * P ^ 2 + 2 * P) + 11 * J) / (ρ θ) ^ 2 ∧
      ‖levelAreaSecond_tangentialGradient u v ρ θ‖ ≤ 30 * J / (ρ θ) ^ 4 ∧
      ‖fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ) θ‖ ≤ 30 * J / (ρ θ) ^ 4 ∧
      ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ)) θ‖ ≤
        30 * J / (ρ θ) ^ 4 := by
  have hs0 : 0 < ρ θ := zero_lt_one.trans_le hs
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  let G : E3 → E3 := fun y => gradient E (ρ y • (‖y‖⁻¹ • y))
  have hE' : ContDiffAt ℝ 3 E (ρ θ • (‖θ‖⁻¹ • θ)) := by simpa [hθ] using hE
  have hgrad : ContDiffAt ℝ 2 (gradient E) (ρ θ • (‖θ‖⁻¹ • θ)) :=
    (toDual ℝ E3).symm.contDiff.contDiffAt.comp _
      (hE'.fderiv_right (m := 2) (by norm_num))
  have hF : ContDiffAt ℝ 2 (fun y => ρ y • (‖y‖⁻¹ • y)) θ := hρ.smul hn
  have hG : ContDiffAt ℝ 2 G θ :=
    ContDiffAt.comp θ (f := fun y => ρ y • (‖y‖⁻¹ • y)) (g := gradient E) hgrad hF
  have hb : ContDiffAt ℝ 2 (fun y => ⟪G y, ‖y‖⁻¹ • y⟫) θ := hG.inner ℝ hn
  have hm : ContDiffAt ℝ 2 (fun y => -v 0 * (ρ y)⁻¹ ^ 2) θ :=
    contDiffAt_const.mul ((hρ.inv hs0.ne').pow 2)
  obtain ⟨ha, hT⟩ := levelAreaComp_components_eventuallyEq hθ hs0 hρ.continuousAt
    (hE.of_le (by norm_num)) heq
  obtain ⟨hb0, hb1, hb2⟩ := levelAreaComp_radial_bounds hθ hG
  have herror : |levelAreaSecond_radialGradient u v ρ θ + v 0 / (ρ θ) ^ 2| ≤
      J / (ρ θ) ^ 4 := by
    rw [ha.eq_of_nhds]
    have hid : -v 0 * (ρ θ)⁻¹ ^ 2 + ⟪G θ, ‖θ‖⁻¹ • θ⟫ + v 0 / (ρ θ) ^ 2 =
        ⟪G θ, ‖θ‖⁻¹ • θ⟫ := by rw [inv_pow, div_eq_mul_inv]; ring
    change |-v 0 * (ρ θ)⁻¹ ^ 2 + ⟪G θ, ‖θ‖⁻¹ • θ⟫ + v 0 / (ρ θ) ^ 2| ≤ _
    rw [hid]
    exact hb0.trans hG0
  obtain ⟨ha0, hai⟩ := levelAreaComp_radial_inverse_bound hC hs0 herror hsmall
  obtain ⟨hm1, hm2⟩ := levelAreaComp_monopole_radial_bounds hC.le hP hs hρ hρ1 hρ2
  have hdec : J / (ρ θ) ^ 4 ≤ J / (ρ θ) ^ 2 := by
    exact div_le_div_of_nonneg_left hJ (by positivity)
      (pow_le_pow_right₀ hs (by norm_num))
  have hb1' : ‖fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫) θ‖ ≤ 11 * J / (ρ θ) ^ 2 := by
    have hbound : ‖fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫) θ‖ ≤ 3 * (J / (ρ θ) ^ 4) := by
      change ‖G θ‖ ≤ _ at hG0
      change ‖fderiv ℝ G θ‖ ≤ _ at hG1
      linarith
    have : 0 ≤ J / (ρ θ) ^ 2 := by positivity
    rw [mul_div_assoc]
    linarith
  have hb2' : ‖fderiv ℝ (fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫)) θ‖ ≤
      11 * J / (ρ θ) ^ 2 := by
    have hbound : ‖fderiv ℝ (fderiv ℝ (fun y => ⟪G y, ‖y‖⁻¹ • y⟫)) θ‖ ≤
        11 * (J / (ρ θ) ^ 4) := by
      change ‖G θ‖ ≤ _ at hG0
      change ‖fderiv ℝ G θ‖ ≤ _ at hG1
      change ‖fderiv ℝ (fderiv ℝ G) θ‖ ≤ _ at hG2
      linarith
    rw [mul_div_assoc]
    linarith
  obtain ⟨hT0, hT1, hT2⟩ := levelAreaComp_tangential_bounds hθ hG hG0 hG1 hG2
  refine ⟨ha0, hai, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha.fderiv_eq]
    change ‖fderiv ℝ (fun y => -v 0 * (ρ y)⁻¹ ^ 2 + ⟪G y, ‖y‖⁻¹ • y⟫) θ‖ ≤ _
    rw [fderiv_fun_add (hm.differentiableAt (by norm_num))
      (hb.differentiableAt (by norm_num))]
    apply (norm_add_le _ _).trans
    exact (add_le_add hm1 hb1').trans_eq (by ring)
  · rw [ha.fderiv.fderiv_eq]
    change ‖fderiv ℝ (fderiv ℝ
      (fun y => -v 0 * (ρ y)⁻¹ ^ 2 + ⟪G y, ‖y‖⁻¹ • y⟫)) θ‖ ≤ _
    rw [levelAreaSecond_fderiv_two_add hm hb]
    apply (norm_add_le (E := E3 →L[ℝ] E3 →L[ℝ] ℝ) _ _).trans
    exact (add_le_add hm2 hb2').trans_eq (by ring)
  · rw [hT.eq_of_nhds]
    exact hT0.trans_eq (by ring)
  · rw [hT.fderiv_eq]
    exact hT1.trans_eq (by ring)
  · rw [hT.fderiv.fderiv_eq]
    exact hT2.trans_eq (by ring)


set_option maxSynthPendingDepth 8 in
set_option maxHeartbeats 1000000 in
-- The uniform assembly combines third derivatives and several existential constants.
/-- Uniform component bounds for every admissible small capacitary level graph,
together with the coarse radius jets needed for the area Hessian estimate. -/
theorem levelAreaComp_capacitary_bounds
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ S D B : ℝ, 0 ≤ S ∧ 0 ≤ D ∧ 0 ≤ B ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ρ : E3 → ℝ,
          (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
          (∀ θ : E3, ‖θ‖ = 1 →
            0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
          ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} ∧
          ∀ θ : E3, ‖θ‖ = 1 →
            |ρ θ| ≤ S / t ∧ ‖fderiv ℝ ρ θ‖ ≤ S / t ∧
            ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ S / t ∧
            levelAreaSecond_radialGradient u v ρ θ ≠ 0 ∧
            |(levelAreaSecond_radialGradient u v ρ θ)⁻¹| ≤ D / t ^ 2 ∧
            ‖fderiv ℝ (levelAreaSecond_radialGradient u v ρ) θ‖ ≤ D * t ^ 2 ∧
            ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_radialGradient u v ρ)) θ‖ ≤ D * t ^ 2 ∧
            ‖levelAreaSecond_tangentialGradient u v ρ θ‖ ≤ B * t ^ 4 ∧
            ‖fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ) θ‖ ≤ B * t ^ 4 ∧
            ‖fderiv ℝ (fderiv ℝ (levelAreaSecond_tangentialGradient u v ρ)) θ‖ ≤
              B * t ^ 4 := by
  obtain ⟨v, r, hr, hv, he, hv0, R, M, hR, hM, hW, hWb⟩ :=
    levelGradSecond_capacitary_translated_remainder_derivatives
      hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨vr, rr, hrr, hvr, her, _, Ar, hAr, hevR⟩ :=
    capacitary_level_radius_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0r, hgr, hQr⟩ := kelvin_extension_data_eq hrr hr hvr hv her he
  have hrem (t : ℝ) (ρ : E3 → ℝ) : levelRadiusRemainder vr t ρ =
      levelRadiusRemainder v t ρ := by
    funext y
    simp only [levelRadiusRemainder, h0r, hQr]
  simp only [hrem, h0r, hgr] at hevR
  obtain ⟨B, hB, hBb⟩ := levelAreaComp_nonmonopole_bounds
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v) hM hW
    (fun x hx => by
      simpa only [levelGradSecond_norm_iteratedFDeriv_three] using (hWb x hx).2)
  obtain ⟨Bq, hBq, hBqb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v)
  let E : E3 → ℝ := fun y => farQuadrupole (kelvinTranslatedQuadrupole v) y +
    kelvinTranslatedRemainder u v y
  have hEq : (fun x => u (x + (v 0)⁻¹ • gradient v 0)) =
      fun x => v 0 / ‖x‖ + E x := by
    funext x
    dsimp [E, farQuadrupole, kelvinTranslatedRemainder]
    ring
  let L := Ar + Bq / (v 0) ^ 2
  let P := Ar + 10 * Bq / (v 0) ^ 2
  let S := v 0 + L + P
  let H := 2 / v 0
  let N := 5 * P + 6
  let J := B * (1 + N + N ^ 2)
  let D₀ := v 0 * (6 * P ^ 2 + 2 * P) + 11 * J
  let D := 2 * S ^ 2 / v 0 + D₀ * H ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨v, r, hr, hv, he, hv0, S, D, 30 * J * H ^ 4, hS, hD, by positivity, ?_⟩
  have eL := level_eventually_lt_of_continuous (g := fun t => t * L)
    (continuous_id.mul continuous_const) (by simp) (by positivity : 0 < v 0 / 2)
  have eR := level_eventually_lt_of_continuous (g := fun t => t * (R + 1 + L))
    (continuous_id.mul continuous_const) (by simp) hv0
  have eJ := level_eventually_lt_of_continuous (g := fun t => J * (H * t) ^ 2)
    (continuous_const.mul ((continuous_const.mul continuous_id).pow 2)) (by simp)
    (by positivity : 0 < v 0 / 2)
  filter_upwards [hevR, Ioo_mem_nhdsGT one_pos, eL, eR, eJ]
    with t htR htr htL htRfar htJ
  have ht : 0 < t := htr.1
  have ht1 : t ≤ 1 := htr.2.le
  intro ρ hhom hroot
  obtain ⟨hρsmooth, hρb⟩ := htR ρ hhom hroot
  refine ⟨hρsmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hρ : ContDiffAt ℝ 2 ρ θ :=
    (hρsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  have hs : 0 < ρ θ := (hroot θ hθ).1
  obtain ⟨hE0, hE1, hE2⟩ := hρb θ hθ
  have hq : |kelvinTranslatedQuadrupole v θ| ≤ Bq := by
    simpa only [farQuadrupole, hθ, one_pow, div_one] using (hBqb θ hθ0).1
  have hqD : ‖fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ Bq := by
    simpa only [hθ, one_pow, div_one] using (hBqb θ hθ0).2.1
  have hqDD : ‖fderiv ℝ (fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v))) θ‖ ≤
      Bq := by simpa only [hθ, one_pow, div_one] using (hBqb θ hθ0).2.2
  obtain ⟨hρD, hρDD⟩ := levelArea_radius_derivative_bounds ht.le ht1 hAr hBq.le hθ hρ
    hqD hqDD hE1 hE2
  change ‖fderiv ℝ ρ θ‖ ≤ P * t at hρD
  change ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P * t at hρDD
  have hρD' : ‖fderiv ℝ ρ θ‖ ≤ P := hρD.trans (mul_le_of_le_one_right hP ht1)
  have hρDD' : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P :=
    hρDD.trans (mul_le_of_le_one_right hP ht1)
  have hcoarse : |ρ θ - v 0 / t| ≤ L := by
    have hterm : |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| ≤ Bq / (v 0) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg (v 0))]
      exact div_le_div_of_nonneg_right
        ((mul_le_mul ht1 hq (abs_nonneg _) zero_le_one).trans_eq (one_mul Bq))
        (sq_nonneg _)
    have hE' : |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤
        Ar * t ^ 2 := by simpa only [levelRadiusRemainder, hθ, inv_one, one_smul] using hE0
    calc
      _ = |(ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)) +
          t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ Ar * t ^ 2 + Bq / (v 0) ^ 2 := add_le_add hE' hterm
      _ ≤ L := by dsimp [L]; nlinarith [pow_le_one₀ ht.le ht1 (n := 2)]
  have hlower : v 0 / t - L ≤ ρ θ := by have := (abs_le.mp hcoarse).1; linarith
  have hupper : ρ θ ≤ v 0 / t + L := by have := (abs_le.mp hcoarse).2; linarith
  have hhalf : v 0 / (2 * t) ≤ ρ θ := by
    have hLt : L ≤ v 0 / (2 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have heq : v 0 / t - v 0 / (2 * t) = v 0 / (2 * t) := by ring
    linarith
  have hinv : (ρ θ)⁻¹ ≤ H * t := by
    have hi := (inv_le_inv₀ hs (by positivity : 0 < v 0 / (2 * t))).mpr hhalf
    exact hi.trans_eq (by dsimp [H]; field_simp)
  have hsfar : R + 1 < ρ θ := by
    have hrlt : R + 1 + L < v 0 / t := by
      rw [lt_div_iff₀ ht]
      nlinarith
    linarith
  have hsR : R < ρ θ := by linarith
  have hs1 : 1 ≤ ρ θ := by linarith
  have hSupper : ρ θ ≤ S / t := by
    rw [le_div_iff₀ ht]
    have hm := mul_le_mul_of_nonneg_right hupper ht.le
    rw [add_mul, div_mul_cancel₀ _ ht.ne'] at hm
    have hLt : L * t ≤ L := mul_le_of_le_one_right hL ht1
    dsimp [S]
    linarith
  have hPS : P ≤ S / t := by
    rw [le_div_iff₀ ht]
    dsimp [S]
    nlinarith
  have hnorm : ‖ρ θ • θ‖ = ρ θ := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hθ, mul_one]
  obtain ⟨hEc, hEb1, hEb2, hEb3⟩ := hBb (ρ θ • θ) (by simpa [hnorm] using hsR)
    (by simpa [hnorm] using hs1)
  rw [hnorm] at hEb1 hEb2 hEb3
  have hEc' : ContDiffAt ℝ 3 E (ρ θ • (‖θ‖⁻¹ • θ)) := by
    simpa only [hθ, inv_one, one_smul] using hEc
  have hEb1' : ‖iteratedFDeriv ℝ 1 E (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ B / (ρ θ) ^ 4 := by
    simpa only [hθ, inv_one, one_smul] using hEb1
  have hEb2' : ‖iteratedFDeriv ℝ 2 E (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ B / (ρ θ) ^ 5 := by
    simpa only [hθ, inv_one, one_smul] using hEb2
  have hEb3' : ‖iteratedFDeriv ℝ 3 E (ρ θ • (‖θ‖⁻¹ • θ))‖ ≤ B / (ρ θ) ^ 6 := by
    simpa only [hθ, inv_one, one_smul] using hEb3
  have hF : ContDiffAt ℝ 2 (fun y => ρ y • (‖y‖⁻¹ • y)) θ :=
    hρ.smul ((levelRadius_normalize_contDiffAt hθ0).of_le (by simp))
  obtain ⟨hF1, hF2⟩ := levelGradSecond_radial_map_bounds hθ hs1 hP hρ hρD' hρDD'
  have hF1' : ‖fderiv ℝ (fun y => ρ y • (‖y‖⁻¹ • y)) θ‖ ≤ N * ρ θ :=
    hF1.trans (by dsimp [N]; nlinarith)
  obtain ⟨hG0, hG1, hG2⟩ := levelAreaComp_gradient_comp_decay hs hN hB hF hEc'
    hF1' hF2 hEb1' hEb2' hEb3'
  have hsmall : J / (ρ θ) ^ 2 ≤ v 0 / 2 := by
    calc
      _ = J * (ρ θ)⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
      _ ≤ J * (H * t) ^ 2 := by gcongr
      _ ≤ _ := htJ.le
  obtain ⟨ha0, hai, ha1, ha2, hT0, hT1, hT2⟩ := levelAreaComp_components_bounds
    hv0 hP hJ hθ hs1 hρ hρD' hρDD' hEc hEq hG0 hG1 hG2 hsmall
  have hrad : D₀ / (ρ θ) ^ 2 ≤ D * t ^ 2 := by
    calc
      _ = D₀ * (ρ θ)⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
      _ ≤ D₀ * (H * t) ^ 2 := by gcongr
      _ = (D₀ * H ^ 2) * t ^ 2 := by ring
      _ ≤ _ := by
        gcongr
        dsimp [D]
        exact le_add_of_nonneg_left (by positivity)
  have htan : 30 * J / (ρ θ) ^ 4 ≤ (30 * J * H ^ 4) * t ^ 4 := by
    calc
      _ = 30 * J * (ρ θ)⁻¹ ^ 4 := by rw [inv_pow, div_eq_mul_inv]
      _ ≤ 30 * J * (H * t) ^ 4 := by gcongr
      _ = _ := by ring
  refine ⟨by rwa [abs_of_pos hs], hρD'.trans hPS, hρDD'.trans hPS, ha0, ?_,
    ha1.trans hrad, ha2.trans hrad, hT0.trans htan, hT1.trans htan, hT2.trans htan⟩
  apply hai.trans
  calc
    _ ≤ 2 * (S / t) ^ 2 / v 0 := by gcongr
    _ = (2 * S ^ 2 / v 0) / t ^ 2 := by ring
    _ ≤ D / t ^ 2 := by
      gcongr
      dsimp [D]
      exact le_add_of_nonneg_right (by positivity)


set_option maxHeartbeats 600000 in
-- Three capacitary expansions must be aligned using their common Kelvin data.
/-- `eq:K-dA`: the area-density remainder and its first two angular derivatives
are uniformly `O(t)` on small capacitary levels, under the original hypotheses. -/
theorem capacitary_level_area_derivatives
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ρ : E3 → ℝ,
        (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
        (∀ θ : E3, ‖θ‖ = 1 →
          0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
        ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} ∧
        ∀ θ : E3, ‖θ‖ = 1 →
          |levelAreaRemainder u v t ρ θ| ≤ A * t ∧
          ‖fderiv ℝ (levelAreaRemainder u v t ρ) θ‖ ≤ A * t ∧
          ‖fderiv ℝ (fderiv ℝ (levelAreaRemainder u v t ρ)) θ‖ ≤ A * t := by
  obtain ⟨v, r, hr, hv, he, hv0, S, D, B, hS, hD, hB, hevC⟩ :=
    levelAreaComp_capacitary_bounds hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨va, ra, hra, hva, hea, _, Aa, hAa, hevA⟩ :=
    capacitary_level_area_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0a, hga, hQa⟩ := kelvin_extension_data_eq hra hr hva hv hea he
  have hrem (t : ℝ) (ρ : E3 → ℝ) : levelAreaRemainder u va t ρ =
      levelAreaRemainder u v t ρ := by
    funext y
    simp only [levelAreaRemainder, h0a, hga, hQa]
  simp only [hrem, h0a, hga] at hevA
  obtain ⟨vq, rq, hrq, hvq, heq, _, Aq, _, hevQ⟩ :=
    levelAreaSecond_capacitary_radius_square_bound hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0q, hgq, hQq⟩ := kelvin_extension_data_eq hrq hr hvq hv heq he
  simp only [h0q, hgq, hQq] at hevQ
  let N := B * (D + 3 * D ^ 3 + 2 * D ^ 5)
  let A₂ := Aq + S ^ 2 * (10 * N ^ 2 + N ^ 4)
  refine ⟨v, r, hr, hv, he, hv0, max Aa A₂, hAa.trans (le_max_left _ _), ?_⟩
  have huSmooth := capacitary_potential_contDiffOn hK hu hh
  filter_upwards [hevC, hevA, hevQ, Ioo_mem_nhdsGT one_pos] with t htC htA htQ htr
  have ht : 0 < t := htr.1
  intro ρ hhom hroot
  obtain ⟨hρsmooth, hCb⟩ := htC ρ hhom hroot
  have hAb := (htA ρ hhom hroot).2
  have hQb := (htQ ρ hhom hroot).2
  refine ⟨hρsmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hρ : ContDiffAt ℝ 2 ρ θ :=
    (hρsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  have hx : ρ θ • θ + (v 0)⁻¹ • gradient v 0 ∈ Kᶜ := by
    intro hxK
    have heq := hb _ hxK
    rw [(hroot θ hθ).2] at heq
    exact htr.2.ne heq
  have hu3 : ContDiffAt ℝ 3 u (ρ θ • (‖θ‖⁻¹ • θ) + (v 0)⁻¹ • gradient v 0) := by
    simpa only [hθ, inv_one, one_smul] using
      (huSmooth.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx)).of_le
        (by simp : (3 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  obtain ⟨hρ0, hρ1, hρ2, ha0, hai, ha1, ha2, hT0, hT1, hT2⟩ := hCb θ hθ
  have hsecond : ‖fderiv ℝ (fderiv ℝ (levelAreaRemainder u v t ρ)) θ‖ ≤ A₂ * t :=
    levelAreaSecond_remainder_bound_of_components hθ0 hS hD hB ht htr.2.le hρ hu3 ha0
      (hQb θ hθ) hρ0 hρ1 hρ2 hai ha1 ha2 hT0 hT1 hT2
  obtain ⟨hval, hfirst⟩ := hAb θ hθ
  exact ⟨hval.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le),
    hfirst.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le),
    hsecond.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le)⟩

end LiquidDrop.CapacitaryK
