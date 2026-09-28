import NoCompromise.CapacitaryK.LevelRadiusDerivatives

/-!
# Second derivatives of the capacitary level radius

Differential identities for the zero-homogeneous extension of a radial level graph.
All derivatives in this file are ambient Fréchet derivatives.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The second derivative chain rule, evaluated on two vectors. -/
theorem levelRadius_fderiv_two_comp {F : E3 → E3} {U : E3 → ℝ} {x : E3}
    (hF : ContDiffAt ℝ 2 F x) (hU : ContDiffAt ℝ 2 U (F x)) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => U (F y))) x e f =
      fderiv ℝ (fderiv ℝ U) (F x) (fderiv ℝ F x e) (fderiv ℝ F x f) +
        fderiv ℝ U (F x) (fderiv ℝ (fderiv ℝ F) x e f) := by
  have hFd := hF.differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => U (F z)) y f) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ U (F y) (fderiv ℝ F y f)) := by
    filter_upwards [hF.eventually (by norm_num),
      hFd.continuousAt.eventually (hU.eventually (by norm_num))] with y hy hz
    rw [fderiv_fun_comp y (hz.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))]
    rfl
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) (F x) :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc : DifferentiableAt ℝ (fderiv ℝ (fun z => U (F z))) x :=
    ((hU.comp x hF).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hDU.hasFDerivAt.comp x hFd.hasFDerivAt).clm_apply
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const f x))
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_comm] using hid

/-- The second derivative product rule for a scalar times a vector. -/
theorem levelRadius_fderiv_two_smul {a : E3 → ℝ} {F : E3 → E3} {x : E3}
    (ha : ContDiffAt ℝ 2 a x) (hF : ContDiffAt ℝ 2 F x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => a y • F y)) x e f =
      a x • fderiv ℝ (fderiv ℝ F) x e f +
        fderiv ℝ a x e • fderiv ℝ F x f +
        fderiv ℝ a x f • fderiv ℝ F x e +
        fderiv ℝ (fderiv ℝ a) x e f • F x := by
  have had := ha.differentiableAt (by norm_num)
  have hFd := hF.differentiableAt (by norm_num)
  have hDa : DifferentiableAt ℝ (fderiv ℝ a) x :=
    (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc : DifferentiableAt ℝ (fderiv ℝ (fun y => a y • F y)) x :=
    ((ha.smul hF).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => a z • F z) y f) =ᶠ[𝓝 x]
      (fun y => a y • fderiv ℝ F y f + fderiv ℝ a y f • F y) := by
    filter_upwards [ha.eventually (by norm_num), hF.eventually (by norm_num)] with y hy hz
    change fderiv ℝ (a • F) y f = _
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.smul
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (had.hasFDerivAt.smul
    (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).add
      ((hDa.hasFDerivAt.clm_apply (hasFDerivAt_const f x)).smul hFd.hasFDerivAt)
  have hid := congrArg (fun L : E3 →L[ℝ] E3 => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc] using hid

/-- The derivative of normalization at a unit vector is the tangential projection. -/
theorem levelRadius_normalize_fderiv {θ : E3} (hθ : ‖θ‖ = 1) (e : E3) :
    fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y) θ e = e - ⟪θ, e⟫ • θ := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hi := (hasFDerivAt_monopole 1 hθ0).smul (hasFDerivAt_id θ)
  simp only [one_div] at hi
  change fderiv ℝ ((fun y : E3 => ‖y‖⁻¹) • id) θ e = _
  rw [hi.fderiv]
  simp [hθ, sub_eq_add_neg]

/-- The second derivative of normalization at a unit vector. -/
theorem levelRadius_normalize_fderiv_two {θ : E3} (hθ : ‖θ‖ = 1) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y : E3 => ‖y‖⁻¹ • y)) θ e f =
      (3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
        ⟪θ, e⟫ • f - ⟪θ, f⟫ • e := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hi : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹) θ := by
    exact (contDiffAt_norm ℝ hθ0).inv (norm_ne_zero_iff.mpr hθ0)
  have hd := hasFDerivAt_monopole 1 hθ0
  have hdd := fderiv_two_monopole 1 hθ0 e f
  simp only [one_div] at hd hdd
  rw [levelRadius_fderiv_two_smul (F := fun y => y) hi contDiffAt_id, hdd, hd.fderiv]
  have hid : fderiv ℝ (fun y : E3 => y) = fun _ => ContinuousLinearMap.id ℝ E3 := by
    funext y
    exact fderiv_id
  rw [hid, fderiv_fun_const]
  simp [hθ]
  module

/-- Smoothness of normalization away from zero. -/
theorem levelRadius_normalize_contDiffAt {x : E3} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E3 => ‖y‖⁻¹ • y) x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- The first derivative of the radial parametrization, at a unit vector. -/
theorem levelRadius_levelMap_fderiv {ρ : E3 → ℝ} {θ : E3} (hθ : ‖θ‖ = 1)
    (hρ : DifferentiableAt ℝ ρ θ) (e : E3) :
    fderiv ℝ (fun y => ρ y • (‖y‖⁻¹ • y)) θ e =
      fderiv ℝ ρ θ e • θ + ρ θ • (e - ⟪θ, e⟫ • θ) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hd := hρ.hasFDerivAt.smul
    ((levelRadius_normalize_contDiffAt hθ0).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun y => ρ y • (‖y‖⁻¹ • y)) _ θ at hd
  rw [hd.fderiv]
  simp [levelRadius_normalize_fderiv hθ, hθ, add_comm]

/-- The twice-differentiated level equation, with the second derivative of the
radius isolated on the left. No division by the radial derivative is used. -/
theorem levelRadius_implicit_fderiv_two {U : E3 → ℝ} {t : ℝ} {ρ : E3 → ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    {θ : E3} (hθ : ‖θ‖ = 1) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hU : ContDiffAt ℝ 2 U (ρ θ • θ)) (e f : E3) :
    let P : E3 → E3 := fun w => w - ⟪θ, w⟫ • θ
    let A : E3 → E3 := fun w => fderiv ℝ ρ θ w • θ + ρ θ • P w
    fderiv ℝ U (ρ θ • θ) θ * fderiv ℝ (fderiv ℝ ρ) θ e f =
      -fderiv ℝ (fderiv ℝ U) (ρ θ • θ) (A e) (A f) -
        fderiv ℝ ρ θ e * fderiv ℝ U (ρ θ • θ) (P f) -
        fderiv ℝ ρ θ f * fderiv ℝ U (ρ θ • θ) (P e) -
        ρ θ * fderiv ℝ U (ρ θ • θ)
          ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
            ⟪θ, e⟫ • f - ⟪θ, f⟫ • e) := by
  dsimp only
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hn : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  have hconst : (fun y => U (ρ y • (‖y‖⁻¹ • y))) =ᶠ[𝓝 θ] fun _ => t := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    rw [hhom y hy]
    exact hroot _ (by simp [norm_smul, norm_ne_zero_iff.mpr hy])
  have hz : fderiv ℝ (fderiv ℝ (fun y => U (ρ y • (‖y‖⁻¹ • y)))) θ e f = 0 := by
    rw [hconst.fderiv.fderiv_eq]
    simp
  have hU' : ContDiffAt ℝ 2 U (ρ θ • (‖θ‖⁻¹ • θ)) := by simpa [hθ] using hU
  rw [levelRadius_fderiv_two_comp (F := fun y => ρ y • (‖y‖⁻¹ • y))
      (hρ.smul hn) hU',
    levelRadius_levelMap_fderiv hθ (hρ.differentiableAt (by norm_num)),
    levelRadius_levelMap_fderiv hθ (hρ.differentiableAt (by norm_num)),
    levelRadius_fderiv_two_smul hρ hn, levelRadius_normalize_fderiv_two hθ,
    levelRadius_normalize_fderiv hθ, levelRadius_normalize_fderiv hθ] at hz
  simp only [hθ, inv_one, one_smul, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul] at hz ⊢
  linear_combination hz

/-- The angular Hessian of a quadratic coefficient is the Hessian of its
degree-minus-three potential composed with normalization. -/
theorem levelRadius_angular_fderiv_two {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {θ : E3} (hθ : ‖θ‖ = 1) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => Q (‖y‖⁻¹ • y))) θ e f =
      fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ
        (e - ⟪θ, e⟫ • θ) (f - ⟪θ, f⟫ • θ) +
      fderiv ℝ (farQuadrupole Q) θ
        ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
          ⟪θ, e⟫ • f - ⟪θ, f⟫ • e) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have he : (fun y => Q (‖y‖⁻¹ • y)) =ᶠ[𝓝 θ]
      (fun y => farQuadrupole Q (‖y‖⁻¹ • y)) := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    have hn : ‖‖y‖⁻¹ • y‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy]
    simp [farQuadrupole, hn]
  have hF : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) θ :=
    (levelRadius_normalize_contDiffAt hθ0).of_le (by simp)
  have hU : ContDiffAt ℝ 2 (farQuadrupole Q) (‖θ‖⁻¹ • θ) := by
    simpa only [hθ, inv_one, one_smul] using
      (contDiffAt_farQuadrupole hQ hθ0).of_le (by simp : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  rw [he.fderiv.fderiv_eq, levelRadius_fderiv_two_comp hF hU,
    levelRadius_normalize_fderiv hθ, levelRadius_normalize_fderiv hθ,
    levelRadius_normalize_fderiv_two hθ]
  simp only [hθ, inv_one, one_smul]

/-- A uniform bound for the Hessian of normalization on pairs of unit vectors. -/
theorem levelRadius_normalize_fderiv_two_bound {θ e f : E3}
    (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖(3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e‖ ≤ 6 := by
  have hae : |⟪θ, e⟫| ≤ 1 := by simpa [hθ, he] using abs_real_inner_le_norm θ e
  have haf : |⟪θ, f⟫| ≤ 1 := by simpa [hθ, hf] using abs_real_inner_le_norm θ f
  have hef : |⟪e, f⟫| ≤ 1 := by simpa [he, hf] using abs_real_inner_le_norm e f
  have hab : |3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫| ≤ 4 := by
    calc
      _ ≤ |3 * ⟪θ, e⟫ * ⟪θ, f⟫| + |⟪e, f⟫| := abs_sub _ _
      _ ≤ 3 * 1 * 1 + 1 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        gcongr
      _ = 4 := by norm_num
  calc
    _ ≤ ‖(3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ‖ +
        ‖⟪θ, e⟫ • f‖ + ‖⟪θ, f⟫ • e‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 4 + 1 + 1 := by
      simp only [norm_smul, Real.norm_eq_abs, hθ, he, hf, mul_one]
      gcongr
    _ = 6 := by norm_num

/-- Bounds for the two far-quadrupole derivatives control the angular Hessian. -/
theorem levelRadius_angular_fderiv_two_bound {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {B : ℝ} (hB : 0 ≤ B)
    {θ : E3} (hθ : ‖θ‖ = 1)
    (hD : ‖fderiv ℝ (farQuadrupole Q) θ‖ ≤ B)
    (hDD : ‖fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ‖ ≤ B) :
    ‖fderiv ℝ (fderiv ℝ (fun y => Q (‖y‖⁻¹ • y))) θ‖ ≤ 10 * B := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro f hf
  have hPe : ‖e - ⟪θ, e⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ e, he, mul_one] using
      (levelRadius_tangent_norm_le (w := e) hθ)
  have hPf : ‖f - ⟪θ, f⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ f, hf, mul_one] using
      (levelRadius_tangent_norm_le (w := f) hθ)
  rw [levelRadius_angular_fderiv_two hQ hθ]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ
        (e - ⟪θ, e⟫ • θ) (f - ⟪θ, f⟫ • θ)‖ +
        ‖fderiv ℝ (farQuadrupole Q) θ
          ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
            ⟪θ, e⟫ • f - ⟪θ, f⟫ • e)‖ := norm_add_le _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ‖ *
        ‖e - ⟪θ, e⟫ • θ‖) * ‖f - ⟪θ, f⟫ • θ‖ +
        ‖fderiv ℝ (farQuadrupole Q) θ‖ *
          ‖(3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
            ⟪θ, e⟫ • f - ⟪θ, f⟫ • e‖ := by
      exact add_le_add
        (((fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right
            ((fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ).le_opNorm _) (norm_nonneg _)))
        ((fderiv ℝ (farQuadrupole Q) θ).le_opNorm _)
    _ ≤ (B * 2) * 2 + B * 6 := by
      gcongr
      exact levelRadius_normalize_fderiv_two_bound hθ he hf
    _ = 10 * B := by ring

/-- The radial Coulomb terms cancel in the twice-differentiated level equation.
The only remaining term is quadratic in the first derivatives of the radius. -/
theorem levelRadius_monopole_cancellation {θ : E3} (hθ : ‖θ‖ = 1)
    {s : ℝ} (hs : 0 < s) (C a b : ℝ) (e f : E3) :
    let P : E3 → E3 := fun w => w - ⟪θ, w⟫ • θ
    let N := (3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e
    fderiv ℝ (fderiv ℝ (fun y : E3 => C / ‖y‖)) (s • θ)
        (a • θ + s • P e) (b • θ + s • P f) +
      a * fderiv ℝ (fun y : E3 => C / ‖y‖) (s • θ) (P f) +
      b * fderiv ℝ (fun y : E3 => C / ‖y‖) (s • θ) (P e) +
      s * fderiv ℝ (fun y : E3 => C / ‖y‖) (s • θ) N =
        2 * C / s ^ 3 * a * b := by
  dsimp only
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hx : s • θ ≠ 0 := smul_ne_zero hs.ne' hθ0
  have hn : ‖s • θ‖ = s := by simp [norm_smul, abs_of_pos hs, hθ]
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  rw [fderiv_two_monopole C hx, (hasFDerivAt_monopole C hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right, hθθ, hn, real_inner_comm e θ, real_inner_comm f θ]
  field_simp
  ring

/-- The Hessian of the radius error subtracts the angular model Hessian. -/
theorem levelRadiusRemainder_fderiv_two {v : E3 → ℝ} {t : ℝ} {ρ : E3 → ℝ}
    {x : E3} (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x) :
    fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x =
      fderiv ℝ (fderiv ℝ ρ) x - (t / (v 0) ^ 2) •
        fderiv ℝ (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x := by
  let q : E3 → ℝ := fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)
  have hq : ContDiffAt ℝ 2 q x :=
    ((translated_quadrupole_contDiff v).contDiffAt.comp x
      (levelRadius_normalize_contDiffAt hx)).of_le (by simp)
  have he : levelRadiusRemainder v t ρ = fun y =>
      ρ y - (v 0 / t + (t / (v 0) ^ 2) * q y) := by
    funext y
    dsimp [levelRadiusRemainder, q]
    ring
  have heD : fderiv ℝ (levelRadiusRemainder v t ρ) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ ρ y - (t / (v 0) ^ 2) • fderiv ℝ q y) := by
    filter_upwards [hρ.eventually (by norm_num), hq.eventually (by norm_num)] with y hy hz
    rw [he]
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.sub
      (((hz.differentiableAt (by norm_num)).hasFDerivAt.const_mul
        (t / (v 0) ^ 2)).const_add (v 0 / t))).fderiv
  rw [heD.fderiv_eq]
  exact (((hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt
    one_ne_zero).hasFDerivAt.sub
      (((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero).hasFDerivAt.const_smul (t / (v 0) ^ 2))).fderiv

/-- Exact cancellation of the monopole and the leading angular quadrupole in
the Hessian equation. The maps `dw` and `hw` represent the remainder derivatives. -/
theorem levelRadius_hessian_error_identity {U Q : E3 → ℝ} {t C : ℝ} {ρ : E3 → ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {θ : E3} (hθ : ‖θ‖ = 1)
    (hs : 0 < ρ θ) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hU : ContDiffAt ℝ 2 U (ρ θ • θ))
    (dw : E3 →L[ℝ] ℝ) (hw : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hD : fderiv ℝ U (ρ θ • θ) =
      fderiv ℝ (fun y : E3 => C / ‖y‖) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 4 • fderiv ℝ (farQuadrupole Q) θ + dw)
    (hDD : fderiv ℝ (fderiv ℝ U) (ρ θ • θ) =
      fderiv ℝ (fderiv ℝ (fun y : E3 => C / ‖y‖)) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 5 • fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ + hw)
    (e f : E3) :
    let s := ρ θ
    let p := fderiv ℝ ρ θ
    let d := fderiv ℝ (farQuadrupole Q) θ
    let H := fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ
    let P : E3 → E3 := fun w => w - ⟪θ, w⟫ • θ
    let A : E3 → E3 := fun w => p w • θ + s • P w
    let N := (3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e
    (-s ^ 2 * fderiv ℝ U (s • θ) θ) * fderiv ℝ (fderiv ℝ ρ) θ e f -
        s⁻¹ * fderiv ℝ (fderiv ℝ (fun y => Q (‖y‖⁻¹ • y))) θ e f =
      2 * C * s⁻¹ * p e * p f +
        s⁻¹ ^ 3 * p e * p f * H θ θ +
        s⁻¹ ^ 2 * p e * H θ (P f) + s⁻¹ ^ 2 * p f * H (P e) θ +
        s⁻¹ ^ 2 * p e * d (P f) + s⁻¹ ^ 2 * p f * d (P e) +
        s ^ 2 * hw (A e) (A f) +
        s ^ 2 * p e * dw (P f) + s ^ 2 * p f * dw (P e) + s ^ 3 * dw N := by
  dsimp only
  have hi := levelRadius_implicit_fderiv_two hhom hroot hθ hρ hU e f
  have hm := levelRadius_monopole_cancellation hθ hs C
    (fderiv ℝ ρ θ e) (fderiv ℝ ρ θ f) e f
  have hq := levelRadius_angular_fderiv_two hQ hθ e f
  dsimp only at hi hm
  rw [hD, hDD] at hi
  rw [hq, hD]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hi hm ⊢
  linear_combination (norm := (field_simp; ring))
    -(ρ θ) ^ 2 * hi + (ρ θ) ^ 2 * hm

/-- Scalar inversion of the Hessian equation in any real normed space. -/
theorem levelRadius_hessian_inversion_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C D B L ε t a : ℝ} {H V : F}
    (hC : 0 < C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : C / 2 ≤ a) (had : |a - C| ≤ D * ε ^ 2)
    (het : |ε - t / C| ≤ D / C * ε ^ 2) (hH : ‖H‖ ≤ B)
    (hres : ‖a • V - ε • H‖ ≤ L * ε ^ 2) :
    ‖V - (t / C ^ 2) • H‖ ≤
      (2 / C * ((D / C + D / C ^ 2) * B + L)) * ε ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hD : 0 ≤ D * ε ^ 2 := (abs_nonneg _).trans had
  have hc : |ε - a * t / C ^ 2| ≤ (D / C + D / C ^ 2) * ε ^ 2 := by
    have hid : ε - a * t / C ^ 2 = (ε - t / C) - (a - C) * t / C ^ 2 := by
      field_simp
      ring
    have hterm : |(a - C) * t / C ^ 2| ≤ D / C ^ 2 * ε ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg ht, abs_of_nonneg (sq_nonneg C)]
      calc
        _ ≤ (D * ε ^ 2) * 1 / C ^ 2 := by gcongr
        _ = _ := by ring
    rw [hid]
    exact (abs_sub _ _).trans ((add_le_add het hterm).trans_eq (by ring))
  have hid : a • (V - (t / C ^ 2) • H) =
      (a • V - ε • H) + (ε - a * t / C ^ 2) • H := by
    simp only [smul_sub, smul_smul]
    module
  have hn : a * ‖V - (t / C ^ 2) • H‖ ≤
      ((D / C + D / C ^ 2) * B + L) * ε ^ 2 := by
    calc
      _ = ‖a • (V - (t / C ^ 2) • H)‖ := by
        rw [norm_smul, Real.norm_of_nonneg ha0.le]
      _ ≤ ‖a • V - ε • H‖ + |ε - a * t / C ^ 2| * ‖H‖ := by
        rw [hid]
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_add_le (a • V - ε • H) ((ε - a * t / C ^ 2) • H)
      _ ≤ L * ε ^ 2 + ((D / C + D / C ^ 2) * ε ^ 2) * B :=
        add_le_add hres (mul_le_mul hc hH (norm_nonneg _) ((abs_nonneg _).trans hc))
      _ = _ := by ring
  have hhalf := mul_le_mul_of_nonneg_right ha (norm_nonneg (V - (t / C ^ 2) • H))
  have hm := mul_le_mul_of_nonneg_left (hhalf.trans hn) (by positivity : 0 ≤ 2 / C)
  have hid' : 2 / C * (C / 2 * ‖V - (t / C ^ 2) • H‖) =
      ‖V - (t / C ^ 2) • H‖ := by field_simp
  rw [hid'] at hm
  simpa only [mul_assoc] using hm

private theorem levelRadius_decay_mono {s A : ℝ} (hs : 1 ≤ s) (hA : 0 ≤ A)
    {p q : ℕ} (hpq : p ≤ q) : A / s ^ q ≤ A / s ^ p :=
  div_le_div_of_nonneg_left hA (by positivity) (pow_le_pow_right₀ hs hpq)

/-- The error terms in the cancelled Hessian equation have order `s⁻²`.
Only first derivative control of the radius is used here. -/
theorem levelRadius_hessian_residual_bound {s C B M P a b : ℝ}
    (hs : 1 ≤ s) (hB : 0 ≤ B) (hM : 0 ≤ M) (hP : 0 ≤ P)
    {θ e f : E3} (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (ha : |a| ≤ P / s) (hb : |b| ≤ P / s)
    (d dw : E3 →L[ℝ] ℝ) (H hw : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hd : ‖d‖ ≤ B) (hH : ‖H‖ ≤ B)
    (hdw : ‖dw‖ ≤ M / s ^ 5) (hhw : ‖hw‖ ≤ M / s ^ 6) :
    let T : E3 → E3 := fun w => w - ⟪θ, w⟫ • θ
    let N := (3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e
    |2 * C * s⁻¹ * a * b + s⁻¹ ^ 3 * a * b * H θ θ +
        s⁻¹ ^ 2 * a * H θ (T f) + s⁻¹ ^ 2 * b * H (T e) θ +
        s⁻¹ ^ 2 * a * d (T f) + s⁻¹ ^ 2 * b * d (T e) +
        s ^ 2 * hw (a • θ + s • T e) (b • θ + s • T f) +
        s ^ 2 * a * dw (T f) + s ^ 2 * b * dw (T e) + s ^ 3 * dw N| ≤
      (2 * |C| * P ^ 2 + B * P ^ 2 + 8 * B * P +
        M * (P + 2) ^ 2 + 4 * M * P + 6 * M) / s ^ 2 := by
  dsimp only
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hTe : ‖e - ⟪θ, e⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ e, he, mul_one] using
      (levelRadius_tangent_norm_le (w := e) hθ)
  have hTf : ‖f - ⟪θ, f⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ f, hf, mul_one] using
      (levelRadius_tangent_norm_le (w := f) hθ)
  have hN := levelRadius_normalize_fderiv_two_bound hθ he hf
  have hA : ‖a • θ + s • (e - ⟪θ, e⟫ • θ)‖ ≤ (P + 2) * s := by
    calc
      _ ≤ ‖a • θ‖ + ‖s • (e - ⟪θ, e⟫ • θ)‖ := norm_add_le _ _
      _ ≤ P / s + s * 2 := by
        simp only [norm_smul, Real.norm_eq_abs, hθ, mul_one, abs_of_pos hs0]
        gcongr
      _ ≤ P * s + s * 2 := by
        gcongr
        exact (div_le_self hP hs).trans (le_mul_of_one_le_right hP hs)
      _ = _ := by ring
  have hA' : ‖b • θ + s • (f - ⟪θ, f⟫ • θ)‖ ≤ (P + 2) * s := by
    calc
      _ ≤ ‖b • θ‖ + ‖s • (f - ⟪θ, f⟫ • θ)‖ := norm_add_le _ _
      _ ≤ P / s + s * 2 := by
        simp only [norm_smul, Real.norm_eq_abs, hθ, mul_one, abs_of_pos hs0]
        gcongr
      _ ≤ P * s + s * 2 := by
        gcongr
        exact (div_le_self hP hs).trans (le_mul_of_one_le_right hP hs)
      _ = _ := by ring
  have hHθθ : |H θ θ| ≤ B := by
    have hh := H.le_opNorm₂ θ θ
    rw [hθ, mul_one, mul_one] at hh
    exact hh.trans hH
  have hHθf : |H θ (f - ⟪θ, f⟫ • θ)| ≤ 2 * B := by
    calc
      _ ≤ ‖H‖ * ‖θ‖ * ‖f - ⟪θ, f⟫ • θ‖ := H.le_opNorm₂ _ _
      _ ≤ B * 1 * 2 := by rw [hθ]; gcongr
      _ = _ := by ring
  have hHeθ : |H (e - ⟪θ, e⟫ • θ) θ| ≤ 2 * B := by
    calc
      _ ≤ ‖H‖ * ‖e - ⟪θ, e⟫ • θ‖ * ‖θ‖ := H.le_opNorm₂ _ _
      _ ≤ B * 2 * 1 := by rw [hθ]; gcongr
      _ = _ := by ring
  have hde : |d (e - ⟪θ, e⟫ • θ)| ≤ 2 * B := by
    exact (d.le_opNorm _).trans (by nlinarith [mul_le_mul hd hTe (norm_nonneg _) hB])
  have hdf : |d (f - ⟪θ, f⟫ • θ)| ≤ 2 * B := by
    exact (d.le_opNorm _).trans (by nlinarith [mul_le_mul hd hTf (norm_nonneg _) hB])
  have hwe : |dw (e - ⟪θ, e⟫ • θ)| ≤ 2 * M / s ^ 5 := by
    calc
      _ ≤ ‖dw‖ * ‖e - ⟪θ, e⟫ • θ‖ := dw.le_opNorm _
      _ ≤ (M / s ^ 5) * 2 := by gcongr
      _ = _ := by ring
  have hwf : |dw (f - ⟪θ, f⟫ • θ)| ≤ 2 * M / s ^ 5 := by
    calc
      _ ≤ ‖dw‖ * ‖f - ⟪θ, f⟫ • θ‖ := dw.le_opNorm _
      _ ≤ (M / s ^ 5) * 2 := by gcongr
      _ = _ := by ring
  have hwN : |dw ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e)| ≤ 6 * M / s ^ 5 := by
    calc
      _ ≤ ‖dw‖ * ‖(3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
          ⟪θ, e⟫ • f - ⟪θ, f⟫ • e‖ := dw.le_opNorm _
      _ ≤ (M / s ^ 5) * 6 := by gcongr
      _ = _ := by ring
  have hwA : |hw (a • θ + s • (e - ⟪θ, e⟫ • θ))
      (b • θ + s • (f - ⟪θ, f⟫ • θ))| ≤ M * (P + 2) ^ 2 / s ^ 4 := by
    calc
      _ ≤ ‖hw‖ * ‖a • θ + s • (e - ⟪θ, e⟫ • θ)‖ *
          ‖b • θ + s • (f - ⟪θ, f⟫ • θ)‖ := hw.le_opNorm₂ _ _
      _ ≤ (M / s ^ 6) * ((P + 2) * s) * ((P + 2) * s) := by gcongr
      _ = _ := by field_simp
  have h1 : |2 * C * s⁻¹ * a * b| ≤ 2 * |C| * P ^ 2 / s ^ 2 := by
    calc
      _ ≤ 2 * |C| * s⁻¹ * (P / s) * (P / s) := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (inv_pos.mpr hs0)]
        gcongr
      _ = 2 * |C| * P ^ 2 / s ^ 3 := by field_simp
      _ ≤ _ := levelRadius_decay_mono hs (by positivity) (by norm_num)
  have h2 : |s⁻¹ ^ 3 * a * b * H θ θ| ≤ B * P ^ 2 / s ^ 2 := by
    calc
      _ ≤ s⁻¹ ^ 3 * (P / s) * (P / s) * B := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < s⁻¹ ^ 3)]
        gcongr
      _ = B * P ^ 2 / s ^ 5 := by field_simp
      _ ≤ _ := levelRadius_decay_mono hs (by positivity) (by norm_num)
  have hcross (c z : ℝ) (hc : |c| ≤ P / s) (hz : |z| ≤ 2 * B) :
      |s⁻¹ ^ 2 * c * z| ≤ 2 * B * P / s ^ 2 := by
    calc
      _ ≤ s⁻¹ ^ 2 * (P / s) * (2 * B) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
        gcongr
      _ = 2 * B * P / s ^ 3 := by field_simp
      _ ≤ _ := levelRadius_decay_mono hs (by positivity) (by norm_num)
  have h7 : |s ^ 2 * hw (a • θ + s • (e - ⟪θ, e⟫ • θ))
      (b • θ + s • (f - ⟪θ, f⟫ • θ))| ≤ M * (P + 2) ^ 2 / s ^ 2 := by
    calc
      _ ≤ s ^ 2 * (M * (P + 2) ^ 2 / s ^ 4) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
        gcongr
      _ = _ := by field_simp
  have hwcross (c z : ℝ) (hc : |c| ≤ P / s) (hz : |z| ≤ 2 * M / s ^ 5) :
      |s ^ 2 * c * z| ≤ 2 * M * P / s ^ 2 := by
    calc
      _ ≤ s ^ 2 * (P / s) * (2 * M / s ^ 5) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)]
        gcongr
      _ = 2 * M * P / s ^ 4 := by field_simp
      _ ≤ _ := levelRadius_decay_mono hs (by positivity) (by norm_num)
  have h10 : |s ^ 3 * dw ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e)| ≤ 6 * M / s ^ 2 := by
    calc
      _ ≤ s ^ 3 * (6 * M / s ^ 5) := by
        rw [abs_mul, abs_of_pos (pow_pos hs0 3)]
        gcongr
      _ = _ := by field_simp
  have hadd {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
      |a + b| ≤ A + B := (abs_add_le a b).trans (add_le_add ha hb)
  have hsum := hadd
    (hadd (hadd (hadd
      (hadd (hadd (hadd
        (hadd (hadd h1 h2)
          (hcross _ _ ha hHθf)) (hcross _ _ hb hHeθ)) (hcross _ _ ha hdf))
          (hcross _ _ hb hde)) h7) (hwcross _ _ ha hwf)) (hwcross _ _ hb hwe)) h10
  exact hsum.trans_eq (by ring)

set_option maxHeartbeats 800000 in
-- The nested bilinear norm bounds need extra elaboration steps.
/-- Quantitative second-order implicit differentiation after removing the
Coulomb term and the leading angular quadrupole. -/
theorem levelRadius_implicit_hessian_estimate {U Q : E3 → ℝ} {t C B M P : ℝ}
    {ρ : E3 → ℝ} (hC : 0 < C) (hB : 0 ≤ B) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {θ : E3} (hθ : ‖θ‖ = 1)
    (hs : 1 ≤ ρ θ) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hU : ContDiffAt ℝ 2 U (ρ θ • θ))
    (dw : E3 →L[ℝ] ℝ) (hw : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hD : fderiv ℝ U (ρ θ • θ) =
      fderiv ℝ (fun y : E3 => C / ‖y‖) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 4 • fderiv ℝ (farQuadrupole Q) θ + dw)
    (hDD : fderiv ℝ (fderiv ℝ U) (ρ θ • θ) =
      fderiv ℝ (fderiv ℝ (fun y : E3 => C / ‖y‖)) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 5 • fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ + hw)
    (hd : ‖fderiv ℝ (farQuadrupole Q) θ‖ ≤ B)
    (hH : ‖fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ‖ ≤ B)
    (hdw : ‖dw‖ ≤ M / (ρ θ) ^ 5) (hhw : ‖hw‖ ≤ M / (ρ θ) ^ 6)
    (hp : ‖fderiv ℝ ρ θ‖ ≤ P / ρ θ)
    (hval : |t - C / ρ θ| ≤ (B + M) / (ρ θ) ^ 3)
    (hsmall : (B + M) / (ρ θ) ^ 2 ≤ C / 2) :
    ‖fderiv ℝ (fderiv ℝ ρ) θ - (t / C ^ 2) •
        fderiv ℝ (fderiv ℝ (fun y => Q (‖y‖⁻¹ • y))) θ‖ ≤
      (2 / C * (((B + M) / C + (B + M) / C ^ 2) * (10 * B) +
        (2 * |C| * P ^ 2 + B * P ^ 2 + 8 * B * P +
          M * (P + 2) ^ 2 + 4 * M * P + 6 * M))) * (ρ θ)⁻¹ ^ 2 := by
  have hs0 : 0 < ρ θ := lt_of_lt_of_le zero_lt_one hs
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hn : ‖ρ θ • θ‖ = ρ θ := by simp [norm_smul, abs_of_pos hs0, hθ]
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  let a := -(ρ θ) ^ 2 * fderiv ℝ U (ρ θ • θ) θ
  have hdθ : |fderiv ℝ (farQuadrupole Q) θ θ| ≤ B := by
    simpa only [hθ, mul_one, Real.norm_eq_abs] using
      ((fderiv ℝ (farQuadrupole Q) θ).le_opNorm θ).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg θ))
  have hdwθ : |dw θ| ≤ M / (ρ θ) ^ 5 := by
    simpa only [hθ, mul_one, Real.norm_eq_abs] using (dw.le_opNorm θ).trans
      (mul_le_mul_of_nonneg_right hdw (norm_nonneg θ))
  have hid : a - C = -(ρ θ)⁻¹ ^ 2 * fderiv ℝ (farQuadrupole Q) θ θ -
      (ρ θ) ^ 2 * dw θ := by
    dsimp [a]
    rw [hD, (hasFDerivAt_monopole C (smul_ne_zero hs0.ne' hθ0)).fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      real_inner_smul_left, hθθ, mul_one, hn]
    field_simp
    ring
  have had : |a - C| ≤ (B + M) * (ρ θ)⁻¹ ^ 2 := by
    rw [hid]
    calc
      _ ≤ |-(ρ θ)⁻¹ ^ 2 * fderiv ℝ (farQuadrupole Q) θ θ| +
          |(ρ θ) ^ 2 * dw θ| := abs_sub _ _
      _ ≤ (ρ θ)⁻¹ ^ 2 * B + (ρ θ) ^ 2 * (M / (ρ θ) ^ 5) := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ((ρ θ)⁻¹)),
          abs_of_nonneg (sq_nonneg (ρ θ))]
        gcongr
      _ = B / (ρ θ) ^ 2 + M / (ρ θ) ^ 3 := by field_simp
      _ ≤ B / (ρ θ) ^ 2 + M / (ρ θ) ^ 2 :=
        add_le_add le_rfl (levelRadius_decay_mono hs hM (by norm_num))
      _ = _ := by rw [inv_pow]; ring
  have ha : C / 2 ≤ a := by
    have hh := (abs_le.mp had).1
    have hh' : (B + M) * (ρ θ)⁻¹ ^ 2 ≤ C / 2 := by
      simpa only [inv_pow, ← div_eq_mul_inv] using hsmall
    linarith
  have het : |(ρ θ)⁻¹ - t / C| ≤ (B + M) / C * (ρ θ)⁻¹ ^ 2 := by
    have heq : (ρ θ)⁻¹ - t / C = -(t - C / ρ θ) / C := by field_simp; ring
    rw [heq, abs_div, abs_neg, abs_of_pos hC]
    calc
      _ ≤ ((B + M) / (ρ θ) ^ 3) / C := div_le_div_of_nonneg_right hval hC.le
      _ ≤ ((B + M) / (ρ θ) ^ 2) / C := div_le_div_of_nonneg_right
        (levelRadius_decay_mono hs (add_nonneg hB hM) (by norm_num)) hC.le
      _ = _ := by rw [inv_pow]; ring
  let L := 2 * |C| * P ^ 2 + B * P ^ 2 + 8 * B * P +
    M * (P + 2) ^ 2 + 4 * M * P + 6 * M
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hres : ‖a • fderiv ℝ (fderiv ℝ ρ) θ - (ρ θ)⁻¹ •
      fderiv ℝ (fderiv ℝ (fun y => Q (‖y‖⁻¹ • y))) θ‖ ≤ L * (ρ θ)⁻¹ ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hpe : |fderiv ℝ ρ θ e| ≤ P / ρ θ := by
      simpa only [he, mul_one, Real.norm_eq_abs] using ((fderiv ℝ ρ θ).le_opNorm e).trans
        (mul_le_mul_of_nonneg_right hp (norm_nonneg e))
    have hpf : |fderiv ℝ ρ θ f| ≤ P / ρ θ := by
      simpa only [hf, mul_one, Real.norm_eq_abs] using ((fderiv ℝ ρ θ).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right hp (norm_nonneg f))
    simp only [sub_apply, smul_apply, smul_eq_mul, Real.norm_eq_abs]
    dsimp only [a]
    rw [levelRadius_hessian_error_identity hhom hroot hQ hθ hs0 hρ hU dw hw hD hDD]
    have hb := levelRadius_hessian_residual_bound (C := C) hs hB hM hP hθ he hf
      hpe hpf (fderiv ℝ (farQuadrupole Q) θ) dw
      (fderiv ℝ (fderiv ℝ (farQuadrupole Q)) θ) hw hd hH hdw hhw
    simpa only [L, inv_pow, ← div_eq_mul_inv] using hb
  exact levelRadius_hessian_inversion_bound (F := E3 →L[ℝ] E3 →L[ℝ] ℝ)
    hC ht ht1 ha had het
    (levelRadius_angular_fderiv_two_bound hQ hB hθ hd hH) hres

private theorem levelRadius_fderiv_two_add {f g : E3 → ℝ} {x : E3}
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

set_option maxHeartbeats 1000000 in
-- Combining the implicit estimate and the far-field bounds has a large local context.
/-- The capacitary level radius has a remainder of order `t²` in value and in
its first two ambient derivatives of the zero-homogeneous extension. -/
theorem capacitary_level_radius_derivatives
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
          |levelRadiusRemainder v t ρ θ| ≤ A * t ^ 2 ∧
          ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤ A * t ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤ A * t ^ 2 := by
  obtain ⟨v, r, hr, hv, he, _, hv0, _, hQs, _, _, R, M, hR, hW, hbound⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨v', r', hr', hv', he', _, A, hA, hev⟩ :=
    capacitary_level_radius_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0, hg0, hQ0⟩ := kelvin_extension_data_eq hr' hr hv' hv he' he
  have hrem (t : ℝ) (ρ : E3 → ℝ) :
      levelRadiusRemainder v' t ρ = levelRadiusRemainder v t ρ := by
    funext y
    simp only [levelRadiusRemainder, h0, hQ0]
  simp only [hrem, h0, hg0] at hev
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) hQs
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  let W := kelvinTranslatedRemainder u v
  let f := farQuadrupole (kelvinTranslatedQuadrupole v)
  have hUeq : U = fun y => (v 0 / ‖y‖ + f y) + W y := by
    funext y
    dsimp [U, W, f, kelvinTranslatedRemainder, farQuadrupole]
    ring
  have hUc : Continuous U := hu.comp (continuous_id.add continuous_const)
  have hUpos : ∀ y, 0 < U y := fun y =>
    capacitary_pos_everywhere hK hzero hu hh hb hinf _
  have hlim : Tendsto (fun s : ℝ => (B + |M|) / s ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨S, hS, hsmallS⟩ := ((eventually_ge_atTop (max (R + 1) 1)).and
    (hlim.eventually (gt_mem_nhds (by positivity : 0 < v 0 / 2)))).exists
  have hS1 : 1 ≤ S := (le_max_right _ _).trans hS
  have hSR : R < S := by have := (le_max_left _ _).trans hS; linarith
  obtain ⟨y₀, _, hy₀⟩ := (isCompact_closedBall (0 : E3) S).exists_isMinOn
    ⟨0, mem_closedBall_self (by linarith)⟩ hUc.continuousOn
  let P := (A + 2 * B / (v 0) ^ 2) * (v 0 + B + |M|)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let L := 2 / v 0 *
    (((B + |M|) / v 0 + (B + |M|) / (v 0) ^ 2) * (10 * B) +
      (2 * |v 0| * P ^ 2 + B * P ^ 2 + 8 * B * P +
        |M| * (P + 2) ^ 2 + 4 * |M| * P + 6 * |M|))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨v, r, hr, hv, he, hv0, max A (L * (2 / v 0) ^ 2),
    hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (lt_min one_pos (hUpos y₀))] with t ht htr
  have htpos := htr.1
  have ht1 : t ≤ 1 := htr.2.le.trans (min_le_left _ _)
  have htm : t < U y₀ := htr.2.trans_le (min_le_right _ _)
  intro ρ hhom hroot
  obtain ⟨hsmooth, hbds⟩ := ht ρ hhom hroot
  refine ⟨hsmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  obtain ⟨hs, hut⟩ := hroot θ hθ
  have hn : ‖ρ θ • θ‖ = ρ θ := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hθ, mul_one]
  have hSs : S < ρ θ := by
    by_contra h
    have hm := hy₀ (show ρ θ • θ ∈ closedBall 0 S by
      simpa only [mem_closedBall, dist_zero_right, hn] using not_lt.mp h)
    change U y₀ ≤ U (ρ θ • θ) at hm
    change U (ρ θ • θ) = t at hut
    linarith
  have hsR : R < ‖ρ θ • θ‖ := by rw [hn]; exact hSR.trans hSs
  have hs1 : 1 ≤ ρ θ := hS1.trans hSs.le
  have hx0 : ρ θ • θ ≠ 0 := smul_ne_zero hs.ne' hθ0
  have hsmall : (B + |M|) / (ρ θ) ^ 2 ≤ v 0 / 2 := by
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by linarith : 0 ≤ S) hSs.le 2)).trans hsmallS.le
  obtain ⟨hWv, hWd, hWdd⟩ := hbound (ρ θ • θ) hsR.le
  rw [hn] at hWv hWd hWdd
  have hWv' : |W (ρ θ • θ)| ≤ |M| / (ρ θ) ^ 4 :=
    hWv.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
  have hWd' : ‖fderiv ℝ W (ρ θ • θ)‖ ≤ |M| / (ρ θ) ^ 5 :=
    hWd.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
  have hWdd' : ‖fderiv ℝ (fderiv ℝ W) (ρ θ • θ)‖ ≤ |M| / (ρ θ) ^ 6 :=
    hWdd.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
  have hval : |t - v 0 / ρ θ| ≤ (B + |M|) / (ρ θ) ^ 3 := by
    have hid : t - v 0 / ρ θ = f (ρ θ • θ) + W (ρ θ • θ) := by
      have hUt : U (ρ θ • θ) = t := hut
      rw [hUeq] at hUt
      dsimp only at hUt
      rw [hn] at hUt
      linarith
    have hfval := (hBb (ρ θ • θ) hx0).1
    rw [hn] at hfval
    rw [hid]
    calc
      _ ≤ |f (ρ θ • θ)| + |W (ρ θ • θ)| := abs_add_le _ _
      _ ≤ B / (ρ θ) ^ 3 + |M| / (ρ θ) ^ 3 := add_le_add hfval
        (hWv'.trans (levelRadius_decay_mono hs1 (abs_nonneg M) (by norm_num)))
      _ = _ := by ring
  have htupper : t ≤ (v 0 + B + |M|) / ρ θ := by
    have hh := (abs_le.mp hval).2
    have hh' := levelRadius_decay_mono hs1 (show 0 ≤ B + |M| by positivity)
      (by norm_num : 1 ≤ 3)
    have hsum : v 0 / ρ θ + (B + |M|) / ρ θ = (v 0 + B + |M|) / ρ θ := by ring
    rw [← hsum]
    simp only [pow_one] at hh'
    linarith
  have hinv : (ρ θ)⁻¹ ≤ 2 * (t / v 0) := by
    have h1 := (abs_le.mp hval).1
    have h2 := mul_le_mul_of_nonneg_right hsmall (inv_nonneg.mpr hs.le)
    rw [show 2 * (t / v 0) = (2 * t) / v 0 by ring, le_div_iff₀ hv0]
    simp only [div_eq_mul_inv, ← inv_pow] at h1 h2
    nlinarith only [h1, h2]
  have hρc : ContDiffAt ℝ (⊤ : ℕ∞) ρ θ :=
    hsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)
  have hρd := hρc.differentiableAt (by simp)
  obtain ⟨hvalue, hfirst⟩ := hbds θ hθ
  change |levelRadiusRemainder v t ρ θ| ≤ A * t ^ 2 at hvalue
  change ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤ A * t ^ 2 at hfirst
  have hdB : ‖fderiv ℝ f θ‖ ≤ B := by simpa [hθ] using (hBb θ hθ0).2.1
  have hddB : ‖fderiv ℝ (fderiv ℝ f) θ‖ ≤ B := by
    simpa [hθ] using (hBb θ hθ0).2.2
  have htg : ‖gradient f θ - ⟪gradient f θ, θ⟫ • θ‖ ≤ 2 * B := by
    have hg : ‖gradient f θ‖ ≤ B := by
      rw [gradient, (toDual ℝ E3).symm.norm_map]
      exact hdB
    exact (levelRadius_tangent_norm_le hθ).trans (by linarith)
  have hp : ‖fderiv ℝ ρ θ‖ ≤ P / ρ θ := by
    have heq : gradient ρ θ = gradient (levelRadiusRemainder v t ρ) θ +
        (t / (v 0) ^ 2) • (gradient f θ - ⟪gradient f θ, θ⟫ • θ) := by
      rw [levelRadiusRemainder_gradient hθ hρd]
      dsimp [f]
      module
    have hp0 : ‖fderiv ℝ ρ θ‖ ≤ A * t ^ 2 + (t / (v 0) ^ 2) * (2 * B) := by
      rw [← (toDual ℝ E3).symm.norm_map (fderiv ℝ ρ θ)]
      change ‖gradient ρ θ‖ ≤ _
      rw [heq]
      calc
        _ ≤ ‖gradient (levelRadiusRemainder v t ρ) θ‖ +
            ‖(t / (v 0) ^ 2) • (gradient f θ - ⟪gradient f θ, θ⟫ • θ)‖ :=
          norm_add_le _ _
        _ ≤ A * t ^ 2 + (t / (v 0) ^ 2) * (2 * B) := by
          rw [gradient, (toDual ℝ E3).symm.norm_map, norm_smul,
            Real.norm_of_nonneg (by positivity : 0 ≤ t / (v 0) ^ 2)]
          exact add_le_add hfirst (mul_le_mul_of_nonneg_left htg (by positivity))
    calc
      _ ≤ (A + 2 * B / (v 0) ^ 2) * t := by
        have ht2 : t ^ 2 ≤ t := by nlinarith only [htpos, ht1]
        calc
          _ ≤ A * t ^ 2 + (t / (v 0) ^ 2) * (2 * B) := hp0
          _ ≤ A * t + (t / (v 0) ^ 2) * (2 * B) :=
            add_le_add (mul_le_mul_of_nonneg_left ht2 hA) le_rfl
          _ = _ := by ring
      _ ≤ (A + 2 * B / (v 0) ^ 2) * ((v 0 + B + |M|) / ρ θ) :=
        mul_le_mul_of_nonneg_left htupper (by positivity)
      _ = _ := by dsimp [P]; ring
  have hWc : ContDiffAt ℝ 2 W (ρ θ • θ) :=
    (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hsR)).of_le
      (by simp)
  have hmc : ContDiffAt ℝ 2 (fun y : E3 => v 0 / ‖y‖) (ρ θ • θ) :=
    (contDiffAt_monopole (v 0) hx0).of_le (by simp)
  have hfc : ContDiffAt ℝ 2 f (ρ θ • θ) :=
    (contDiffAt_farQuadrupole (translated_quadrupole_contDiff v) hx0).of_le (by simp)
  have hUcs : ContDiffAt ℝ 2 U (ρ θ • θ) := by
    rw [hUeq]
    exact (hmc.add hfc).add hWc
  have hD : fderiv ℝ U (ρ θ • θ) =
      fderiv ℝ (fun y : E3 => v 0 / ‖y‖) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 4 • fderiv ℝ f θ + fderiv ℝ W (ρ θ • θ) := by
    rw [hUeq]
    calc
      _ = fderiv ℝ (fun y : E3 => v 0 / ‖y‖) (ρ θ • θ) +
          fderiv ℝ f (ρ θ • θ) + fderiv ℝ W (ρ θ • θ) :=
        (((hmc.differentiableAt (by norm_num)).hasFDerivAt.add
          (hfc.differentiableAt (by norm_num)).hasFDerivAt).add
            (hWc.differentiableAt (by norm_num)).hasFDerivAt).fderiv
      _ = _ := by rw [fderiv_farQuadrupole_smul hQs hs θ, inv_pow]
  have hDD : fderiv ℝ (fderiv ℝ U) (ρ θ • θ) =
      fderiv ℝ (fderiv ℝ (fun y : E3 => v 0 / ‖y‖)) (ρ θ • θ) +
        (ρ θ)⁻¹ ^ 5 • fderiv ℝ (fderiv ℝ f) θ + fderiv ℝ (fderiv ℝ W) (ρ θ • θ) := by
    rw [hUeq, levelRadius_fderiv_two_add (hmc.add hfc) hWc,
      levelRadius_fderiv_two_add hmc hfc, fderiv_two_farQuadrupole_smul hQs hs θ, inv_pow]
  have hest := levelRadius_implicit_hessian_estimate hv0 hB.le (abs_nonneg M) hP
    htpos.le ht1 hhom (fun θ hθ => (hroot θ hθ).2) (translated_quadrupole_contDiff v)
    hθ hs1 (hρc.of_le (by simp)) hUcs (fderiv ℝ W (ρ θ • θ))
    (fderiv ℝ (fderiv ℝ W) (ρ θ • θ)) hD hDD hdB hddB hWd' hWdd' hp hval hsmall
  have hsecond : ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤
      (L * (2 / v 0) ^ 2) * t ^ 2 := by
    rw [levelRadiusRemainder_fderiv_two hθ0 (hρc.of_le (by simp))]
    calc
      _ ≤ L * (ρ θ)⁻¹ ^ 2 := hest
      _ ≤ L * (2 * (t / v 0)) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hinv 2) hL
      _ = _ := by ring
  have hA' := mul_le_mul_of_nonneg_right (le_max_left A (L * (2 / v 0) ^ 2))
    (sq_nonneg t)
  have hL' := mul_le_mul_of_nonneg_right (le_max_right A (L * (2 / v 0) ^ 2))
    (sq_nonneg t)
  exact ⟨hvalue.trans hA', hfirst.trans hA', hsecond.trans hL'⟩

end LiquidDrop.CapacitaryK
