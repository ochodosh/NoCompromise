import NoCompromise.CapacitaryK.LevelRadiusSecondDerivative
import NoCompromise.CapacitaryK.LevelGradDerivatives
import NoCompromise.CapacitaryK.CapacitaryLevelRadius

/-!
# Angular derivatives of the capacitary area density

The density is extended using radial normalization. Its geometric representation
separates the squared-radius expansion from the smaller gradient correction.

`capacitary_level_area_first_derivative` proves the value and first derivative
bounds. The squared-radius Hessian cancellation and arbitrary-order spatial decay
of the translated harmonic error are also established below. Second angular
derivative bounds for the full area density and gradient length are not asserted.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The area-density error, with the angular argument radially normalized. -/
def levelAreaRemainder (u v : E3 → ℝ) (t : ℝ) (ρ : E3 → ℝ) (y : E3) : ℝ :=
  ρ y ^ 2 * gradNorm u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) /
      |⟪gradient u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0), ‖y‖⁻¹ • y⟫| -
    ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0)

/-- The implicit density agrees with the radial-graph area factor. Positivity
of the radius and the level identity on every unit direction are explicit. -/
theorem levelAreaRemainder_eq_areaFactor {u v ρ : E3 → ℝ} {t : ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 →
      u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t)
    {θ : E3} (hθ : ‖θ‖ = 1) (hpos : 0 < ρ θ)
    (hρ : DifferentiableAt ℝ ρ θ)
    (hu : DifferentiableAt ℝ (fun y => u (y + (v 0)⁻¹ • gradient v 0)) (ρ θ • θ))
    (hder : ⟪gradient u (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ ≠ 0) :
    ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
      ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0) =
      levelAreaRemainder u v t ρ θ := by
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  have hg (y : E3) : gradient U y = gradient u (y + (v 0)⁻¹ • gradient v 0) := by
    simp only [U, gradient, fderiv_comp_add_right]
  have hd : ⟪gradient U (ρ θ • θ), θ⟫ ≠ 0 := by rwa [hg]
  have hgr := levelRadius_gradient (U := U) hhom hroot hθ hρ hu hd
  rw [radial_graph_jacobian_of_implicit hθ hpos hd hgr, hg]
  simp only [levelAreaRemainder, hθ, inv_one, one_smul, gradNorm]

/-- The gradient of the zero-homogeneous level radius is tangential at unit points. -/
theorem levelArea_radius_gradient_tangent {U ρ : E3 → ℝ} {t : ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    {θ : E3} (hθ : ‖θ‖ = 1) (hρ : DifferentiableAt ℝ ρ θ)
    (hU : DifferentiableAt ℝ U (ρ θ • θ))
    (hder : ⟪gradient U (ρ θ • θ), θ⟫ ≠ 0) :
    ⟪gradient ρ θ, θ⟫ = 0 := by
  rw [levelRadius_gradient hhom hroot hθ hρ hU hder]
  simp [inner_sub_left, real_inner_smul_left, hθ]

/-- The coefficient left after differentiating the area correction is small.
This is the cancellation of the two leading derivatives of the squared radius. -/
theorem levelArea_sqrt_coefficient_bound {s n : ℝ} (hs : 0 < s) (hn : 0 ≤ n) :
    |Real.sqrt (s ^ 2 + n ^ 2) + s ^ 2 / Real.sqrt (s ^ 2 + n ^ 2) - 2 * s| ≤ n := by
  set a := Real.sqrt (s ^ 2 + n ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = s ^ 2 + n ^ 2 := Real.sq_sqrt (by positivity)
  have hsa : s ≤ a := by nlinarith
  have han : a - s ≤ n := by nlinarith
  have he : a + s ^ 2 / a - 2 * s = (a - s) ^ 2 / a := by field_simp; ring
  rw [he, abs_of_nonneg (by positivity), div_le_iff₀ ha]
  calc
    (a - s) ^ 2 ≤ n * (a - s) := by nlinarith
    _ ≤ n * a := by gcongr; linarith

/-- Differentiating the area correction costs only one derivative of the
gradient vector. This estimate uses no lower bound on the positive radius. -/
theorem levelArea_correction_fderiv_bound {s : E3 → ℝ} {V : E3 → E3} {x : E3}
    (hs : DifferentiableAt ℝ s x) (hV : DifferentiableAt ℝ V x) (hpos : 0 < s x) :
    DifferentiableAt ℝ
        (fun y => s y * Real.sqrt (s y ^ 2 + ‖V y‖ ^ 2) - s y ^ 2) x ∧
      ‖fderiv ℝ (fun y => s y * Real.sqrt (s y ^ 2 + ‖V y‖ ^ 2) - s y ^ 2) x‖ ≤
        ‖V x‖ * (‖fderiv ℝ s x‖ + ‖fderiv ℝ V x‖) := by
  have hp : 0 < s x ^ 2 + ‖V x‖ ^ 2 := by positivity
  have hroot := ((hs.hasFDerivAt.pow 2).add hV.hasFDerivAt.norm_sq).sqrt hp.ne'
  have hd := (hs.hasFDerivAt.mul hroot).sub (hs.hasFDerivAt.pow 2)
  change HasFDerivAt
    (fun y => s y * Real.sqrt (s y ^ 2 + ‖V y‖ ^ 2) - s y ^ 2) _ x at hd
  refine ⟨hd.differentiableAt, ?_⟩
  set a := Real.sqrt (s x ^ 2 + ‖V x‖ ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 hp
  have ha2 : a ^ 2 = s x ^ 2 + ‖V x‖ ^ 2 := Real.sq_sqrt hp.le
  have hsa : s x ≤ a := by nlinarith
  have hratio : |s x / a| ≤ 1 := by
    rw [abs_of_pos (div_pos hpos ha), div_le_one ha]
    exact hsa
  have hcoeff := levelArea_sqrt_coefficient_bound hpos (norm_nonneg (V x))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  have hde : fderiv ℝ
      (fun y => s y * Real.sqrt (s y ^ 2 + ‖V y‖ ^ 2) - s y ^ 2) x e =
      (a + s x ^ 2 / a - 2 * s x) * fderiv ℝ s x e +
        (s x / a) * ⟪V x, fderiv ℝ V x e⟫ := by
    rw [hd.fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, Pi.add_apply]
    dsimp only [a]
    ring
  rw [hde, Real.norm_eq_abs]
  have hds : |fderiv ℝ s x e| ≤ ‖fderiv ℝ s x‖ := by
    simpa [he] using (fderiv ℝ s x).le_opNorm e
  have hdV : ‖fderiv ℝ V x e‖ ≤ ‖fderiv ℝ V x‖ := by
    simpa [he] using (fderiv ℝ V x).le_opNorm e
  calc
    _ ≤ |a + s x ^ 2 / a - 2 * s x| * |fderiv ℝ s x e| +
        |s x / a| * |⟪V x, fderiv ℝ V x e⟫| := by
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
    _ ≤ ‖V x‖ * ‖fderiv ℝ s x‖ + 1 * (‖V x‖ * ‖fderiv ℝ V x‖) :=
      add_le_add (mul_le_mul hcoeff hds (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hratio ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left hdV (norm_nonneg _))) (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- The first derivative of the squared-radius expansion. The error in the
radius derivative is multiplied by the radius, losing one power of `t`. -/
theorem levelArea_radius_square_fderiv_bound {s q : E3 → ℝ} {x : E3} {C t A B L : ℝ}
    (hC : 0 < C) (ht : 0 < t) (ht1 : t ≤ 1) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hL : 0 ≤ L) (hs : DifferentiableAt ℝ s x) (hq : DifferentiableAt ℝ q x)
    (hpos : 0 < s x) (hcoarse : |s x - C / t| ≤ L) (hDq : ‖fderiv ℝ q x‖ ≤ B)
    (hE : ‖fderiv ℝ (fun y => s y - (C / t + t * q y / C ^ 2)) x‖ ≤ A * t ^ 2) :
    ‖fderiv ℝ (fun y => s y ^ 2 - (C ^ 2 / t ^ 2 + 2 * q y / C)) x‖ ≤
      (2 * A * (C + L) + 2 * L * B / C ^ 2) * t := by
  let E : E3 → ℝ := fun y => s y - (C / t + t * q y / C ^ 2)
  have hEd : HasFDerivAt E (fderiv ℝ s x - (t / C ^ 2) • fderiv ℝ q x) x := by
    have he : E = fun y => s y - (C / t + (t / C ^ 2) * q y) := by
      funext y; dsimp [E]; ring
    rw [he]
    exact hs.hasFDerivAt.sub
      ((hq.hasFDerivAt.const_mul (t / C ^ 2)).const_add (C / t))
  have hsq : HasFDerivAt (fun y => s y ^ 2 - (C ^ 2 / t ^ 2 + 2 * q y / C))
      ((2 * s x) • fderiv ℝ s x - (2 / C) • fderiv ℝ q x) x := by
    have he : (fun y => s y ^ 2 - (C ^ 2 / t ^ 2 + 2 * q y / C)) =
        fun y => s y ^ 2 - (C ^ 2 / t ^ 2 + (2 / C) * q y) := by
      funext y; ring
    rw [he]
    simpa using! (hs.hasFDerivAt.pow 2).sub
      ((hq.hasFDerivAt.const_mul (2 / C)).const_add (C ^ 2 / t ^ 2))
  have hid : fderiv ℝ (fun y => s y ^ 2 - (C ^ 2 / t ^ 2 + 2 * q y / C)) x =
      (2 * s x) • fderiv ℝ E x +
        (2 * t / C ^ 2 * (s x - C / t)) • fderiv ℝ q x := by
    rw [hsq.fderiv, hEd.fderiv]
    ext e
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    field_simp
    ring
  have hsupper : s x ≤ C / t + L := by have := (abs_le.mp hcoarse).2; linarith
  have hterm : 2 * s x * (A * t ^ 2) ≤ 2 * A * (C + L) * t := by
    calc
      _ ≤ 2 * (C / t + L) * (A * t ^ 2) := by gcongr
      _ = 2 * A * C * t + 2 * A * L * t ^ 2 := by field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (by nlinarith : t ^ 2 ≤ t)
          (by positivity : 0 ≤ 2 * A * L)
        nlinarith
  rw [hid]
  calc
    _ ≤ ‖(2 * s x) • fderiv ℝ E x‖ +
        ‖(2 * t / C ^ 2 * (s x - C / t)) • fderiv ℝ q x‖ := norm_add_le _ _
    _ = 2 * s x * ‖fderiv ℝ E x‖ +
        (2 * t / C ^ 2 * |s x - C / t|) * ‖fderiv ℝ q x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2 * s x), abs_mul,
        abs_of_pos (by positivity : 0 < 2 * t / C ^ 2)]
    _ ≤ 2 * s x * (A * t ^ 2) + (2 * t / C ^ 2 * L) * B := by
      gcongr
    _ ≤ 2 * A * (C + L) * t + (2 * t / C ^ 2 * L) * B := by gcongr
    _ = _ := by ring

/-- Off the origin the density can be written using the gradient at the
normalized direction. This identity also controls its ambient derivatives. -/
theorem levelAreaRemainder_eq_normalized_areaFactor {u v ρ : E3 → ℝ} {t : ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 →
      0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t)
    (hρ : ∀ θ : E3, ‖θ‖ = 1 → DifferentiableAt ℝ ρ θ)
    (hu : ∀ θ : E3, ‖θ‖ = 1 →
      DifferentiableAt ℝ (fun y => u (y + (v 0)⁻¹ • gradient v 0)) (ρ θ • θ))
    (hder : ∀ θ : E3, ‖θ‖ = 1 →
      ⟪gradient u (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ ≠ 0)
    {y : E3} (hy : y ≠ 0) :
    levelAreaRemainder u v t ρ y =
      ρ y * Real.sqrt (ρ y ^ 2 + ‖gradient ρ (‖y‖⁻¹ • y)‖ ^ 2) -
        ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0) := by
  have hn : ‖‖y‖⁻¹ • y‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy]
  have hlink := levelAreaRemainder_eq_areaFactor hhom (fun θ hθ => (hroot θ hθ).2)
    hn (hroot _ hn).1 (hρ _ hn) (hu _ hn) (hder _ hn)
  have htan := levelArea_radius_gradient_tangent
    (U := fun x => u (x + (v 0)⁻¹ • gradient v 0)) hhom
    (fun θ hθ => (hroot θ hθ).2) hn (hρ _ hn) (hu _ hn)
    (by simpa only [gradient, fderiv_comp_add_right] using hder _ hn)
  simp only [htan, zero_smul, sub_zero, levelAreaRemainder, hn, inv_one, one_smul] at hlink
  simpa only [levelAreaRemainder, hhom y hy] using hlink.symm

/-- The first derivative of the area remainder is controlled by the derivative
of the squared-radius remainder and the first two derivatives of the radius. -/
theorem levelAreaRemainder_fderiv_bound {u v ρ : E3 → ℝ} {t : ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 →
      0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t)
    (hρ : ∀ θ : E3, ‖θ‖ = 1 → ContDiffAt ℝ 2 ρ θ)
    (hu : ∀ θ : E3, ‖θ‖ = 1 →
      DifferentiableAt ℝ (fun y => u (y + (v 0)⁻¹ • gradient v 0)) (ρ θ • θ))
    (hder : ∀ θ : E3, ‖θ‖ = 1 →
      ⟪gradient u (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ ≠ 0)
    {θ : E3} (hθ : ‖θ‖ = 1) :
    ‖fderiv ℝ (levelAreaRemainder u v t ρ) θ‖ ≤
      ‖fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0)) θ‖ +
      ‖fderiv ℝ ρ θ‖ * (‖fderiv ℝ ρ θ‖ + 2 * ‖fderiv ℝ (fderiv ℝ ρ) θ‖) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  let n : E3 → E3 := fun y => ‖y‖⁻¹ • y
  let V : E3 → E3 := fun y => gradient ρ (n y)
  let S : E3 → ℝ := fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
    2 * kelvinTranslatedQuadrupole v (n y) / v 0)
  let F : E3 → ℝ := fun y => ρ y * Real.sqrt (ρ y ^ 2 + ‖V y‖ ^ 2) - ρ y ^ 2
  have hn : n θ = θ := by simp [n, hθ]
  have hnd : DifferentiableAt ℝ n θ :=
    (levelRadius_normalize_contDiffAt hθ0).differentiableAt (by simp)
  have hρd := (hρ θ hθ).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (gradient ρ) (n θ) := by
    rw [hn]
    exact differentiableAt_gradient_of_contDiffAt (hρ θ hθ)
  have hVd : DifferentiableAt ℝ V θ := hgd.comp θ hnd
  have hDn : ‖fderiv ℝ n θ‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    intro e he
    rw [levelRadius_normalize_fderiv hθ]
    simpa only [real_inner_comm θ e, he, mul_one] using
      (levelRadius_tangent_norm_le (w := e) hθ)
  have hDV : ‖fderiv ℝ V θ‖ ≤ 2 * ‖fderiv ℝ (fderiv ℝ ρ) θ‖ := by
    rw [show V = (gradient ρ) ∘ n from rfl, fderiv_comp θ hgd hnd, hn]
    calc
      _ ≤ ‖fderiv ℝ (gradient ρ) θ‖ * ‖fderiv ℝ n θ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ ρ) θ‖ * 2 :=
        mul_le_mul (levelGrad_norm_fderiv_gradient_le ρ θ) hDn (norm_nonneg _)
          (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) θ))
      _ = _ := mul_comm _ _
  have hV : ‖V θ‖ = ‖fderiv ℝ ρ θ‖ := by
    dsimp only [V]
    rw [hn, gradient, (toDual ℝ E3).symm.norm_map]
  obtain ⟨hFd, hFb⟩ := levelArea_correction_fderiv_bound hρd hVd (hroot θ hθ).1
  have hSd : DifferentiableAt ℝ S θ := by
    have heS : S = fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        (2 / v 0) * kelvinTranslatedQuadrupole v (n y)) := by
      funext y; dsimp [S]; ring
    rw [heS]
    exact (hρd.pow 2).sub (differentiableAt_const _ |>.add
      (((translated_quadrupole_contDiff v).differentiable (by simp)).differentiableAt.comp
        θ hnd |>.const_mul (2 / v 0)))
  have heq : levelAreaRemainder u v t ρ =ᶠ[𝓝 θ] fun y => S y + F y := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    rw [levelAreaRemainder_eq_normalized_areaFactor hhom hroot
      (fun θ hθ => (hρ θ hθ).differentiableAt (by norm_num)) hu hder hy]
    dsimp [S, F, V, n]
    ring
  rw [heq.fderiv_eq, fderiv_fun_add hSd hFd]
  calc
    _ ≤ ‖fderiv ℝ S θ‖ + ‖fderiv ℝ F θ‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ S θ‖ + ‖V θ‖ * (‖fderiv ℝ ρ θ‖ + ‖fderiv ℝ V θ‖) :=
      add_le_add le_rfl hFb
    _ ≤ _ := by rw [hV]; gcongr

/-- Uniform bounds for the first two radius derivatives, extracted from the
corresponding remainder estimates. -/
theorem levelArea_radius_derivative_bounds {v ρ : E3 → ℝ} {t A B : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {θ : E3} (hθ : ‖θ‖ = 1) (hρ : ContDiffAt ℝ 2 ρ θ)
    (hq : ‖fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B)
    (hqq : ‖fderiv ℝ (fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v))) θ‖ ≤ B)
    (hE : ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤ A * t ^ 2)
    (hEE : ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤ A * t ^ 2) :
    ‖fderiv ℝ ρ θ‖ ≤ (A + 10 * B / (v 0) ^ 2) * t ∧
      ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ (A + 10 * B / (v 0) ^ 2) * t := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hpow : A * t ^ 2 ≤ A * t :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA
  have hcoeff : 0 ≤ t / (v 0) ^ 2 := by positivity
  have hRg : ‖gradient (levelRadiusRemainder v t ρ) θ‖ ≤ A * t ^ 2 := by
    rwa [gradient, (toDual ℝ E3).symm.norm_map]
  rw [levelRadiusRemainder_gradient hθ (hρ.differentiableAt (by norm_num))] at hRg
  have hH : ‖gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
      ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ‖ ≤ 2 * B := by
    apply (levelRadius_tangent_norm_le hθ).trans
    rw [gradient, (toDual ℝ E3).symm.norm_map]
    gcongr
  have hfirst : ‖gradient ρ θ‖ ≤ A * t ^ 2 + (t / (v 0) ^ 2) * (2 * B) := by
    calc
      _ ≤ ‖gradient ρ θ - (t / (v 0) ^ 2) •
          (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
            ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ)‖ +
          ‖(t / (v 0) ^ 2) •
          (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
            ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ)‖ := by
        simpa only [add_comm] using norm_le_norm_add_norm_sub' (gradient ρ θ)
          ((t / (v 0) ^ 2) •
            (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
              ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ))
      _ ≤ _ := by
        rw [norm_smul, Real.norm_of_nonneg hcoeff]
        gcongr
  have hsecond := levelRadius_angular_fderiv_two_bound
    (translated_quadrupole_contDiff v) hB hθ hq hqq
  rw [levelRadiusRemainder_fderiv_two hθ0 hρ] at hEE
  have hsecond' : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤
      A * t ^ 2 + (t / (v 0) ^ 2) * (10 * B) := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ ρ) θ - (t / (v 0) ^ 2) •
          fderiv ℝ (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ‖ +
          ‖(t / (v 0) ^ 2) •
          fderiv ℝ (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ‖ := by
        simpa only [add_comm] using norm_le_norm_add_norm_sub' (fderiv ℝ (fderiv ℝ ρ) θ)
          ((t / (v 0) ^ 2) •
            fderiv ℝ (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ)
      _ ≤ _ := by
        apply add_le_add hEE
        apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
        intro e he
        apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
        intro f hf
        simp only [smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg hcoeff]
        apply mul_le_mul_of_nonneg_left _ hcoeff
        have hb := ((fderiv ℝ (fderiv ℝ
          (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ).le_opNorm e)
        have hb' := ((fderiv ℝ (fderiv ℝ
          (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ e).le_opNorm f)
        simp only [he, hf, mul_one] at hb hb'
        exact hb'.trans (hb.trans hsecond)
  constructor
  · rw [← (toDual ℝ E3).symm.norm_map (fderiv ℝ ρ θ)]
    exact hfirst.trans (by
      change A * t ^ 2 + (t / (v 0) ^ 2) * (2 * B) ≤ _
      calc
        _ ≤ A * t + (t / (v 0) ^ 2) * (10 * B) := by gcongr; linarith
        _ = _ := by ring)
  · exact hsecond'.trans (calc
      _ ≤ A * t + (t / (v 0) ^ 2) * (10 * B) := add_le_add hpow le_rfl
      _ = _ := by ring)

/-- `eq:K-dA`: the area-density remainder and its first angular derivative
are uniformly `O(t)` on the small capacitary levels. -/
theorem capacitary_level_area_first_derivative
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
          ‖fderiv ℝ (levelAreaRemainder u v t ρ) θ‖ ≤ A * t := by
  obtain ⟨v, r, hr, hv, he, hv0, Ar, hAr, hevR⟩ :=
    capacitary_level_radius_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨va, ra, hra, hva, hea, _, Aa, hAa, hevA⟩ :=
    capacitary_level_area_density_expansion hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0a, hga, hQa⟩ := kelvin_extension_data_eq hra hr hva hv hea he
  simp only [h0a, hga, hQa] at hevA
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v)
  let L := Ar + B / (v 0) ^ 2
  let P := Ar + 10 * B / (v 0) ^ 2
  let D := 2 * Ar * (v 0 + L) + 2 * L * (2 * B) / (v 0) ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨v, r, hr, hv, he, hv0, max Aa (D + 3 * P ^ 2),
    hAa.trans (le_max_left _ _), ?_⟩
  have huSmooth := capacitary_potential_contDiffOn hK hu hh
  filter_upwards [hevR, hevA, Ioo_mem_nhdsGT one_pos] with t htR htA htr
  have ht : 0 < t := htr.1
  have ht1 : t ≤ 1 := htr.2.le
  intro ρ hhom hroot
  obtain ⟨hρSmooth, hρb⟩ := htR ρ hhom hroot
  have hρC2 (θ : E3) (hθ : ‖θ‖ = 1) : ContDiffAt ℝ 2 ρ θ := by
    have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
    exact (hρSmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  have hU (θ : E3) (hθ : ‖θ‖ = 1) :
      DifferentiableAt ℝ (fun y => u (y + (v 0)⁻¹ • gradient v 0)) (ρ θ • θ) := by
    have hx : ρ θ • θ + (v 0)⁻¹ • gradient v 0 ∈ Kᶜ := by
      intro hxK
      have := hb _ hxK
      rw [(hroot θ hθ).2] at this
      exact htr.2.ne this
    exact ((huSmooth.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx)).differentiableAt
      (by simp)).comp (ρ θ • θ)
        (differentiableAt_id.add_const ((v 0)⁻¹ • gradient v 0))
  have hder (θ : E3) (hθ : ‖θ‖ = 1) :
      ⟪gradient u (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ ≠ 0 :=
    (htA θ hθ _ (hroot θ hθ).1 (hroot θ hθ).2).1.ne
  refine ⟨hρSmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  obtain ⟨hE, hED, hEDD⟩ := hρb θ hθ
  have hval : |levelAreaRemainder u v t ρ θ| ≤ Aa * t := by
    simpa only [levelAreaRemainder, hθ, inv_one, one_smul, gradNorm] using
      (htA θ hθ _ (hroot θ hθ).1 (hroot θ hθ).2).2
  refine ⟨hval.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le), ?_⟩
  have hq : |kelvinTranslatedQuadrupole v θ| ≤ B := by
    simpa only [farQuadrupole, hθ, one_pow, div_one] using (hBb θ hθ0).1
  have hqD : ‖fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B := by
    simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.1
  have hqDD : ‖fderiv ℝ (fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v))) θ‖ ≤
      B := by simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.2
  obtain ⟨hρD, hρDD⟩ := levelArea_radius_derivative_bounds ht.le ht1 hAr hB.le hθ
    (hρC2 θ hθ) hqD hqDD hED hEDD
  have hcoarse : |ρ θ - v 0 / t| ≤ L := by
    have hterm : |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| ≤ B / (v 0) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg (v 0))]
      exact div_le_div_of_nonneg_right
        ((mul_le_mul ht1 hq (abs_nonneg _) zero_le_one).trans_eq (one_mul B))
        (sq_nonneg _)
    have hE' : |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤
        Ar * t ^ 2 := by simpa only [levelRadiusRemainder, hθ, inv_one, one_smul] using hE
    calc
      _ = |(ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)) +
          t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ Ar * t ^ 2 + B / (v 0) ^ 2 := add_le_add hE' hterm
      _ ≤ L := by dsimp [L]; nlinarith [pow_le_one₀ ht.le ht1 (n := 2)]
  have hqAngular := levelRadius_angular_gradient (translated_quadrupole_contDiff v)
    (kelvinTranslatedQuadrupole_smul v) hθ
  have hqAngularD : ‖fderiv ℝ
      (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ‖ ≤ 2 * B := by
    rw [← (toDual ℝ E3).symm.norm_map]
    change ‖gradient (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ‖ ≤ _
    rw [hqAngular.2]
    apply (levelRadius_tangent_norm_le hθ).trans
    rw [gradient, (toDual ℝ E3).symm.norm_map]
    gcongr
  have hsq := levelArea_radius_square_fderiv_bound hv0 ht ht1 hAr
    (by positivity : 0 ≤ 2 * B) hL ((hρC2 θ hθ).differentiableAt (by norm_num))
    hqAngular.1 (hroot θ hθ).1 hcoarse hqAngularD hED
  have hgeom := levelAreaRemainder_fderiv_bound hhom hroot hρC2 hU hder hθ
  have hsmall : (P * t) * (P * t + 2 * (P * t)) ≤ 3 * P ^ 2 * t := by
    have := mul_le_mul_of_nonneg_left (by nlinarith : t ^ 2 ≤ t)
      (by positivity : 0 ≤ 3 * P ^ 2)
    nlinarith
  calc
    _ ≤ D * t + (P * t) * (P * t + 2 * (P * t)) :=
      hgeom.trans (add_le_add hsq (by gcongr))
    _ ≤ (D + 3 * P ^ 2) * t := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le

/-- Exterior harmonic decay gains one inverse-radius power per derivative.
The order is arbitrary, so in particular this supplies the third derivative
needed when differentiating the level gradient length twice. -/
theorem levelArea_harmonic_exterior_iterated_decay (k : ℕ) {W : E3 → ℝ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hΔ : ∀ x, R < ‖x‖ → laplacianN W x = 0)
    (hb : ∀ x, R ≤ ‖x‖ → |W x| ≤ M / ‖x‖ ^ 4) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x : E3, 2 * R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ k W x‖ ≤ M' / ‖x‖ ^ (k + 4) := by
  obtain ⟨c, hc, hbound⟩ := harmonic_scaled_iteratedFDeriv_bound k
  refine ⟨16 * 2 ^ k * c * M, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hhalf : R ≤ ‖x‖ / 2 := by linarith
  have hball : ∀ y ∈ ball x (‖x‖ / 2), ‖x‖ / 2 < ‖y‖ := by
    intro y hy
    have ht := norm_sub_norm_le x y
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
    linarith
  have hsub : ball x (‖x‖ / 2) ⊆ {y | R < ‖y‖} :=
    fun y hy => hhalf.trans_lt (hball y hy)
  have hlocal : ∀ y ∈ ball x (‖x‖ / 2), |W y| ≤ 16 * M / ‖x‖ ^ 4 := by
    intro y hy
    have hny : ‖x‖ / 2 ≤ ‖y‖ := (hball y hy).le
    calc
      _ ≤ M / ‖y‖ ^ 4 := hb y (hhalf.trans hny)
      _ ≤ M / (‖x‖ / 2) ^ 4 := div_le_div_of_nonneg_left hM (by positivity)
        (pow_le_pow_left₀ (by positivity) hny 4)
      _ = _ := by ring
  have hd := hbound W x (‖x‖ / 2) (16 * M / ‖x‖ ^ 4) (half_pos hxpos)
    (hs.mono hsub) (fun y hy => hΔ y (hsub hy)) hlocal
  exact hd.trans_eq (by
    rw [div_pow, pow_add]
    field_simp)

/-- The order-three exterior harmonic estimate, with decay order seven. -/
theorem levelArea_harmonic_exterior_third_derivative {W : E3 → ℝ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hΔ : ∀ x, R < ‖x‖ → laplacianN W x = 0)
    (hb : ∀ x, R ≤ ‖x‖ → |W x| ≤ M / ‖x‖ ^ 4) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x : E3, 2 * R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ 3 W x‖ ≤ M' / ‖x‖ ^ 7 :=
  levelArea_harmonic_exterior_iterated_decay 3 hR hM hs hΔ hb

/-- The second derivative of a scalar square, evaluated on two vectors. -/
theorem levelArea_fderiv_two_square {s : E3 → ℝ} {x : E3}
    (hs : ContDiffAt ℝ 2 s x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => s y ^ 2)) x e f =
      2 * s x * fderiv ℝ (fderiv ℝ s) x e f +
        2 * fderiv ℝ s x e * fderiv ℝ s x f := by
  have hsd := hs.differentiableAt (by norm_num)
  have hD := (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDD := ((hs.pow 2).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => s z ^ 2) y f) =ᶠ[𝓝 x]
      (fun y => 2 * s y * fderiv ℝ s y f) := by
    filter_upwards [hs.eventually (by norm_num)] with y hy
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.pow 2).fderiv]
    simp
  have hleft := hDD.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hsd.hasFDerivAt.const_mul 2).mul
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const f x))
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hid

/-- Subtracting a constant and a scalar multiple commutes with the second derivative. -/
theorem levelArea_fderiv_two_sub_model {s q : E3 → ℝ} {x : E3} (a b : ℝ)
    (hs : ContDiffAt ℝ 2 s x) (hq : ContDiffAt ℝ 2 q x) :
    fderiv ℝ (fderiv ℝ (fun y => s y - (a + b * q y))) x =
      fderiv ℝ (fderiv ℝ s) x - b • fderiv ℝ (fderiv ℝ q) x := by
  have heq : fderiv ℝ (fun y => s y - (a + b * q y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ s y - b • fderiv ℝ q y) := by
    filter_upwards [hs.eventually (by norm_num), hq.eventually (by norm_num)] with y hy hz
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.sub
      (((hz.differentiableAt (by norm_num)).hasFDerivAt.const_mul b).const_add a)).fderiv
  rw [heq.fderiv_eq]
  exact (((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt
    one_ne_zero).hasFDerivAt.sub
      (((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero).hasFDerivAt.const_smul b)).fderiv

/-- The exact second derivative cancellation for the squared-radius remainder.
Only the second radius derivative is used; the remaining area correction is separate. -/
theorem levelArea_radius_square_fderiv_two {v ρ : E3 → ℝ} {t : ℝ}
    (hC : v 0 ≠ 0) (ht : t ≠ 0) {x : E3} (hx : x ≠ 0)
    (hρ : ContDiffAt ℝ 2 ρ x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) x e f =
      2 * ρ x * fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x e f +
        2 * fderiv ℝ ρ x e * fderiv ℝ ρ x f +
        (2 * t / (v 0) ^ 2 * (ρ x - v 0 / t)) *
          fderiv ℝ (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x e f := by
  have hq : ContDiffAt ℝ 2 (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) x :=
    ((translated_quadrupole_contDiff v).contDiffAt.comp x
      (levelRadius_normalize_contDiffAt hx)).of_le (by simp)
  have he : (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0)) =
      fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
        (2 / v 0) * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) := by
    funext y; ring
  rw [he, levelArea_fderiv_two_sub_model _ _ (hρ.pow 2) hq,
    levelRadiusRemainder_fderiv_two hx hρ]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [levelArea_fderiv_two_square hρ]
  field_simp
  ring

/-- The translated error is smooth and harmonic outside the translated obstacle. -/
theorem levelArea_translated_remainder_smooth_harmonic
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) {u v : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hQ : ∀ x : E3, laplacianN (kelvinTranslatedQuadrupole v) x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v)
      {x | R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖} ∧
    (∀ x, R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖ →
      laplacianN (kelvinTranslatedRemainder u v) x = 0) := by
  have hmodel (x : E3) : v 0 / ‖x‖ + kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 =
      kelvinTransform (fun y => v 0 + kelvinTranslatedQuadrupole v y) x := by
    simp only [kelvinTransform, kelvinInversion, kelvinTranslatedQuadrupole_smul,
      div_eq_mul_inv, inv_pow]
    ring
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
    rw [← hmodel]
    simp only [kelvinTranslatedRemainder, z, add_comm, sub_sub]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) U := by
    rw [he]
    exact htu.sub hsm
  refine ⟨hs, ?_⟩
  apply kelvin_laplacianN_eq_zero_of_distributional hU hs.continuousOn
  rw [he]
  simpa only [sub_self] using hhu.sub hhm

/-- Every fixed spatial derivative of the translated capacitary error has the
expected decay. At order three the estimate is `O(|x|⁻⁷)`. -/
theorem capacitary_translated_remainder_iterated_derivative (k : ℕ)
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R < ‖x‖} ∧
        ∀ x : E3, R ≤ ‖x‖ →
          ‖iteratedFDeriv ℝ k (kelvinTranslatedRemainder u v) x‖ ≤ M / ‖x‖ ^ (k + 4) := by
  obtain ⟨v, r, hr, hv, he, _, hv0, _, _, hQΔ, _, R, M, hR, hW, hWb⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨_, hΔ⟩ := levelArea_translated_remainder_smooth_harmonic hK hR₀ hKR hu hh hQΔ
  let S := max R (R₀ + ‖(v 0)⁻¹ • gradient v 0‖)
  have hS : 0 < S := hR.trans_le (le_max_left _ _)
  have hWs : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | S < ‖x‖} := by
    apply hW.mono
    intro x hx
    change R < ‖x‖
    exact (le_max_left _ _).trans_lt hx
  obtain ⟨M', hM', hDb⟩ := levelArea_harmonic_exterior_iterated_decay k hS (abs_nonneg M)
    hWs (fun x hx => hΔ x ((le_max_right _ _).trans_lt hx)) (fun x hx =>
      ((hWb x ((le_max_left _ _).trans hx)).1).trans
        (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  refine ⟨v, r, hr, hv, he, hv0, 2 * S, M', by positivity, hM', ?_, hDb⟩
  exact hWs.mono (fun x hx => by change S < ‖x‖; change 2 * S < ‖x‖ at hx; linarith)

/-- The squared-radius remainder has second derivative `O(t)` as soon as the
radius remainder has second derivative `O(t²)`. This does not estimate the
second derivative of the additional area correction. -/
theorem levelArea_radius_square_fderiv_two_bound {v ρ : E3 → ℝ} {t A B L P : ℝ}
    (hC : 0 < v 0) (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hP : 0 ≤ P)
    {x : E3} (hx : x ≠ 0) (hρ : ContDiffAt ℝ 2 ρ x) (hpos : 0 < ρ x)
    (hcoarse : |ρ x - v 0 / t| ≤ L) (hD : ‖fderiv ℝ ρ x‖ ≤ P * t)
    (hE : ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x‖ ≤ A * t ^ 2)
    (hQ : ‖fderiv ℝ (fderiv ℝ
      (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x‖ ≤ B) :
    ‖fderiv ℝ (fderiv ℝ (fun y => ρ y ^ 2 - ((v 0) ^ 2 / t ^ 2 +
      2 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / v 0))) x‖ ≤
      (2 * A * (v 0 + L) + 2 * P ^ 2 + 2 * L * B / (v 0) ^ 2) * t := by
  have hsupper : ρ x ≤ v 0 / t + L := by
    have := (abs_le.mp hcoarse).2
    linarith
  have hterm : 2 * ρ x * (A * t ^ 2) ≤ 2 * A * (v 0 + L) * t := by
    calc
      _ ≤ 2 * (v 0 / t + L) * (A * t ^ 2) := by gcongr
      _ = 2 * A * v 0 * t + 2 * A * L * t ^ 2 := by field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (by nlinarith : t ^ 2 ≤ t)
          (by positivity : 0 ≤ 2 * A * L)
        nlinarith
  have hquad : 2 * (P * t) * (P * t) ≤ 2 * P ^ 2 * t := by
    have := mul_le_mul_of_nonneg_left (by nlinarith : t ^ 2 ≤ t)
      (by positivity : 0 ≤ 2 * P ^ 2)
    nlinarith
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro f hf
  have hDe : |fderiv ℝ ρ x e| ≤ P * t := by
    have hb := (fderiv ℝ ρ x).le_opNorm e
    simp only [he, mul_one, Real.norm_eq_abs] at hb
    exact hb.trans hD
  have hDf : |fderiv ℝ ρ x f| ≤ P * t := by
    have hb := (fderiv ℝ ρ x).le_opNorm f
    simp only [hf, mul_one, Real.norm_eq_abs] at hb
    exact hb.trans hD
  have hEe : |fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x e f| ≤ A * t ^ 2 := by
    have hb := (fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x).le_opNorm₂ e f
    simp only [he, hf, mul_one, Real.norm_eq_abs] at hb
    exact hb.trans hE
  have hQe : |fderiv ℝ (fderiv ℝ
      (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x e f| ≤ B := by
    have hb := (fderiv ℝ (fderiv ℝ
      (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x).le_opNorm₂ e f
    simp only [he, hf, mul_one, Real.norm_eq_abs] at hb
    exact hb.trans hQ
  rw [levelArea_radius_square_fderiv_two hC.ne' ht.ne' hx hρ, Real.norm_eq_abs]
  calc
    _ ≤ |2 * ρ x * fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) x e f| +
        |2 * fderiv ℝ ρ x e * fderiv ℝ ρ x f| +
        |(2 * t / (v 0) ^ 2 * (ρ x - v 0 / t)) *
          fderiv ℝ (fderiv ℝ
            (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) x e f| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * ρ x * (A * t ^ 2) + 2 * (P * t) * (P * t) +
        (2 * t / (v 0) ^ 2 * L) * B := by
      simp only [abs_mul, abs_of_pos hpos, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by positivity : 0 < 2 * t / (v 0) ^ 2)]
      gcongr
    _ ≤ 2 * A * (v 0 + L) * t + 2 * P ^ 2 * t +
        (2 * t / (v 0) ^ 2 * L) * B := by gcongr
    _ = _ := by ring

end LiquidDrop.CapacitaryK
