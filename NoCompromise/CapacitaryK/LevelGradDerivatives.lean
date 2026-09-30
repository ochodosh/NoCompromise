module

public import NoCompromise.CapacitaryK.LevelGradExpansion
public import NoCompromise.CapacitaryK.LevelRadiusDerivatives
public import NoCompromise.CapacitaryK.LevelFrame

@[expose] public section

/-!
# Angular calculus for the gradient length on capacitary levels

The angular remainder is extended using radial normalization. At a unit direction,
the chain rule splits its derivative into a radial derivative times the radius
gradient and a tangential derivative times the radius. The leading coefficients
are `-2 + 3 = 1`, as required by Chapter 31, `eq:K-gradu`.

The value and first angular derivative estimates are proved in
`capacitary_level_gradNorm_first_derivative`. No second angular derivative estimate
is asserted here.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The gradient-length error, with the angular argument radially normalized. -/
def levelGradRemainder (u v : E3 → ℝ) (t : ℝ) (ρ : E3 → ℝ) (y : E3) : ℝ :=
  gradNorm u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) -
    (t ^ 2 / v 0 + t ^ 4 * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / (v 0) ^ 4)

/-- The angular chain rule on a radial graph, using the ambient derivative
of the radially normalized argument. No level-set equation is needed. -/
theorem levelGrad_radial_composition_gradient {F ρ : E3 → ℝ} {z θ : E3}
    (hθ : ‖θ‖ = 1) (hρ : DifferentiableAt ℝ ρ θ)
    (hF : DifferentiableAt ℝ F (ρ θ • θ + z)) :
    DifferentiableAt ℝ (fun y => F (ρ y • (‖y‖⁻¹ • y) + z)) θ ∧
      gradient (fun y => F (ρ y • (‖y‖⁻¹ • y) + z)) θ =
        ⟪gradient F (ρ θ • θ + z), θ⟫ • gradient ρ θ +
          ρ θ • (gradient F (ρ θ • θ + z) -
            ⟪gradient F (ρ θ • θ + z), θ⟫ • θ) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  let q : E3 → ℝ := fun y => ρ y * ‖y‖⁻¹
  have hinv := (hasDerivAt_inv (norm_ne_zero_iff.mpr hθ0)).comp_hasFDerivAt θ
    (levelRadius_hasFDerivAt_norm hθ0)
  have hq := hρ.hasFDerivAt.mul hinv
  have hsm := (hq.smul (hasFDerivAt_id θ)).add_const z
  have hqθ : q θ = ρ θ := by simp [q, hθ]
  have hF' : HasFDerivAt F (fderiv ℝ F (ρ θ • θ + z)) (q θ • θ + z) := by
    rw [hqθ]
    exact hF.hasFDerivAt
  have hd := hF'.comp θ hsm
  change HasFDerivAt (fun y => F (q y • y + z)) _ θ at hd
  have he : (fun y => F (ρ y • (‖y‖⁻¹ • y) + z)) =
      (fun y => F (q y • y + z)) := by
    funext y
    rw [smul_smul]
  refine ⟨by rw [he]; exact hd.differentiableAt, ?_⟩
  apply ext_inner_right ℝ
  intro e
  rw [he, inner_gradient_left, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  rw [map_add, map_smul, map_smul]
  simp only [← inner_gradient_left, inner_add_left, real_inner_smul_left,
    inner_sub_left, Pi.mul_apply, Function.comp_apply, id_eq, hθ, one_pow, inv_one, mul_one]
  ring

/-- Exact first derivative of the level gradient-length remainder. -/
theorem levelGradRemainder_gradient {u v ρ : E3 → ℝ} {t : ℝ} {θ : E3}
    (hθ : ‖θ‖ = 1) (hρ : DifferentiableAt ℝ ρ θ)
    (hu : DifferentiableAt ℝ (gradNorm u)
      (ρ θ • θ + (v 0)⁻¹ • gradient v 0)) :
    DifferentiableAt ℝ (levelGradRemainder u v t ρ) θ ∧
      gradient (levelGradRemainder u v t ρ) θ =
        ⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ •
            gradient ρ θ +
          ρ θ • (gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0) -
            ⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ • θ) -
          (t ^ 4 / (v 0) ^ 4) •
            (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
              ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ) := by
  obtain ⟨hd, hg⟩ := levelGrad_radial_composition_gradient hθ hρ hu
  obtain ⟨hQd, hQg⟩ := levelRadius_angular_gradient (translated_quadrupole_contDiff v)
    (kelvinTranslatedQuadrupole_smul v) hθ
  have he : levelGradRemainder u v t ρ = fun y =>
      gradNorm u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) -
        (t ^ 2 / v 0 + (t ^ 4 / (v 0) ^ 4) *
          kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) := by
    funext y
    dsimp [levelGradRemainder]
    ring
  have hder := hd.hasFDerivAt.sub
    ((hQd.hasFDerivAt.const_mul (t ^ 4 / (v 0) ^ 4)).const_add (t ^ 2 / v 0))
  change HasFDerivAt (fun y =>
    gradNorm u (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0) -
      (t ^ 2 / v 0 + (t ^ 4 / (v 0) ^ 4) *
        kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) _ θ at hder
  refine ⟨by rw [he]; exact hder.differentiableAt, ?_⟩
  rw [he, gradient, hder.fderiv, map_sub, map_smul]
  change gradient (fun y => gradNorm u
      (ρ y • (‖y‖⁻¹ • y) + (v 0)⁻¹ • gradient v 0)) θ -
    (t ^ 4 / (v 0) ^ 4) •
      gradient (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ = _
  rw [hg, hQg]

/-- Quantitative form of the coefficient cancellation `-2 + 3 = 1`.
The weaker inverse-radius accuracy `O(a²)` already suffices for this step. -/
theorem levelGrad_coefficient_cancellation {a ε K : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hεa : ε ≤ 2 * a) (hK : 0 ≤ K)
    (hd : |ε - a| ≤ K * a ^ 2) :
    |-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4| ≤ 59 * K * a ^ 5 := by
  have hε2 : ε ^ 2 ≤ 4 * a ^ 2 := by
    nlinarith [pow_le_pow_left₀ hε hεa 2]
  have hε3 : ε ^ 3 ≤ 8 * a ^ 3 := by
    nlinarith [pow_le_pow_left₀ hε hεa 3]
  have hpoly3 : ε ^ 2 + ε * a + a ^ 2 ≤ 7 * a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hεa ha]
  have hpoly4 : ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3 ≤ 15 * a ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hε2 ha,
      mul_le_mul_of_nonneg_right hεa (sq_nonneg a)]
  have h3 : |ε ^ 3 - a ^ 3| ≤ 7 * K * a ^ 4 := by
    rw [show ε ^ 3 - a ^ 3 = (ε - a) * (ε ^ 2 + ε * a + a ^ 2) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 + ε * a + a ^ 2)]
    calc
      _ ≤ (K * a ^ 2) * (7 * a ^ 2) :=
        mul_le_mul hd hpoly3 (by positivity) (by positivity)
      _ = _ := by ring
  have h4 : |ε ^ 4 - a ^ 4| ≤ 15 * K * a ^ 5 := by
    rw [show ε ^ 4 - a ^ 4 =
      (ε - a) * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3) by ring,
      abs_mul, abs_of_nonneg (by positivity :
        0 ≤ ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3)]
    calc
      _ ≤ (K * a ^ 2) * (15 * a ^ 3) :=
        mul_le_mul hd hpoly4 (by positivity) (by positivity)
      _ = _ := by ring
  rw [show -2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4 =
    3 * (ε ^ 4 - a ^ 4) - 2 * a * (ε ^ 3 - a ^ 3) by ring]
  calc
    _ ≤ |3 * (ε ^ 4 - a ^ 4)| + |2 * a * (ε ^ 3 - a ^ 3)| := abs_sub _ _
    _ = 3 * |ε ^ 4 - a ^ 4| + 2 * a * |ε ^ 3 - a ^ 3| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * a)]
      norm_num
    _ ≤ 3 * (15 * K * a ^ 5) + 2 * a * (7 * K * a ^ 4) := by gcongr
    _ = _ := by ring

/-- Propagation of radial and tangential errors through the angular chain rule.
Here `a = t/C`, `ε = 1/ρ`, `V = ∇ρ`, `d` is the radial derivative of the gradient
length, `Z` is its tangential derivative multiplied by `ρ`, and `H = ∇_T Q`.
Every error bound used in this algebraic step is an explicit hypothesis. -/
theorem levelGrad_angular_error_bound {C a ε A B D K d : ℝ} {H V Z : E3}
    (hC : 0 < C) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεa : ε ≤ 2 * a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hinv : |ε - a| ≤ K * a ^ 2) (hH : ‖H‖ ≤ B)
    (hV : ‖V - (a / C) • H‖ ≤ A * a ^ 2)
    (hd : |d + 2 * C * ε ^ 3| ≤ D * ε ^ 5)
    (hZ : ‖Z - (3 * ε ^ 4) • H‖ ≤ D * ε ^ 5) :
    ‖d • V + Z - a ^ 4 • H‖ ≤
      (8 * (2 * C + D) * A + 32 * D * (B / C + 1) + 59 * K * B) * a ^ 5 := by
  have hε53 : ε ^ 5 ≤ ε ^ 3 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have hε3 : ε ^ 3 ≤ 8 * a ^ 3 := by
    nlinarith [pow_le_pow_left₀ hε hεa 3]
  have hε5 : ε ^ 5 ≤ 32 * a ^ 5 := by
    nlinarith [pow_le_pow_left₀ hε hεa 5]
  have hdabs : |d| ≤ (2 * C + D) * ε ^ 3 := by
    have he : d = (d + 2 * C * ε ^ 3) - 2 * C * ε ^ 3 := by ring
    calc
      |d| = |(d + 2 * C * ε ^ 3) - 2 * C * ε ^ 3| := congrArg abs he
      _ ≤ |d + 2 * C * ε ^ 3| + |2 * C * ε ^ 3| := abs_sub _ _
      _ ≤ D * ε ^ 5 + 2 * C * ε ^ 3 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * C * ε ^ 3)]
        exact add_le_add hd le_rfl
      _ ≤ (2 * C + D) * ε ^ 3 := by nlinarith
  have he : d • V + Z - a ^ 4 • H =
      d • (V - (a / C) • H) +
        ((d + 2 * C * ε ^ 3) * (a / C)) • H +
        (Z - (3 * ε ^ 4) • H) + (-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) • H := by
    have hc : (2 * C * ε ^ 3) * (a / C) = 2 * ε ^ 3 * a := by field_simp
    rw [add_mul, hc]
    module
  have h₁ : ‖d • (V - (a / C) • H)‖ ≤ 8 * (2 * C + D) * A * a ^ 5 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ ((2 * C + D) * ε ^ 3) * (A * a ^ 2) :=
        mul_le_mul hdabs hV (norm_nonneg _) (by positivity)
      _ ≤ ((2 * C + D) * (8 * a ^ 3)) * (A * a ^ 2) := by gcongr
      _ = _ := by ring
  have h₂ : ‖((d + 2 * C * ε ^ 3) * (a / C)) • H‖ ≤
      32 * D * (B / C) * a ^ 5 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a / C)]
    calc
      _ ≤ ((D * ε ^ 5) * (1 / C)) * B := by
        apply mul_le_mul _ hH (norm_nonneg _) (by positivity)
        exact mul_le_mul hd (div_le_div_of_nonneg_right ha1 hC.le)
          (by positivity) (by positivity)
      _ ≤ ((D * (32 * a ^ 5)) * (1 / C)) * B := by gcongr
      _ = _ := by ring
  have h₃ : ‖Z - (3 * ε ^ 4) • H‖ ≤ 32 * D * a ^ 5 :=
    hZ.trans ((mul_le_mul_of_nonneg_left hε5 hD).trans_eq (by ring))
  have h₄ : ‖(-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) • H‖ ≤
      59 * K * B * a ^ 5 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (levelGrad_coefficient_cancellation ha hε hεa hK hinv)
      hH (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [he]
  calc
    _ ≤ ‖d • (V - (a / C) • H)‖ + ‖((d + 2 * C * ε ^ 3) * (a / C)) • H‖ +
        ‖Z - (3 * ε ^ 4) • H‖ + ‖(-2 * ε ^ 3 * a + 3 * ε ^ 4 - a ^ 4) • H‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-- A vector expansion for the spatial gradient of the gradient length gives the
radial and tangential estimates needed in the angular chain rule. -/
theorem levelGrad_radial_tangent_estimates {C ε q D : ℝ} {θ H g : E3}
    (hθ : ‖θ‖ = 1) (hH : ⟪H, θ⟫ = 0) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : 0 ≤ D)
    (hg : ‖g - ((-2 * C * ε ^ 3 - 12 * q * ε ^ 5) • θ +
      (3 * ε ^ 5) • H)‖ ≤ D * ε ^ 6) :
    |⟪g, θ⟫ + 2 * C * ε ^ 3| ≤ (12 * |q| + D) * ε ^ 5 ∧
      ‖ε⁻¹ • (g - ⟪g, θ⟫ • θ) - (3 * ε ^ 4) • H‖ ≤ 2 * D * ε ^ 5 := by
  let e := g - ((-2 * C * ε ^ 3 - 12 * q * ε ^ 5) • θ + (3 * ε ^ 5) • H)
  have he : ‖e‖ ≤ D * ε ^ 6 := hg
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  have hie : ⟪e, θ⟫ = ⟪g, θ⟫ + 2 * C * ε ^ 3 + 12 * q * ε ^ 5 := by
    dsimp [e]
    rw [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hθθ, hH]
    ring
  have hib : |⟪e, θ⟫| ≤ D * ε ^ 6 := by
    have hi : |⟪e, θ⟫| ≤ ‖e‖ := by
      simpa only [hθ, mul_one] using abs_real_inner_le_norm e θ
    exact hi.trans he
  refine ⟨?_, ?_⟩
  · have hid : ⟪g, θ⟫ + 2 * C * ε ^ 3 = ⟪e, θ⟫ - 12 * q * ε ^ 5 := by
      rw [hie]
      ring
    have h65 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
    rw [hid]
    calc
      _ ≤ |⟪e, θ⟫| + |12 * q * ε ^ 5| := abs_sub _ _
      _ ≤ D * ε ^ 6 + 12 * |q| * ε ^ 5 := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < ε ^ 5)]
        norm_num
        exact hib
      _ ≤ (12 * |q| + D) * ε ^ 5 := by nlinarith
  · have hid : ε⁻¹ • (g - ⟪g, θ⟫ • θ) - (3 * ε ^ 4) • H =
        ε⁻¹ • (e - ⟪e, θ⟫ • θ) := by
      rw [hie]
      dsimp [e]
      have hc : ε⁻¹ * (3 * ε ^ 5) = 3 * ε ^ 4 := by field_simp
      rw [← hc]
      module
    rw [hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    calc
      _ ≤ ε⁻¹ * (2 * (D * ε ^ 6)) := by
        gcongr
        exact (levelRadius_tangent_norm_le hθ).trans (by linarith)
      _ = _ := by field_simp

/-- First derivative control at a unit direction, given the spatial radial and
tangential estimates. The hypotheses identify precisely the analytic estimates
still needed beyond the radius theorem. -/
theorem levelGradRemainder_first_derivative_of_radial_tangent_estimates
    {u v ρ : E3 → ℝ} {t A B D K : ℝ} {θ : E3}
    (hC : 0 < v 0) (ht : 0 ≤ t) (htC : t / v 0 ≤ 1)
    (hθ : ‖θ‖ = 1) (hρpos : 0 < ρ θ) (hρ1 : (ρ θ)⁻¹ ≤ 1)
    (hinv2 : (ρ θ)⁻¹ ≤ 2 * (t / v 0))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hρ : DifferentiableAt ℝ ρ θ)
    (hu : DifferentiableAt ℝ (gradNorm u)
      (ρ θ • θ + (v 0)⁻¹ • gradient v 0))
    (hinv : |(ρ θ)⁻¹ - t / v 0| ≤ K * (t / v 0) ^ 2)
    (hQ : ‖gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
      ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ‖ ≤ B)
    (hρerr : ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤ A * (t / v 0) ^ 2)
    (hrad : |⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ +
      2 * v 0 * (ρ θ)⁻¹ ^ 3| ≤ D * (ρ θ)⁻¹ ^ 5)
    (htan : ‖ρ θ •
      (gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0) -
        ⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ • θ) -
      (3 * (ρ θ)⁻¹ ^ 4) •
        (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
          ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ)‖ ≤
      D * (ρ θ)⁻¹ ^ 5) :
    ‖fderiv ℝ (levelGradRemainder u v t ρ) θ‖ ≤
      ((8 * (2 * v 0 + D) * A + 32 * D * (B / v 0 + 1) + 59 * K * B) /
        (v 0) ^ 5) * t ^ 5 := by
  have hV : ‖gradient ρ θ - ((t / v 0) / v 0) •
      (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
        ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ)‖ ≤
        A * (t / v 0) ^ 2 := by
    have he : (t / v 0) / v 0 = t / (v 0) ^ 2 := by ring
    rw [he, ← levelRadiusRemainder_gradient hθ hρ]
    simpa only [gradient, (toDual ℝ E3).symm.norm_map] using hρerr
  have hb := levelGrad_angular_error_bound hC (div_nonneg ht hC.le) htC
    (inv_nonneg.mpr hρpos.le) hρ1 hinv2 hA hB hD hK hinv hQ hV hrad htan
  have hn : ‖fderiv ℝ (levelGradRemainder u v t ρ) θ‖ =
      ‖gradient (levelGradRemainder u v t ρ) θ‖ :=
    ((toDual ℝ E3).symm.norm_map _).symm
  rw [hn, (levelGradRemainder_gradient hθ hρ hu).2]
  rw [div_pow, div_pow] at hb
  convert hb using 1
  ring

/-- Tangential cancellation in the Hessian-gradient product, before dividing by
the gradient length. `S θ = -4 f` is the differentiated homogeneity identity
for the quadrupole potential. `T` represents the full Hessian and `E` its remainder. -/
theorem levelGrad_tangent_hessian_product {C ε B M : ℝ} {θ g f w : E3}
    {T S E : E3 →L[ℝ] E3}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hθ : ‖θ‖ = 1) (hf : ‖f‖ ≤ B) (hw : ‖w‖ ≤ M * ε ^ 5)
    (hg : g = -(C * ε ^ 2) • θ + ε ^ 4 • f + w)
    (hT : ∀ v : E3, T v = (C * ε ^ 3) • ((3 * ⟪v, θ⟫) • θ - v) +
      ε ^ 5 • S v + E v)
    (hSθ : S θ = (-4 : ℝ) • f) (hS : ‖S‖ ≤ B) (hE : ‖E‖ ≤ M * ε ^ 6) :
    ‖(T g - ⟪T g, θ⟫ • θ) -
      (3 * C * ε ^ 7) • (f - ⟪f, θ⟫ • θ)‖ ≤
      2 * (C * M + B ^ 2 + B * M + M * (C + B + M)) * ε ^ 8 := by
  let P : E3 →L[ℝ] E3 := ContinuousLinearMap.id ℝ E3 - (innerSL ℝ θ).smulRight θ
  have hP (v : E3) : P v = v - ⟪v, θ⟫ • θ := by
    simp only [P, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_comm θ v]
  have hPθ : P θ = 0 := by
    rw [hP, real_inner_self_eq_norm_sq, hθ]
    simp
  have hPn (v : E3) : ‖P v‖ ≤ 2 * ‖v‖ := by
    rw [hP]
    exact levelRadius_tangent_norm_le hθ
  have h42 : ε ^ 4 ≤ ε ^ 2 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have h52 : ε ^ 5 ≤ ε ^ 2 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have h98 : ε ^ 9 ≤ ε ^ 8 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have h108 : ε ^ 10 ≤ ε ^ 8 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have hgn : ‖g‖ ≤ (C + B + M) * ε ^ 2 := by
    rw [hg]
    calc
      _ ≤ ‖-(C * ε ^ 2) • θ‖ + ‖ε ^ 4 • f‖ + ‖w‖ := norm_add₃_le
      _ ≤ C * ε ^ 2 + ε ^ 4 * B + M * ε ^ 5 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity :
          0 ≤ C * ε ^ 2), abs_of_nonneg (by positivity : 0 ≤ ε ^ 4), hθ, mul_one]
        gcongr
      _ ≤ (C + B + M) * ε ^ 2 := by nlinarith
  have hid : P (T g) - (3 * C * ε ^ 7) • P f =
      -(C * ε ^ 3) • P w + ε ^ 9 • P (S f) +
        ε ^ 5 • P (S w) + P (E g) := by
    rw [hT]
    simp only [map_add, map_sub, map_smul, hPθ, smul_zero, zero_sub]
    rw [hg]
    simp only [map_add, map_smul, hPθ, hSθ, smul_zero, zero_add]
    module
  have h₁ : ‖-(C * ε ^ 3) • P w‖ ≤ 2 * C * M * ε ^ 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity :
      0 ≤ C * ε ^ 3)]
    calc
      _ ≤ (C * ε ^ 3) * (2 * (M * ε ^ 5)) := by
        gcongr
        exact (hPn w).trans (by linarith)
      _ = _ := by ring
  have h₂ : ‖ε ^ 9 • P (S f)‖ ≤ 2 * B ^ 2 * ε ^ 8 := by
    have hs : ‖S f‖ ≤ B * B :=
      (S.le_opNorm f).trans (mul_le_mul hS hf (norm_nonneg _) hB)
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 9)]
    calc
      _ ≤ ε ^ 9 * (2 * (B * B)) := by
        gcongr
        exact (hPn (S f)).trans (by linarith)
      _ ≤ ε ^ 8 * (2 * (B * B)) := by gcongr
      _ = _ := by ring
  have h₃ : ‖ε ^ 5 • P (S w)‖ ≤ 2 * B * M * ε ^ 8 := by
    have hs : ‖S w‖ ≤ B * (M * ε ^ 5) :=
      (S.le_opNorm w).trans (mul_le_mul hS hw (norm_nonneg _) hB)
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 5)]
    calc
      _ ≤ ε ^ 5 * (2 * (B * (M * ε ^ 5))) := by
        gcongr
        exact (hPn (S w)).trans (by linarith)
      _ = 2 * B * M * ε ^ 10 := by ring
      _ ≤ _ := by gcongr
  have h₄ : ‖P (E g)‖ ≤ 2 * M * (C + B + M) * ε ^ 8 := by
    have he : ‖E g‖ ≤ (M * ε ^ 6) * ((C + B + M) * ε ^ 2) :=
      (E.le_opNorm g).trans (mul_le_mul hE hgn (norm_nonneg _) (by positivity))
    exact ((hPn (E g)).trans (mul_le_mul_of_nonneg_left he (by norm_num))).trans_eq
      (by ring)
  rw [← hP (T g), ← hP f, hid]
  calc
    _ ≤ ‖-(C * ε ^ 3) • P w‖ + ‖ε ^ 9 • P (S f)‖ +
        ‖ε ^ 5 • P (S w)‖ + ‖P (E g)‖ :=
      (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
    _ ≤ _ := by linarith

/-- Lower bound and leading approximation for the gradient length. The smallness
condition is explicit and, in the exterior application, follows by increasing the radius. -/
theorem levelGrad_norm_perturbation {C ε B M : ℝ} {θ g f w : E3}
    (hC : 0 < C) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M)
    (hθ : ‖θ‖ = 1) (hf : ‖f‖ ≤ B) (hw : ‖w‖ ≤ M * ε ^ 5)
    (hg : g = -(C * ε ^ 2) • θ + ε ^ 4 • f + w)
    (hsmall : (B + M) * ε ^ 2 ≤ C / 2) :
    C * ε ^ 2 / 2 ≤ ‖g‖ ∧ 0 < ‖g‖ ∧
      |‖g‖ - C * ε ^ 2| ≤ (B + M) * ε ^ 4 := by
  have h54 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hpert : ‖g - (-(C * ε ^ 2) • θ)‖ ≤ (B + M) * ε ^ 4 := by
    rw [hg, show -(C * ε ^ 2) • θ + ε ^ 4 • f + w - (-(C * ε ^ 2) • θ) =
      ε ^ 4 • f + w by module]
    calc
      _ ≤ ‖ε ^ 4 • f‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε ^ 4 * B + M * ε ^ 5 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 4)]
        gcongr
      _ ≤ (B + M) * ε ^ 4 := by nlinarith
  have hn : ‖-(C * ε ^ 2) • θ‖ = C * ε ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), hθ, mul_one]
  have he : |‖g‖ - C * ε ^ 2| ≤ (B + M) * ε ^ 4 := by
    rw [← hn]
    exact (abs_norm_sub_norm_le _ _).trans hpert
  have hhalf : C * ε ^ 2 / 2 ≤ ‖g‖ := by
    have h := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ε)
    have := (abs_le.mp he).1
    nlinarith
  exact ⟨hhalf, lt_of_lt_of_le (by positivity) hhalf, he⟩

/-- Dividing the tangential Hessian-gradient expansion by the gradient length
loses two inverse-radius powers. -/
theorem levelGrad_normalized_tangent_error {C ε n A B D : ℝ} {V H : E3}
    (hC : 0 < C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hn : C * ε ^ 2 / 2 ≤ n) (hd : |n - C * ε ^ 2| ≤ D * ε ^ 4)
    (hH : ‖H‖ ≤ B) (hV : ‖V - (3 * C * ε ^ 7) • H‖ ≤ A * ε ^ 8) :
    ‖n⁻¹ • V - (3 * ε ^ 5) • H‖ ≤ (2 / C * (A + 3 * D * B)) * ε ^ 6 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have h98 : ε ^ 9 ≤ ε ^ 8 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hid : n • (n⁻¹ • V - (3 * ε ^ 5) • H) =
      (V - (3 * C * ε ^ 7) • H) + ((C * ε ^ 2 - n) * (3 * ε ^ 5)) • H := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    module
  have hterm : ‖((C * ε ^ 2 - n) * (3 * ε ^ 5)) • H‖ ≤ 3 * D * B * ε ^ 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_sub_comm,
      abs_of_pos (by positivity : 0 < 3 * ε ^ 5)]
    calc
      _ ≤ ((D * ε ^ 4) * (3 * ε ^ 5)) * B := by gcongr
      _ = 3 * D * B * ε ^ 9 := by ring
      _ ≤ _ := by gcongr
  have hprod : n * ‖n⁻¹ • V - (3 * ε ^ 5) • H‖ ≤ (A + 3 * D * B) * ε ^ 8 := by
    calc
      _ = ‖n • (n⁻¹ • V - (3 * ε ^ 5) • H)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hn0.le]
      _ ≤ ‖V - (3 * C * ε ^ 7) • H‖ + ‖((C * ε ^ 2 - n) * (3 * ε ^ 5)) • H‖ := by
        rw [hid]
        exact norm_add_le _ _
      _ ≤ _ := by linarith
  have hhalf := mul_le_mul_of_nonneg_right hn (norm_nonneg (n⁻¹ • V - (3 * ε ^ 5) • H))
  have hm := mul_le_mul_of_nonneg_left (hhalf.trans hprod)
    (by positivity : 0 ≤ 2 / (C * ε ^ 2))
  have hl : 2 / (C * ε ^ 2) * (C * ε ^ 2 / 2 *
      ‖n⁻¹ • V - (3 * ε ^ 5) • H‖) = ‖n⁻¹ • V - (3 * ε ^ 5) • H‖ := by
    field_simp
  rw [hl] at hm
  exact hm.trans_eq (by field_simp)

/-- Control of the normalized gradient from its monopole approximation. -/
theorem levelGrad_normalized_gradient_error {C ε n D : ℝ} {θ g : E3}
    (hC : 0 < C) (hε : 0 < ε) (_hD : 0 ≤ D) (hθ : ‖θ‖ = 1)
    (hn : C * ε ^ 2 / 2 ≤ n) (hd : |n - C * ε ^ 2| ≤ D * ε ^ 4)
    (hg : ‖g + (C * ε ^ 2) • θ‖ ≤ D * ε ^ 4) :
    ‖n⁻¹ • g + θ‖ ≤ (4 * D / C) * ε ^ 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hid : n • (n⁻¹ • g + θ) =
      (g + (C * ε ^ 2) • θ) + (n - C * ε ^ 2) • θ := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    module
  have hprod : n * ‖n⁻¹ • g + θ‖ ≤ 2 * D * ε ^ 4 := by
    calc
      _ = ‖n • (n⁻¹ • g + θ)‖ := by rw [norm_smul, Real.norm_of_nonneg hn0.le]
      _ ≤ ‖g + (C * ε ^ 2) • θ‖ + ‖(n - C * ε ^ 2) • θ‖ := by
        rw [hid]
        exact norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs, hθ, mul_one]
        linarith
  have hhalf := mul_le_mul_of_nonneg_right hn (norm_nonneg (n⁻¹ • g + θ))
  have hm := mul_le_mul_of_nonneg_left (hhalf.trans hprod)
    (by positivity : 0 ≤ 2 / (C * ε ^ 2))
  have hl : 2 / (C * ε ^ 2) * (C * ε ^ 2 / 2 * ‖n⁻¹ • g + θ‖) =
      ‖n⁻¹ • g + θ‖ := by field_simp
  rw [hl] at hm
  exact hm.trans_eq (by field_simp; ring)

/-- A coarse Hessian bound suffices for the radial derivative estimate. -/
theorem levelGrad_normalized_radial_error {C ε n A B D : ℝ} {θ g : E3}
    {T : E3 →L[ℝ] E3}
    (hC : 0 < C) (hε : 0 < ε) (_hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hθ : ‖θ‖ = 1) (hn : C * ε ^ 2 / 2 ≤ n)
    (hd : |n - C * ε ^ 2| ≤ D * ε ^ 4)
    (hg : ‖g + (C * ε ^ 2) • θ‖ ≤ D * ε ^ 4)
    (hT : ‖T‖ ≤ B * ε ^ 3)
    (hTθ : ‖T θ - (2 * C * ε ^ 3) • θ‖ ≤ A * ε ^ 5) :
    |⟪n⁻¹ • T g, θ⟫ + 2 * C * ε ^ 3| ≤ (4 * B * D / C + A) * ε ^ 5 := by
  have he := levelGrad_normalized_gradient_error hC hε hD hθ hn hd hg
  have hid : n⁻¹ • T g + (2 * C * ε ^ 3) • θ =
      T (n⁻¹ • g + θ) - (T θ - (2 * C * ε ^ 3) • θ) := by
    rw [map_add, map_smul]
    module
  have hb : ‖n⁻¹ • T g + (2 * C * ε ^ 3) • θ‖ ≤
      (4 * B * D / C + A) * ε ^ 5 := by
    rw [hid]
    calc
      _ ≤ ‖T (n⁻¹ • g + θ)‖ + ‖T θ - (2 * C * ε ^ 3) • θ‖ := norm_sub_le _ _
      _ ≤ (B * ε ^ 3) * ((4 * D / C) * ε ^ 2) + A * ε ^ 5 := by
        apply add_le_add _ hTθ
        exact (T.le_opNorm _).trans (mul_le_mul hT he (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hi := abs_real_inner_le_norm (n⁻¹ • T g + (2 * C * ε ^ 3) • θ) θ
  rw [hθ, mul_one] at hi
  simpa only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    hθ, one_pow, mul_one] using hi.trans hb

/-- At a noncritical point, the spatial gradient of the gradient length is the
Hessian applied to the gradient, divided by its length. -/
theorem levelGrad_gradient_gradNorm {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (hg : 0 < gradNorm u x) :
    gradient (gradNorm u) x =
      (gradNorm u x)⁻¹ • fderiv ℝ (gradient u) x (gradient u x) := by
  apply ext_inner_right ℝ
  intro e
  rw [inner_gradient_left, fderiv_gradNorm_apply hu hg,
    real_inner_smul_left, ← dirHess_eq_inner hu, dirHess_comm hu]

/-- The tangential spatial derivative estimate follows directly from the gradient
and Hessian expansions. This estimate is at inverse radius `ε`, before composing
with a level radius. -/
theorem levelGrad_normalized_tangent_hessian_bound {C ε B M : ℝ} {θ g f w : E3}
    {T S E : E3 →L[ℝ] E3}
    (hC : 0 < C) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hθ : ‖θ‖ = 1) (hf : ‖f‖ ≤ B) (hw : ‖w‖ ≤ M * ε ^ 5)
    (hg : g = -(C * ε ^ 2) • θ + ε ^ 4 • f + w)
    (hT : ∀ v : E3, T v = (C * ε ^ 3) • ((3 * ⟪v, θ⟫) • θ - v) +
      ε ^ 5 • S v + E v)
    (hSθ : S θ = (-4 : ℝ) • f) (hS : ‖S‖ ≤ B) (hE : ‖E‖ ≤ M * ε ^ 6)
    (hsmall : (B + M) * ε ^ 2 ≤ C / 2) :
    ‖‖g‖⁻¹ • (T g - ⟪T g, θ⟫ • θ) - (3 * ε ^ 5) • (f - ⟪f, θ⟫ • θ)‖ ≤
      (2 / C * (2 * (C * M + B ^ 2 + B * M + M * (C + B + M)) +
        6 * (B + M) * B)) * ε ^ 6 := by
  obtain ⟨hn, _, hd⟩ := levelGrad_norm_perturbation hC hε hε1 hM hθ hf hw hg hsmall
  have hH : ‖f - ⟪f, θ⟫ • θ‖ ≤ 2 * B :=
    (levelRadius_tangent_norm_le hθ).trans (by linarith)
  have hV := levelGrad_tangent_hessian_product hC.le hε.le hε1 hB hM hθ hf hw hg
    hT hSθ hS hE
  have h := levelGrad_normalized_tangent_error hC hε hε1
    (by positivity) (by positivity) (by positivity) hn hd hH hV
  convert h using 1
  ring

/-- The spatial radial and tangential estimates, with one constant depending
only on the uniform monopole, quadrupole, and remainder bounds. The Hessian
decomposition and the quadrupole homogeneity identity are explicit inputs. -/
theorem levelGrad_spatial_derivative_estimates {C B M : ℝ}
    (hC : 0 < C) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ε : ℝ) (θ g f w : E3) (T S E : E3 →L[ℝ] E3),
      0 < ε → ε ≤ 1 → ‖θ‖ = 1 → ‖f‖ ≤ B → ‖w‖ ≤ M * ε ^ 5 →
      g = -(C * ε ^ 2) • θ + ε ^ 4 • f + w →
      (∀ v : E3, T v = (C * ε ^ 3) • ((3 * ⟪v, θ⟫) • θ - v) +
        ε ^ 5 • S v + E v) →
      S θ = (-4 : ℝ) • f → ‖S‖ ≤ B → ‖E‖ ≤ M * ε ^ 6 →
      (B + M) * ε ^ 2 ≤ C / 2 →
      0 < ‖g‖ ∧
        |⟪‖g‖⁻¹ • T g, θ⟫ + 2 * C * ε ^ 3| ≤ D * ε ^ 5 ∧
        ‖ε⁻¹ • (‖g‖⁻¹ • T g - ⟪‖g‖⁻¹ • T g, θ⟫ • θ) -
          (3 * ε ^ 4) • (f - ⟪f, θ⟫ • θ)‖ ≤ D * ε ^ 5 := by
  let Dr := 4 * (4 * C + B + M) * (B + M) / C + (4 * B + M)
  let Dt := 2 / C * (2 * (C * M + B ^ 2 + B * M + M * (C + B + M)) +
    6 * (B + M) * B)
  have hDr : 0 ≤ Dr := by dsimp [Dr]; positivity
  refine ⟨max Dr Dt, hDr.trans (le_max_left _ _), ?_⟩
  intro ε θ g f w T S E hε hε1 hθ hf hw hg hT hSθ hS hE hsmall
  obtain ⟨hn, hn0, hd⟩ := levelGrad_norm_perturbation hC hε hε1 hM hθ hf hw hg hsmall
  have h53 : ε ^ 5 ≤ ε ^ 3 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h63 : ε ^ 6 ≤ ε ^ 3 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h54 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h65 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hTn : ‖T‖ ≤ (4 * C + B + M) * ε ^ 3 := by
    apply T.opNorm_le_bound (by positivity)
    intro v
    have hvθ : |⟪v, θ⟫| ≤ ‖v‖ := by
      simpa only [hθ, mul_one] using abs_real_inner_le_norm v θ
    have hv : ‖(3 * ⟪v, θ⟫) • θ - v‖ ≤ 4 * ‖v‖ := by
      calc
        _ ≤ ‖(3 * ⟪v, θ⟫) • θ‖ + ‖v‖ := norm_sub_le _ _
        _ = 3 * |⟪v, θ⟫| + ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, hθ, mul_one]
          norm_num
        _ ≤ _ := by linarith
    have hSv : ‖S v‖ ≤ B * ‖v‖ :=
      (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg v))
    have hEv : ‖E v‖ ≤ (M * ε ^ 6) * ‖v‖ :=
      (E.le_opNorm v).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg v))
    rw [hT]
    calc
      _ ≤ ‖(C * ε ^ 3) • ((3 * ⟪v, θ⟫) • θ - v)‖ + ‖ε ^ 5 • S v‖ + ‖E v‖ :=
        norm_add₃_le
      _ ≤ (C * ε ^ 3) * (4 * ‖v‖) + ε ^ 5 * (B * ‖v‖) +
          (M * ε ^ 6) * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ C * ε ^ 3),
          Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 5)]
        gcongr
      _ ≤ (C * ε ^ 3) * (4 * ‖v‖) + ε ^ 3 * (B * ‖v‖) +
          (M * ε ^ 3) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hTθ : ‖T θ - (2 * C * ε ^ 3) • θ‖ ≤ (4 * B + M) * ε ^ 5 := by
    have hid : T θ - (2 * C * ε ^ 3) • θ = (-4 * ε ^ 5) • f + E θ := by
      rw [hT, hSθ, real_inner_self_eq_norm_sq, hθ]
      norm_num
      module
    have hEθ : ‖E θ‖ ≤ M * ε ^ 6 := by
      have he := (E.le_opNorm θ).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg θ))
      simpa only [hθ, mul_one] using he
    rw [hid]
    calc
      _ ≤ ‖(-4 * ε ^ 5) • f‖ + ‖E θ‖ := norm_add_le _ _
      _ ≤ (4 * ε ^ 5) * B + M * ε ^ 6 := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < ε ^ 5)]
        norm_num
        gcongr
      _ ≤ _ := by nlinarith
  have hpert : ‖g + (C * ε ^ 2) • θ‖ ≤ (B + M) * ε ^ 4 := by
    have he : g + (C * ε ^ 2) • θ = ε ^ 4 • f + w := by rw [hg]; module
    rw [he]
    calc
      _ ≤ ‖ε ^ 4 • f‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε ^ 4 * B + M * ε ^ 5 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 4)]
        gcongr
      _ ≤ _ := by nlinarith
  have hr : |⟪‖g‖⁻¹ • T g, θ⟫ + 2 * C * ε ^ 3| ≤ Dr * ε ^ 5 :=
    levelGrad_normalized_radial_error hC hε (by positivity) (by positivity)
      (by positivity) hθ hn hd hpert hTn hTθ
  have ht : ‖‖g‖⁻¹ • (T g - ⟪T g, θ⟫ • θ) -
      (3 * ε ^ 5) • (f - ⟪f, θ⟫ • θ)‖ ≤ Dt * ε ^ 6 :=
    levelGrad_normalized_tangent_hessian_bound hC hε hε1 hB hM hθ hf hw hg
      hT hSθ hS hE hsmall
  refine ⟨hn0, hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), ?_⟩
  have hid : ε⁻¹ • (‖g‖⁻¹ • T g - ⟪‖g‖⁻¹ • T g, θ⟫ • θ) -
      (3 * ε ^ 4) • (f - ⟪f, θ⟫ • θ) =
      ε⁻¹ • (‖g‖⁻¹ • (T g - ⟪T g, θ⟫ • θ) -
        (3 * ε ^ 5) • (f - ⟪f, θ⟫ • θ)) := by
    rw [real_inner_smul_left]
    have hc : 3 * ε ^ 4 = ε⁻¹ * (3 * ε ^ 5) := by field_simp
    rw [hc]
    module
  rw [hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  calc
    _ ≤ ε⁻¹ * (Dt * ε ^ 6) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = Dt * ε ^ 5 := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The vector Hessian and the bilinear second derivative are related by the
Riesz isometry, including under the total-derivative convention. -/
theorem levelGrad_fderiv_gradient_apply (u : E3 → ℝ) (x w : E3) :
    fderiv ℝ (gradient u) x w =
      (toDual ℝ E3).symm (fderiv ℝ (fderiv ℝ u) x w) := by
  change fderiv ℝ ((toDual ℝ E3).symm ∘ fderiv ℝ u) x w = _
  rw [(toDual ℝ E3).symm.comp_fderiv]
  rfl

/-- The operator bound for the bilinear Hessian also bounds the vector Hessian. -/
theorem levelGrad_norm_fderiv_gradient_le (u : E3 → ℝ) (x : E3) :
    ‖fderiv ℝ (gradient u) x‖ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  apply (fderiv ℝ (gradient u) x).opNorm_le_bound
    (norm_nonneg (fderiv ℝ (fderiv ℝ u) x))
  intro w
  rw [levelGrad_fderiv_gradient_apply, (toDual ℝ E3).symm.norm_map]
  exact (fderiv ℝ (fderiv ℝ u) x).le_opNorm w

/-- The quadrupole gradient has degree minus four. -/
theorem levelGrad_gradient_farQuadrupole_smul {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    gradient (farQuadrupole Q) (c • x) =
      (c ^ 4)⁻¹ • gradient (farQuadrupole Q) x := by
  rw [gradient, fderiv_farQuadrupole_smul hQh hc, map_smul]
  rfl

/-- The quadrupole vector Hessian has degree minus five. -/
theorem levelGrad_hessian_farQuadrupole_smul {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    fderiv ℝ (gradient (farQuadrupole Q)) (c • x) =
      (c ^ 5)⁻¹ • fderiv ℝ (gradient (farQuadrupole Q)) x :=
  fderiv_smul_of_negative_homogeneous
    (fun _ hd y => levelGrad_gradient_farQuadrupole_smul hQh hd y) hc x

/-- The homogeneity identity required by `levelGrad_spatial_derivative_estimates`. -/
theorem levelGrad_hessian_farQuadrupole_radial {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    fderiv ℝ (gradient (farQuadrupole Q)) x x =
      (-4 : ℝ) • gradient (farQuadrupole Q) x := by
  exact euler_of_negative_homogeneous
    (fun _ hc y => levelGrad_gradient_farQuadrupole_smul hQh hc y)
    (differentiableAt_gradient_of_contDiffAt
      ((contDiffAt_farQuadrupole hQ hx).of_le (by simp)))

/-- The monopole vector Hessian in polar coordinates. -/
theorem levelGrad_hessian_monopole (C : ℝ) {s : ℝ} (hs : 0 < s)
    {θ : E3} (hθ : ‖θ‖ = 1) (w : E3) :
    fderiv ℝ (gradient (fun y : E3 => C / ‖y‖)) (s • θ) w =
      (C / s ^ 3) • ((3 * ⟪w, θ⟫) • θ - w) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hx : s • θ ≠ 0 := smul_ne_zero hs.ne' hθ0
  have hn : ‖s • θ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hθ, mul_one]
  apply ext_inner_right ℝ
  intro e
  rw [levelGrad_fderiv_gradient_apply, toDual_symm_apply, fderiv_two_monopole C hx]
  simp only [real_inner_smul_left, inner_sub_left, hn]
  rw [real_inner_comm θ w]
  field_simp

/-- Additivity of the gradient at a point of differentiability. -/
theorem levelGrad_gradient_add {f g : E3 → ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  simp only [gradient, fderiv_fun_add hf hg, map_add]

/-- Additivity of the vector Hessian at a point of twice continuous differentiability. -/
theorem levelGrad_hessian_add {f g : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (gradient (fun y => f y + g y)) x =
      fderiv ℝ (gradient f) x + fderiv ℝ (gradient g) x := by
  have he : gradient (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => gradient f y + gradient g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact levelGrad_gradient_add (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num))
  rw [he.fderiv_eq, fderiv_fun_add (differentiableAt_gradient_of_contDiffAt hf)
    (differentiableAt_gradient_of_contDiffAt hg)]

/-- The far-field estimates for the spatial derivative of the gradient length.
Only two derivatives of the exterior potential remainder are used. -/
theorem levelGrad_far_spatial_derivatives {U Q : E3 → ℝ} {C R M : ℝ}
    (hC : 0 < C)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => U y - C / ‖y‖ - farQuadrupole Q y) {y | R < ‖y‖})
    (hWd : ∀ x : E3, R < ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - farQuadrupole Q y) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - farQuadrupole Q y)) x‖ ≤
        M / ‖x‖ ^ 6) :
    ∃ R' D : ℝ, R < R' ∧ 1 ≤ R' ∧ 0 ≤ D ∧
      ∀ θ : E3, ‖θ‖ = 1 → ∀ s : ℝ, R' ≤ s →
        DifferentiableAt ℝ (gradNorm U) (s • θ) ∧
        |⟪gradient (gradNorm U) (s • θ), θ⟫ + 2 * C / s ^ 3| ≤ D / s ^ 5 ∧
        ‖s • (gradient (gradNorm U) (s • θ) -
          ⟪gradient (gradNorm U) (s • θ), θ⟫ • θ) -
          (3 / s ^ 4) • (gradient (farQuadrupole Q) θ -
            ⟪gradient (farQuadrupole Q) θ, θ⟫ • θ)‖ ≤ D / s ^ 5 := by
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds hQ hQh
  obtain ⟨D, hD, hDb⟩ := levelGrad_spatial_derivative_estimates hC hB.le (abs_nonneg M)
  have hlim : Tendsto (fun s : ℝ => (B + |M|) / s ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨R', hR', hsmall⟩ := ((eventually_ge_atTop (max (R + 1) 1)).and
    (hlim.eventually (gt_mem_nhds (by positivity : 0 < C / 2)))).exists
  have hRR : R < R' := by have := (le_max_left _ _).trans hR'; linarith
  have hR1 : 1 ≤ R' := (le_max_right _ _).trans hR'
  refine ⟨R', D, hRR, hR1, hD, fun θ hθ s hs => ?_⟩
  have hs1 : 1 ≤ s := hR1.trans hs
  have hspos : 0 < s := zero_lt_one.trans_le hs1
  have hsR : R < s := hRR.trans_le hs
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hx0 : s • θ ≠ 0 := smul_ne_zero hspos.ne' hθ0
  have hn : ‖s • θ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hspos.le, hθ, mul_one]
  let W : E3 → ℝ := fun y => U y - C / ‖y‖ - farQuadrupole Q y
  let m : E3 → ℝ := fun y => C / ‖y‖
  let q := farQuadrupole Q
  have hm : ContDiffAt ℝ 2 m (s • θ) := (contDiffAt_monopole C hx0).of_le (by simp)
  have hq : ContDiffAt ℝ 2 q (s • θ) :=
    (contDiffAt_farQuadrupole hQ hx0).of_le (by simp)
  have hw : ContDiffAt ℝ 2 W (s • θ) :=
    (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds
      (by simpa only [mem_ofPred_eq, hn] using hsR))).of_le (by simp)
  have he : U = fun y => (m y + q y) + W y := by funext y; dsimp [m, q, W]; ring
  have hu : ContDiffAt ℝ 2 U (s • θ) := by rw [he]; exact (hm.add hq).add hw
  have hg : gradient U (s • θ) = -(C * s⁻¹ ^ 2) • θ +
      s⁻¹ ^ 4 • gradient q θ + gradient W (s • θ) := by
    conv_lhs => rw [he]
    rw [levelGrad_gradient_add ((hm.add hq).differentiableAt (by norm_num))
      (hw.differentiableAt (by norm_num)), levelGrad_gradient_add
      (hm.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    dsimp only [m, q]
    rw [gradient_monopole C hx0, levelGrad_gradient_farQuadrupole_smul hQh hspos,
      hn, smul_smul, inv_pow]
    simp only [inv_pow]
    congr 2
    field_simp
  have hT (v : E3) : fderiv ℝ (gradient U) (s • θ) v =
      (C * s⁻¹ ^ 3) • ((3 * ⟪v, θ⟫) • θ - v) +
        s⁻¹ ^ 5 • fderiv ℝ (gradient q) θ v + fderiv ℝ (gradient W) (s • θ) v := by
    conv_lhs => rw [he]
    rw [levelGrad_hessian_add (hm.add hq) hw, levelGrad_hessian_add hm hq]
    simp only [add_apply]
    dsimp only [m, q]
    rw [levelGrad_hessian_monopole C hspos hθ,
      levelGrad_hessian_farQuadrupole_smul hQh hspos, smul_apply, inv_pow,
      div_eq_mul_inv]
    simp only [inv_pow]
  have hf : ‖gradient q θ‖ ≤ B := by
    rw [gradient, (toDual ℝ E3).symm.norm_map]
    simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.1
  have hS : ‖fderiv ℝ (gradient q) θ‖ ≤ B :=
    (levelGrad_norm_fderiv_gradient_le q θ).trans
      (by simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.2)
  obtain ⟨hw1, hw2⟩ := hWd (s • θ) (by simpa only [hn] using hsR)
  rw [hn] at hw1 hw2
  have hgw : ‖gradient W (s • θ)‖ ≤ |M| * s⁻¹ ^ 5 := by
    rw [gradient, (toDual ℝ E3).symm.norm_map, inv_pow, ← div_eq_mul_inv]
    exact hw1.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
  have hE : ‖fderiv ℝ (gradient W) (s • θ)‖ ≤ |M| * s⁻¹ ^ 6 := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (levelGrad_norm_fderiv_gradient_le W (s • θ)).trans
      (hw2.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
  have hε1 : s⁻¹ ≤ 1 := by simpa using (inv_le_one₀ hspos).mpr hs1
  have hsmall' : (B + |M|) * s⁻¹ ^ 2 ≤ C / 2 := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (zero_le_one.trans hR1) hs 2)).trans hsmall.le
  obtain ⟨hgn, hrad, htan⟩ := hDb s⁻¹ θ (gradient U (s • θ)) (gradient q θ)
    (gradient W (s • θ)) (fderiv ℝ (gradient U) (s • θ))
    (fderiv ℝ (gradient q) θ) (fderiv ℝ (gradient W) (s • θ))
    (inv_pos.mpr hspos) hε1 hθ hf hgw hg hT
    (levelGrad_hessian_farQuadrupole_radial hQ hQh hθ0) hS hE hsmall'
  have hgn' : 0 < gradNorm U (s • θ) := hgn
  have hgrad := levelGrad_gradient_gradNorm hu hgn'
  refine ⟨differentiableAt_gradNorm hu hgn', ?_, ?_⟩
  · rw [hgrad]
    simpa only [gradNorm, inv_pow, div_eq_mul_inv, mul_assoc] using hrad
  · rw [hgrad]
    simpa only [gradNorm, q, inv_inv, inv_pow, div_eq_mul_inv] using htan

/-- A radius estimate `|ρ - C/t| ≤ L` gives the weaker inverse-radius estimate
used by the angular cancellation lemma. -/
theorem levelGrad_inverse_radius_error {C t s L : ℝ}
    (hC : 0 < C) (ht : 0 < t) (hs : 0 < s) (hL : 0 ≤ L)
    (hinv : s⁻¹ ≤ 2 * (t / C)) (herr : |s - C / t| ≤ L) :
    |s⁻¹ - t / C| ≤ 2 * L * (t / C) ^ 2 := by
  have he : s⁻¹ - t / C = -(s - C / t) * s⁻¹ * (t / C) := by
    field_simp
    ring
  rw [he, abs_mul, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hs),
    abs_of_pos (div_pos ht hC)]
  calc
    _ ≤ L * (2 * (t / C)) * (t / C) := by gcongr
    _ = _ := by ring

/-- The known uniform value bound, with the same radius quantifiers and smoothness
conclusion as the angular radius theorem. -/
theorem capacitary_level_gradNorm_remainder_value
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
        ∀ θ : E3, ‖θ‖ = 1 → |levelGradRemainder u v t ρ θ| ≤ A * t ^ 5 := by
  obtain ⟨v, r, hr, hv, he, hv0, A, hA, hev⟩ :=
    capacitary_level_gradNorm_expansion hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨v', r', hr', hv', he', _, B, _, hev'⟩ :=
    capacitary_level_radius_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0, hg0, _⟩ := kelvin_extension_data_eq hr' hr hv' hv he' he
  refine ⟨v, r, hr, hv, he, hv0, A, hA, ?_⟩
  filter_upwards [hev, hev'] with t ht ht'
  intro ρ hhom hroot
  have hroot' : ∀ θ : E3, ‖θ‖ = 1 →
      0 < ρ θ ∧ u (ρ θ • θ + (v' 0)⁻¹ • gradient v' 0) = t := by
    simpa only [h0, hg0] using hroot
  refine ⟨(ht' ρ hhom hroot').1, fun θ hθ => ?_⟩
  simpa only [levelGradRemainder, hθ, inv_one, one_smul, gradNorm] using
    ht θ hθ (ρ θ) (hroot θ hθ).1 (hroot θ hθ).2

set_option maxHeartbeats 400000 in
-- The uniform assembly combines three existential expansions and exceeds the default limit.
/-- The value and first angular derivative of the gradient-length error are
uniformly `O(t⁵)` on small capacitary levels, with the original capacitary hypotheses. -/
theorem capacitary_level_gradNorm_first_derivative
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
          |levelGradRemainder u v t ρ θ| ≤ A * t ^ 5 ∧
          ‖fderiv ℝ (levelGradRemainder u v t ρ) θ‖ ≤ A * t ^ 5 := by
  obtain ⟨v, r, hr, hv, he, _, hv0, _, hQs, _, _, R, M, _, hW, hWb⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨vr, rr, hrr, hvr, her, _, Ar, hAr, hevR⟩ :=
    capacitary_level_radius_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0r, hgr, hQr⟩ := kelvin_extension_data_eq hrr hr hvr hv her he
  simp only [levelRadiusRemainder, h0r, hgr, hQr] at hevR
  obtain ⟨vg, rg, hrg, hvg, heg, _, Ag, hAg, hevG⟩ :=
    capacitary_level_gradNorm_expansion hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0g, hgg, hQg⟩ := kelvin_extension_data_eq hrg hr hvg hv heg he
  simp only [h0g, hgg, hQg] at hevG
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  have hW' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => U y - v 0 / ‖y‖ - farQuadrupole (kelvinTranslatedQuadrupole v) y)
      {y | R < ‖y‖} := hW
  obtain ⟨R', D, _, hR1, hD, hDb⟩ := levelGrad_far_spatial_derivatives hv0
    (translated_quadrupole_contDiff v) hQs hW' (fun x hx => (hWb x hx.le).2)
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) hQs
  let L := Ar + B / (v 0) ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let A := (8 * (2 * v 0 + D) * (Ar * (v 0) ^ 2) +
    32 * D * ((2 * B) / v 0 + 1) + 59 * (2 * L) * (2 * B)) / (v 0) ^ 5
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨v, r, hr, hv, he, hv0, max Ag A, hAg.trans (le_max_left _ _), ?_⟩
  have eC := level_eventually_lt_of_continuous (g := fun t => t / v 0)
    (continuous_id.div_const _) (by simp) one_pos
  have eL := level_eventually_lt_of_continuous (g := fun t => t * L)
    (continuous_id.mul continuous_const) (by simp) (by positivity : 0 < v 0 / 2)
  have eR := level_eventually_lt_of_continuous (g := fun t => t * (R' + L))
    (continuous_id.mul continuous_const) (by simp) hv0
  filter_upwards [hevR, hevG, Ioo_mem_nhdsGT one_pos, eC, eL, eR]
    with t htR htG htr htC htL htFar
  have ht : 0 < t := htr.1
  have ht1 : t ≤ 1 := htr.2.le
  intro ρ hhom hroot
  obtain ⟨hsmooth, hρb⟩ := htR ρ hhom hroot
  refine ⟨hsmooth, fun θ hθ => ?_⟩
  obtain ⟨hs, hut⟩ := hroot θ hθ
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  obtain ⟨hρval, hρder⟩ := hρb θ hθ
  have hval : |levelGradRemainder u v t ρ θ| ≤ Ag * t ^ 5 := by
    simpa only [levelGradRemainder, hθ, inv_one, one_smul, gradNorm] using
      htG θ hθ (ρ θ) hs hut
  refine ⟨hval.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), ?_⟩
  have hqval : |kelvinTranslatedQuadrupole v θ| ≤ B := by
    simpa only [farQuadrupole, hθ, one_pow, div_one] using (hBb θ hθ0).1
  have hρval' : |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤
      Ar * t ^ 2 := by simpa only [hθ, inv_one, one_smul] using hρval
  have hcoarse : |ρ θ - v 0 / t| ≤ L := by
    have hterm : |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| ≤ B / (v 0) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg (v 0))]
      gcongr
      calc t * |kelvinTranslatedQuadrupole v θ| ≤ 1 * B :=
            mul_le_mul ht1 hqval (abs_nonneg _) (by norm_num)
        _ = B := one_mul B
    calc
      _ = |(ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)) +
          t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := by congr 1; ring
      _ ≤ |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| +
          |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := abs_add_le _ _
      _ ≤ Ar * t ^ 2 + B / (v 0) ^ 2 := add_le_add hρval' hterm
      _ ≤ L := by
        dsimp [L]
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        nlinarith
  have hlower : v 0 / t - L ≤ ρ θ := by have := (abs_le.mp hcoarse).1; linarith
  have hhalf : v 0 / (2 * t) ≤ ρ θ := by
    have hLt : L ≤ v 0 / (2 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have heq : v 0 / t - v 0 / (2 * t) = v 0 / (2 * t) := by ring
    linarith
  have hinv2 : (ρ θ)⁻¹ ≤ 2 * (t / v 0) := by
    have h := (inv_le_inv₀ hs (by positivity : 0 < v 0 / (2 * t))).mpr hhalf
    exact h.trans_eq (by field_simp)
  have hsR : R' ≤ ρ θ := by
    have hrlt : R' + L < v 0 / t := by
      rw [lt_div_iff₀ ht]
      nlinarith
    linarith
  have hρ1 : (ρ θ)⁻¹ ≤ 1 := (inv_le_one₀ hs).mpr (hR1.trans hsR)
  have hinv := levelGrad_inverse_radius_error hv0 ht hs hL hinv2 hcoarse
  have hρd : DifferentiableAt ℝ ρ θ :=
    (hsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).differentiableAt (by simp)
  have hρder' : ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤
      (Ar * (v 0) ^ 2) * (t / v 0) ^ 2 := by
    have heq : (Ar * (v 0) ^ 2) * (t / v 0) ^ 2 = Ar * t ^ 2 := by field_simp
    rw [heq]
    have hrem : levelRadiusRemainder vr t ρ = levelRadiusRemainder v t ρ := by
      funext y
      simp only [levelRadiusRemainder, h0r, hQr]
    rwa [hrem] at hρder
  have hQbound : ‖gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
      ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ‖ ≤ 2 * B := by
    have hgq : ‖gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B := by
      rw [gradient, (toDual ℝ E3).symm.norm_map]
      simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.1
    exact (levelRadius_tangent_norm_le hθ).trans (by linarith)
  obtain ⟨hUd, hrad, htan⟩ := hDb θ hθ (ρ θ) hsR
  have hGN : gradNorm U = fun y => gradNorm u (y + (v 0)⁻¹ • gradient v 0) := by
    funext y
    simp only [gradNorm, U, gradient, fderiv_comp_add_right]
  have hGG (y : E3) : gradient (gradNorm U) y =
      gradient (gradNorm u) (y + (v 0)⁻¹ • gradient v 0) := by
    simp only [hGN, gradient, fderiv_comp_add_right]
  have hdu : DifferentiableAt ℝ (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0) := by
    rw [hGN] at hUd
    exact (differentiableAt_comp_add_right _).mp hUd
  simp only [hGG] at hrad htan
  have hrad' : |⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ +
      2 * v 0 * (ρ θ)⁻¹ ^ 3| ≤ D * (ρ θ)⁻¹ ^ 5 := by
    simpa only [inv_pow, div_eq_mul_inv] using hrad
  have htan' : ‖ρ θ •
      (gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0) -
        ⟪gradient (gradNorm u) (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ • θ) -
      (3 * (ρ θ)⁻¹ ^ 4) •
        (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
          ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ)‖ ≤
        D * (ρ θ)⁻¹ ^ 5 := by
    simpa only [inv_pow, div_eq_mul_inv] using htan
  have hest : ‖fderiv ℝ (levelGradRemainder u v t ρ) θ‖ ≤ A * t ^ 5 :=
    levelGradRemainder_first_derivative_of_radial_tangent_estimates hv0 ht.le htC.le
      hθ hs hρ1 hinv2 (by positivity) (by positivity) hD (by positivity)
      hρd hdu hinv hQbound hρder' hrad' htan'
  exact hest.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end LiquidDrop.CapacitaryK
