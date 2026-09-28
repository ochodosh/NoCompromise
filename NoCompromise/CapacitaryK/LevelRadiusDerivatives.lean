import NoCompromise.CapacitaryK.LevelRadiusSmooth
import NoCompromise.CapacitaryK.LevelRadialArea

/-!
# Angular derivatives of the capacitary level radius

The remainder uses the zero-homogeneous extension of the angular quadrupole.
The value and first derivative estimate is unconditional. The second derivative
estimate is isolated in `LevelRadiusSecondDerivativeBound`; the full conclusion
below is conditional on that explicitly stated, unproved estimate.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The radius error, extended zero-homogeneously away from the origin. -/
def levelRadiusRemainder (v : E3 → ℝ) (t : ℝ) (ρ : E3 → ℝ) (y : E3) : ℝ :=
  ρ y - (v 0 / t + t * kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y) / (v 0) ^ 2)

/-- The angular derivative of a homogeneous quadratic is the tangential part
of the gradient of its degree-minus-three potential. -/
theorem levelRadius_angular_gradient {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {θ : E3} (hθ : ‖θ‖ = 1) :
    DifferentiableAt ℝ (fun y => Q (‖y‖⁻¹ • y)) θ ∧
      gradient (fun y => Q (‖y‖⁻¹ • y)) θ =
        gradient (farQuadrupole Q) θ -
          ⟪gradient (farQuadrupole Q) θ, θ⟫ • θ := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hf := (contDiffAt_farQuadrupole hQ hθ0).differentiableAt (by simp)
  have he : (fun y => ‖y‖ ^ 3 * farQuadrupole Q y) =ᶠ[𝓝 θ]
      (fun y => Q (‖y‖⁻¹ • y)) := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    rw [hQh, farQuadrupole]
    have hn := norm_ne_zero_iff.mpr hy
    field_simp
  have hd := ((levelRadius_hasFDerivAt_norm hθ0).pow 3).mul hf.hasFDerivAt
  have hd' := hd.congr_of_eventuallyEq he.symm
  refine ⟨hd'.differentiableAt, ?_⟩
  have heul := inner_gradient_farQuadrupole hQ hQh hθ0
  rw [real_inner_comm] at heul
  rw [gradient, hd'.fderiv]
  simp only [hθ, one_pow, inv_one, one_smul, map_add, map_smul]
  have hdual : (toDual ℝ E3).symm (innerSL ℝ θ) = θ :=
    (toDual ℝ E3).symm_apply_apply θ
  rw [hdual]
  change gradient (farQuadrupole Q) θ + farQuadrupole Q θ • (3 • (1 : ℝ)) • θ = _
  rw [heul]
  module

/-- Subtracting the angular model differentiates in the ambient punctured space. -/
theorem levelRadiusRemainder_gradient {v : E3 → ℝ} {t : ℝ} {ρ : E3 → ℝ}
    {θ : E3} (hθ : ‖θ‖ = 1) (hρ : DifferentiableAt ℝ ρ θ) :
    gradient (levelRadiusRemainder v t ρ) θ = gradient ρ θ -
      (t / (v 0) ^ 2) • (gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ -
        ⟪gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ, θ⟫ • θ) := by
  obtain ⟨hd, hg⟩ := levelRadius_angular_gradient (translated_quadrupole_contDiff v)
    (kelvinTranslatedQuadrupole_smul v) hθ
  have he : levelRadiusRemainder v t ρ = fun y =>
      ρ y - (v 0 / t + (t / (v 0) ^ 2) *
        kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) := by
    funext y
    dsimp [levelRadiusRemainder]
    ring
  have hfd : fderiv ℝ (fun y => ρ y - (v 0 / t + (t / (v 0) ^ 2) *
      kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y))) θ =
      fderiv ℝ ρ θ - (t / (v 0) ^ 2) •
        fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ :=
    (hρ.hasFDerivAt.sub
      ((hd.hasFDerivAt.const_mul (t / (v 0) ^ 2)).const_add (v 0 / t))).fderiv
  rw [he, gradient, hfd]
  simp only [map_sub, map_smul]
  change gradient ρ θ - (t / (v 0) ^ 2) •
    gradient (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ = _
  rw [hg]

/-- A quantitative scalar inversion estimate for the implicit gradient equation. -/
theorem levelRadius_gradient_error_bound {C D B M ε t a : ℝ} {H Z V : E3}
    (hC : 0 < C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : C / 2 ≤ a) (had : |a - C| ≤ D * ε ^ 2)
    (het : |ε - t / C| ≤ D / C * ε ^ 2)
    (hH : ‖H‖ ≤ 2 * B) (hZ : ‖Z‖ ≤ 2 * M * ε ^ 2)
    (heq : a • V = ε • H + Z) :
    ‖V - (t / C ^ 2) • H‖ ≤
      (2 / C * ((D / C + D / C ^ 2) * (2 * B) + 2 * M)) * ε ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hB : 0 ≤ 2 * B := (norm_nonneg H).trans hH
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
  have hid : a • (V - (t / C ^ 2) • H) = (ε - a * t / C ^ 2) • H + Z := by
    rw [smul_sub, heq, smul_smul]
    module
  have hn : a * ‖V - (t / C ^ 2) • H‖ ≤
      ((D / C + D / C ^ 2) * (2 * B) + 2 * M) * ε ^ 2 := by
    calc
      _ = ‖a • (V - (t / C ^ 2) • H)‖ := by
        rw [norm_smul, Real.norm_of_nonneg ha0.le]
      _ ≤ |ε - a * t / C ^ 2| * ‖H‖ + ‖Z‖ := by
        rw [hid]
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          ((ε - a * t / C ^ 2) • H) Z
      _ ≤ ((D / C + D / C ^ 2) * ε ^ 2) * (2 * B) + 2 * M * ε ^ 2 :=
        add_le_add (mul_le_mul hc hH (norm_nonneg _) ((abs_nonneg _).trans hc)) hZ
      _ = _ := by ring
  have hhalf := mul_le_mul_of_nonneg_right ha (norm_nonneg (V - (t / C ^ 2) • H))
  have hm := mul_le_mul_of_nonneg_left (hhalf.trans hn) (by positivity : 0 ≤ 2 / C)
  have hid' : 2 / C * (C / 2 * ‖V - (t / C ^ 2) • H‖) =
      ‖V - (t / C ^ 2) • H‖ := by field_simp
  rw [hid'] at hm
  simpa only [mul_assoc] using hm

/-- The tangential projection at a unit vector has norm at most twice the original norm. -/
theorem levelRadius_tangent_norm_le {θ w : E3} (hθ : ‖θ‖ = 1) :
    ‖w - ⟪w, θ⟫ • θ‖ ≤ 2 * ‖w‖ := by
  have hi : |⟪w, θ⟫| ≤ ‖w‖ := by simpa [hθ] using abs_real_inner_le_norm w θ
  calc
    _ ≤ ‖w‖ + ‖⟪w, θ⟫ • θ‖ := norm_sub_le _ _
    _ = ‖w‖ + |⟪w, θ⟫| := by rw [norm_smul, hθ, mul_one, Real.norm_eq_abs]
    _ ≤ 2 * ‖w‖ := by linarith

/-- Quantitative first-order implicit differentiation of the exterior expansion. -/
theorem levelRadius_implicit_gradient_estimate {C B M ε t : ℝ} {θ g f w : E3}
    (hC : 0 < C) (hB : 0 ≤ B) (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hθ : ‖θ‖ = 1)
    (hsmall : (B + M) * ε ^ 2 ≤ C / 2)
    (hg : g + (C * ε ^ 2) • θ = ε ^ 4 • f + w)
    (hf : ‖f‖ ≤ B) (hw : ‖w‖ ≤ M * ε ^ 5)
    (hval : |t - C * ε| ≤ (B + M) * ε ^ 3) :
    ⟪g, θ⟫ < 0 ∧
      ‖-(ε⁻¹ / ⟪g, θ⟫) • (g - ⟪g, θ⟫ • θ) -
        (t / C ^ 2) • (f - ⟪f, θ⟫ • θ)‖ ≤
        (2 / C * (((B + M) / C + (B + M) / C ^ 2) * (2 * B) + 2 * M)) * ε ^ 2 := by
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  have h54 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h32 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hpert : ‖g + (C * ε ^ 2) • θ‖ ≤ (B + M) * ε ^ 4 := by
    rw [hg]
    calc
      _ ≤ ‖ε ^ 4 • f‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε ^ 4 * B + M * ε ^ 5 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε ^ 4)]
        gcongr
      _ ≤ (B + M) * ε ^ 4 := by nlinarith
  have hrad : |⟪g, θ⟫ + C * ε ^ 2| ≤ (B + M) * ε ^ 4 := by
    have hi := abs_real_inner_le_norm (g + (C * ε ^ 2) • θ) θ
    simp only [inner_add_left, real_inner_smul_left, hθθ, hθ, mul_one] at hi
    exact hi.trans hpert
  let a := -⟪g, θ⟫ / ε ^ 2
  have had : |a - C| ≤ (B + M) * ε ^ 2 := by
    have he : a - C = -(⟪g, θ⟫ + C * ε ^ 2) / ε ^ 2 := by
      dsimp [a]
      field_simp
      ring
    rw [he, abs_div, abs_neg, abs_of_nonneg (sq_nonneg ε)]
    calc
      _ ≤ ((B + M) * ε ^ 4) / ε ^ 2 :=
        div_le_div_of_nonneg_right hrad (sq_nonneg ε)
      _ = _ := by field_simp
  have ha : C / 2 ≤ a := by have := (abs_le.mp had).1; linarith
  have ha0 : 0 < a := by linarith
  have hd : ⟪g, θ⟫ < 0 := by
    have := (div_pos_iff_of_pos_right (sq_pos_of_pos hε)).mp ha0
    linarith
  refine ⟨hd, ?_⟩
  have het : |ε - t / C| ≤ (B + M) / C * ε ^ 2 := by
    have he : ε - t / C = -(t - C * ε) / C := by field_simp; ring
    rw [he, abs_div, abs_neg, abs_of_pos hC]
    calc
      _ ≤ ((B + M) * ε ^ 3) / C := div_le_div_of_nonneg_right hval hC.le
      _ ≤ ((B + M) * ε ^ 2) / C := by gcongr
      _ = _ := by ring
  have hH : ‖f - ⟪f, θ⟫ • θ‖ ≤ 2 * B :=
    (levelRadius_tangent_norm_le hθ).trans (by linarith)
  have hZ : ‖ε⁻¹ ^ 3 • (w - ⟪w, θ⟫ • θ)‖ ≤ 2 * M * ε ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ε⁻¹ ^ 3)]
    calc
      _ ≤ ε⁻¹ ^ 3 * (2 * (M * ε ^ 5)) := by
        gcongr
        exact (levelRadius_tangent_norm_le hθ).trans (by linarith)
      _ = _ := by field_simp
  have htg : g - ⟪g, θ⟫ • θ =
      ε ^ 4 • (f - ⟪f, θ⟫ • θ) + (w - ⟪w, θ⟫ • θ) := by
    have hg' := eq_sub_of_add_eq hg
    rw [hg']
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hθθ, mul_one]
    module
  apply levelRadius_gradient_error_bound hC ht ht1 ha had het hH hZ
  rw [htg, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have he1 : a * (-(ε⁻¹ / ⟪g, θ⟫)) * ε ^ 4 = ε := by
    dsimp [a]
    field_simp [hd.ne]
  have he2 : a * (-(ε⁻¹ / ⟪g, θ⟫)) = ε⁻¹ ^ 3 := by
    dsimp [a]
    field_simp [hd.ne]
  rw [he1, he2]

/-- The value and first angular derivative of the radius error are uniformly `O(t²)`.
The Kelvin extension is obtained from the translated remainder theorem. -/
theorem capacitary_level_radius_first_derivative
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
          ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ ≤ A * t ^ 2 := by
  obtain ⟨v, r, hr, hv, he, _, hv0, _, hQs, _, _, R, M, hR, hW, hbound⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨v', r', hr', hv', he', _, A, hA, hev⟩ :=
    capacitary_level_radial_graph hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0, hg0, hQ0⟩ := kelvin_extension_data_eq hr' hr hv' hv he' he
  simp only [h0, hg0, hQ0] at hev
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) hQs
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  let W := kelvinTranslatedRemainder u v
  let f := farQuadrupole (kelvinTranslatedQuadrupole v)
  have hUeq : U = fun y => (W y + v 0 / ‖y‖) + f y := by
    funext y
    dsimp [U, W, f, kelvinTranslatedRemainder, farQuadrupole]
    ring
  have hUc : Continuous U := hu.comp (continuous_id.add continuous_const)
  have hUpos : ∀ y, 0 < U y := fun y =>
    capacitary_pos_everywhere hK hzero hu hh hb hinf _
  have hUs : ContDiffOn ℝ (⊤ : ℕ∞) U {y | R < ‖y‖} := by
    intro y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (hR.trans hy)
    rw [hUeq]
    exact (((hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hy)).add
      (contDiffAt_const.div (contDiffAt_norm ℝ hy0) (norm_ne_zero_iff.mpr hy0))).add
        (contDiffAt_farQuadrupole (translated_quadrupole_contDiff v) hy0)).contDiffWithinAt
  have hdecomp (x : E3) (hx : R < ‖x‖) :
      gradient U x + (v 0 / ‖x‖ ^ 3) • x = gradient f x + gradient W x := by
    have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans hx)
    have hdW := (hW.contDiffAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)).differentiableAt (by simp)
    obtain ⟨hdC, hgC⟩ := capacitary_gradient_const_div_norm (v 0) hx0
    have hdf := (contDiffAt_farQuadrupole (translated_quadrupole_contDiff v) hx0)
      |>.differentiableAt (by simp)
    have hfd : fderiv ℝ U x = fderiv ℝ W x +
        fderiv ℝ (fun y : E3 => v 0 / ‖y‖) x + fderiv ℝ f x := by
      rw [hUeq]
      exact ((hdW.hasFDerivAt.add hdC.hasFDerivAt).add hdf.hasFDerivAt).fderiv
    rw [gradient, hfd, map_add, map_add]
    change (gradient W x + gradient (fun y : E3 => v 0 / ‖y‖) x + gradient f x) +
      (v 0 / ‖x‖ ^ 3) • x = _
    rw [hgC]
    module
  have hlim : Tendsto (fun s : ℝ => (B + |M|) / s ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨S, hS, hsmallS⟩ := ((eventually_ge_atTop (max (R + 1) 1)).and
    (hlim.eventually (gt_mem_nhds (by positivity : 0 < v 0 / 2)))).exists
  have hS1 : 1 ≤ S := (le_max_right _ _).trans hS
  have hSR : R < S := by have := (le_max_left _ _).trans hS; linarith
  obtain ⟨y₀, _, hy₀⟩ := (isCompact_closedBall (0 : E3) S).exists_isMinOn
    ⟨0, mem_closedBall_self (by linarith)⟩ hUc.continuousOn
  let L := 2 / v 0 *
    (((B + |M|) / v 0 + (B + |M|) / (v 0) ^ 2) * (2 * B) + 2 * |M|)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨v, r, hr, hv, he, hv0, max A (L * (2 / v 0) ^ 2),
    hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (lt_min one_pos (hUpos y₀))] with t ht htr
  have htpos := htr.1
  have ht1 : t ≤ 1 := htr.2.le.trans (min_le_left _ _)
  have htm : t < U y₀ := htr.2.trans_le (min_le_right _ _)
  intro ρ hhom hroot
  have hpoint : ∀ θ : E3, ‖θ‖ = 1 →
      R < ‖ρ θ • θ‖ ∧ (ρ θ)⁻¹ ≤ 2 * (t / v 0) ∧
        ⟪gradient U (ρ θ • θ), θ⟫ < 0 ∧
        ‖-(ρ θ / ⟪gradient U (ρ θ • θ), θ⟫) •
            (gradient U (ρ θ • θ) - ⟪gradient U (ρ θ • θ), θ⟫ • θ) -
          (t / (v 0) ^ 2) • (gradient f θ - ⟪gradient f θ, θ⟫ • θ)‖ ≤
          L * (ρ θ)⁻¹ ^ 2 := by
    intro θ hθ
    obtain ⟨hs, hut⟩ := hroot θ hθ
    have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
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
    have hε : 0 < (ρ θ)⁻¹ := inv_pos.mpr hs
    have hε1 : (ρ θ)⁻¹ ≤ 1 := by simpa using (inv_le_one₀ hs).mpr hs1
    have hsmall : (B + |M|) * (ρ θ)⁻¹ ^ 2 ≤ v 0 / 2 := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by linarith : 0 ≤ S) hSs.le 2)).trans hsmallS.le
    have hgscale : gradient f (ρ θ • θ) = (ρ θ)⁻¹ ^ 4 • gradient f θ := by
      dsimp [gradient, f]
      rw [fderiv_farQuadrupole_smul hQs hs θ, map_smul, inv_pow]
    have hg := hdecomp (ρ θ • θ) hsR
    rw [hn, hgscale, smul_smul] at hg
    have hc : v 0 / ρ θ ^ 3 * ρ θ = v 0 * (ρ θ)⁻¹ ^ 2 := by field_simp
    rw [hc] at hg
    have hfB : ‖gradient f θ‖ ≤ B := by
      rw [gradient, (toDual ℝ E3).symm.norm_map]
      simpa [hθ] using (hBb θ hθ0).2.1
    obtain ⟨hWv, hWd, _⟩ := hbound (ρ θ • θ) hsR.le
    rw [hn] at hWv hWd
    have hWg : ‖gradient W (ρ θ • θ)‖ ≤ |M| * (ρ θ)⁻¹ ^ 5 := by
      rw [gradient, (toDual ℝ E3).symm.norm_map, inv_pow, ← div_eq_mul_inv]
      exact hWd.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
    have hval : |t - v 0 * (ρ θ)⁻¹| ≤ (B + |M|) * (ρ θ)⁻¹ ^ 3 := by
      have hid : t - v 0 * (ρ θ)⁻¹ = f (ρ θ • θ) + W (ρ θ • θ) := by
        have hUt : U (ρ θ • θ) = t := hut
        rw [hUeq] at hUt
        dsimp only at hUt
        rw [hn, div_eq_mul_inv] at hUt
        linarith
      have hfval := (hBb (ρ θ • θ) (smul_ne_zero hs.ne' hθ0)).1
      rw [hn] at hfval
      have h43 : (ρ θ)⁻¹ ^ 4 ≤ (ρ θ)⁻¹ ^ 3 :=
        pow_le_pow_of_le_one hε.le hε1 (by norm_num)
      rw [hid]
      calc
        _ ≤ |f (ρ θ • θ)| + |W (ρ θ • θ)| := abs_add_le _ _
        _ ≤ B * (ρ θ)⁻¹ ^ 3 + |M| * (ρ θ)⁻¹ ^ 4 := by
          rw [inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv]
          exact add_le_add hfval
            (hWv.trans (div_le_div_of_nonneg_right (le_abs_self M) (by positivity)))
        _ ≤ (B + |M|) * (ρ θ)⁻¹ ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left h43 (abs_nonneg M)]
    have hinv : (ρ θ)⁻¹ ≤ 2 * (t / v 0) := by
      have h1 := (abs_le.mp hval).1
      have h2 := mul_le_mul_of_nonneg_right hsmall hε.le
      rw [show (B + |M|) * (ρ θ)⁻¹ ^ 2 * (ρ θ)⁻¹ =
        (B + |M|) * (ρ θ)⁻¹ ^ 3 by ring] at h2
      rw [← mul_div_assoc, le_div_iff₀ hv0]
      nlinarith
    obtain ⟨hneg, hest⟩ := levelRadius_implicit_gradient_estimate hv0 hB.le (abs_nonneg M)
      hε hε1 htpos.le ht1 hθ hsmall hg hfB hWg hval
    exact ⟨hsR, hinv, hneg, by simpa only [inv_inv] using hest⟩
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} := by
    apply levelRadius_contDiffOn (isOpen_lt continuous_const continuous_norm) hUs hhom
      (fun θ hθ => (hroot θ hθ).1) ?_ (fun θ hθ => (hroot θ hθ).2)
      (fun θ hθ => (hpoint θ hθ).1) (fun θ hθ => (hpoint θ hθ).2.2.1.ne)
    intro θ hθ s hs hut
    obtain ⟨s₀, _, _, _, huniq⟩ := ht θ hθ
    exact (huniq s hs hut).trans
      (huniq (ρ θ) (hroot θ hθ).1 (hroot θ hθ).2).symm
  refine ⟨hsmooth, fun θ hθ => ?_⟩
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  obtain ⟨s, _, _, hs, huniq⟩ := ht θ hθ
  have hρs := huniq (ρ θ) (hroot θ hθ).1 (hroot θ hθ).2
  have hρd := (hsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).differentiableAt (by simp)
  obtain ⟨hmem, hinv, hneg, hest⟩ := hpoint θ hθ
  have hUd := (hUs.contDiffAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hmem)).differentiableAt (by simp)
  have hgrad := levelRadius_gradient hhom (fun θ hθ => (hroot θ hθ).2) hθ hρd hUd hneg.ne
  refine ⟨?_, ?_⟩
  · simpa only [levelRadiusRemainder, hθ, inv_one, one_smul, hρs] using
      hs.trans (mul_le_mul_of_nonneg_right (le_max_left A (L * (2 / v 0) ^ 2))
        (sq_nonneg t))
  · have hnorm : ‖fderiv ℝ (levelRadiusRemainder v t ρ) θ‖ =
        ‖gradient (levelRadiusRemainder v t ρ) θ‖ :=
      ((toDual ℝ E3).symm.norm_map _).symm
    rw [hnorm, levelRadiusRemainder_gradient hθ hρd, hgrad]
    calc
      _ ≤ L * (ρ θ)⁻¹ ^ 2 := hest
      _ ≤ L * (2 * (t / v 0)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr (hroot θ hθ).1.le) hinv 2) hL
      _ = (L * (2 / v 0) ^ 2) * t ^ 2 := by ring
      _ ≤ max A (L * (2 / v 0) ^ 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg t)

/-- The missing uniform second angular derivative estimate for a fixed Kelvin extension.
This is a proposition, not an assertion that the estimate has been proved. -/
def LevelRadiusSecondDerivativeBound (u v : E3 → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ρ : E3 → ℝ,
    (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
    (∀ θ : E3, ‖θ‖ = 1 →
      0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
    ∀ θ : E3, ‖θ‖ = 1 →
      ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤ A * t ^ 2

/-- Conditional assembly of both angular derivative bounds. The only extra input
is the precisely stated second derivative estimate for smooth Kelvin extensions. -/
theorem capacitary_level_radius_derivatives_of_second_derivative_bound
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    (hsecond : ∀ (v : E3 → ℝ) (r : ℝ), 0 < r →
      ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) →
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) → 0 < v 0 →
      LevelRadiusSecondDerivativeBound u v) :
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
  obtain ⟨v, r, hr, hv, he, hv0, A, hA, hev⟩ :=
    capacitary_level_radius_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨B, _, hevB⟩ := hsecond v r hr hv he hv0
  refine ⟨v, r, hr, hv, he, hv0, max A B, hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [hev, hevB] with t ht htB
  intro ρ hhom hroot
  obtain ⟨hs, hbds⟩ := ht ρ hhom hroot
  refine ⟨hs, fun θ hθ => ?_⟩
  obtain ⟨hval, hfirst⟩ := hbds θ hθ
  have hA' := mul_le_mul_of_nonneg_right (le_max_left A B) (sq_nonneg t)
  have hB' := mul_le_mul_of_nonneg_right (le_max_right A B) (sq_nonneg t)
  exact ⟨hval.trans hA', hfirst.trans hA', (htB ρ hhom hroot θ hθ).trans hB'⟩

end LiquidDrop.CapacitaryK
