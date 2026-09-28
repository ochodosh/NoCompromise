import NoCompromise.Capacity.LevelRadiusDeriv
import NoCompromise.CapacitaryK.LevelRadiusSecondDerivative

/-!
# Uniform second angular derivatives of small capacitary levels

The radius is extended homogeneously with degree zero away from the origin.
The leading Coulomb terms cancel in the twice differentiated level equation.
-/

noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Convert the vector gradient and Hessian errors into Fréchet derivative errors. -/
lemma levelRadius_monopole_derivative_errors {u : E₃ → ℝ} {x : E₃} (hx : x ≠ 0)
    {C B₁ B₂ : ℝ}
    (hg : ‖gradient u x + (C / ‖x‖ ^ 3) • x‖ ≤ B₁)
    (hH : ‖fderiv ℝ (gradient u) x -
      ((3 * C / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
        (C / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ B₂) :
    ‖fderiv ℝ u x - fderiv ℝ (fun y : E₃ => C / ‖y‖) x‖ ≤ B₁ ∧
      ‖fderiv ℝ (fderiv ℝ u) x -
        fderiv ℝ (fderiv ℝ (fun y : E₃ => C / ‖y‖)) x‖ ≤ B₂ := by
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans hg
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans hH
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ hB₁
    intro w
    have he : (fderiv ℝ u x - fderiv ℝ (fun y : E₃ => C / ‖y‖) x) w =
        ⟪gradient u x + (C / ‖x‖ ^ 3) • x, w⟫ := by
      rw [sub_apply, ← CapacitaryK.inner_gradient_eq_fderiv u,
        (CapacitaryK.hasFDerivAt_monopole C hx).fderiv]
      simp [inner_add_left, real_inner_smul_left, neg_div]
    rw [he, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hg (norm_nonneg w))
  · apply ContinuousLinearMap.opNorm_le_bound _ hB₂
    intro e
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    have hG : fderiv ℝ (gradient u) x e =
        (toDual ℝ E₃).symm (fderiv ℝ (fderiv ℝ u) x e) := by
      change fderiv ℝ ((toDual ℝ E₃).symm ∘ fderiv ℝ u) x e = _
      rw [(toDual ℝ E₃).symm.comp_fderiv]
      rfl
    let A := (3 * C / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
      (C / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃
    have he : (fderiv ℝ (fderiv ℝ u) x -
        fderiv ℝ (fderiv ℝ (fun y : E₃ => C / ‖y‖)) x) e f =
          ⟪(fderiv ℝ (gradient u) x - A) e, f⟫ := by
      simp only [sub_apply, CapacitaryK.fderiv_two_monopole C hx, inner_sub_left, hG,
        toDual_symm_apply]
      dsimp [A]
      simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_sub_left,
        real_inner_smul_left]
      ring
    rw [he, Real.norm_eq_abs]
    exact (levelAsymp_abs_inner_le _ e f).trans
      (by gcongr)

/-- The residual in the Coulomb-cancelled Hessian equation is uniformly bounded. -/
lemma levelRadius_second_residual_bound {s C D P a b : ℝ}
    (hs : 1 ≤ s) (hD : 0 ≤ D) (hP : 0 ≤ P)
    {θ e f : E₃} (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (ha : |a| ≤ P) (hb : |b| ≤ P)
    (dw : E₃ →L[ℝ] ℝ) (hw : E₃ →L[ℝ] E₃ →L[ℝ] ℝ)
    (hdw : ‖dw‖ ≤ D / s ^ 3) (hhw : ‖hw‖ ≤ D / s ^ 4) :
    let T : E₃ → E₃ := fun w => w - ⟪θ, w⟫ • θ
    let N := (3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e
    |2 * C * s⁻¹ * a * b + s ^ 2 * hw (a • θ + s • T e) (b • θ + s • T f) +
        s ^ 2 * a * dw (T f) + s ^ 2 * b * dw (T e) + s ^ 3 * dw N| ≤
      2 * |C| * P ^ 2 + D * (P + 2) ^ 2 + 4 * D * P + 6 * D := by
  dsimp only
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hTe : ‖e - ⟪θ, e⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ e, he, mul_one] using
      (CapacitaryK.levelRadius_tangent_norm_le (w := e) hθ)
  have hTf : ‖f - ⟪θ, f⟫ • θ‖ ≤ 2 := by
    simpa only [real_inner_comm θ f, hf, mul_one] using
      (CapacitaryK.levelRadius_tangent_norm_le (w := f) hθ)
  have hN := CapacitaryK.levelRadius_normalize_fderiv_two_bound hθ he hf
  have hA : ‖a • θ + s • (e - ⟪θ, e⟫ • θ)‖ ≤ (P + 2) * s := by
    calc
      _ ≤ ‖a • θ‖ + ‖s • (e - ⟪θ, e⟫ • θ)‖ := norm_add_le _ _
      _ ≤ P + s * 2 := by
        simp only [norm_smul, Real.norm_eq_abs, hθ, mul_one, abs_of_pos hs0]
        gcongr
      _ ≤ (P + 2) * s := by nlinarith
  have hA' : ‖b • θ + s • (f - ⟪θ, f⟫ • θ)‖ ≤ (P + 2) * s := by
    calc
      _ ≤ ‖b • θ‖ + ‖s • (f - ⟪θ, f⟫ • θ)‖ := norm_add_le _ _
      _ ≤ P + s * 2 := by
        simp only [norm_smul, Real.norm_eq_abs, hθ, mul_one, abs_of_pos hs0]
        gcongr
      _ ≤ (P + 2) * s := by nlinarith
  have h0 : |2 * C * s⁻¹ * a * b| ≤ 2 * |C| * P ^ 2 := by
    calc
      _ ≤ 2 * |C| * s⁻¹ * P * P := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_inv, abs_of_pos hs0]
        gcongr
      _ = (2 * |C| * P ^ 2) / s := by ring
      _ ≤ _ := div_le_self (by positivity) hs
  have h1 : |s ^ 2 * hw (a • θ + s • (e - ⟪θ, e⟫ • θ))
      (b • θ + s • (f - ⟪θ, f⟫ • θ))| ≤ D * (P + 2) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ s ^ 2 * (‖hw‖ * ‖a • θ + s • (e - ⟪θ, e⟫ • θ)‖ *
          ‖b • θ + s • (f - ⟪θ, f⟫ • θ)‖) := by
        gcongr
        exact hw.le_opNorm₂ _ _
      _ ≤ s ^ 2 * ((D / s ^ 4) * ((P + 2) * s) * ((P + 2) * s)) := by
        gcongr
      _ = _ := by field_simp
  have h2 : |s ^ 2 * a * dw (f - ⟪θ, f⟫ • θ)| ≤ 2 * D * P := by
    simp only [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ s ^ 2 * P * (‖dw‖ * ‖f - ⟪θ, f⟫ • θ‖) := by
        gcongr
        exact dw.le_opNorm _
      _ ≤ s ^ 2 * P * ((D / s ^ 3) * 2) := by gcongr
      _ = (2 * D * P) / s := by field_simp
      _ ≤ _ := div_le_self (by positivity) hs
  have h3 : |s ^ 2 * b * dw (e - ⟪θ, e⟫ • θ)| ≤ 2 * D * P := by
    simp only [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ s ^ 2 * P * (‖dw‖ * ‖e - ⟪θ, e⟫ • θ‖) := by
        gcongr
        exact dw.le_opNorm _
      _ ≤ s ^ 2 * P * ((D / s ^ 3) * 2) := by gcongr
      _ = (2 * D * P) / s := by field_simp
      _ ≤ _ := div_le_self (by positivity) hs
  have h4 : |s ^ 3 * dw ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
      ⟪θ, e⟫ • f - ⟪θ, f⟫ • e)| ≤ 6 * D := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hs0.le 3)]
    calc
      _ ≤ s ^ 3 * (‖dw‖ * ‖(3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
          ⟪θ, e⟫ • f - ⟪θ, f⟫ • e‖) := by
        gcongr
        exact dw.le_opNorm _
      _ ≤ s ^ 3 * ((D / s ^ 3) * 6) := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ |2 * C * s⁻¹ * a * b| +
        |s ^ 2 * hw (a • θ + s • (e - ⟪θ, e⟫ • θ))
          (b • θ + s • (f - ⟪θ, f⟫ • θ))| +
        |s ^ 2 * a * dw (f - ⟪θ, f⟫ • θ)| +
        |s ^ 2 * b * dw (e - ⟪θ, e⟫ • θ)| +
        |s ^ 3 * dw ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
          ⟪θ, e⟫ • f - ⟪θ, f⟫ • e)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith only [h0, h1, h2, h3, h4]

/-- Second implicit differentiation gives a uniform Hessian bound from Coulomb errors. -/
lemma levelRadius_implicit_second_bound {u ρ : E₃ → ℝ} {t C D P : ℝ}
    (hC : 0 < C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hhom : ∀ y : E₃, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E₃, ‖θ‖ = 1 → u (ρ θ • θ) = t)
    {θ : E₃} (hθ : ‖θ‖ = 1) (hs : 1 ≤ ρ θ)
    (hρ : ContDiffAt ℝ 2 ρ θ) (hu : ContDiffAt ℝ 2 u (ρ θ • θ))
    (hd : ‖fderiv ℝ u (ρ θ • θ) -
      fderiv ℝ (fun y : E₃ => C / ‖y‖) (ρ θ • θ)‖ ≤ D / (ρ θ) ^ 3)
    (hdd : ‖fderiv ℝ (fderiv ℝ u) (ρ θ • θ) -
      fderiv ℝ (fderiv ℝ (fun y : E₃ => C / ‖y‖)) (ρ θ • θ)‖ ≤ D / (ρ θ) ^ 4)
    (hp : ‖fderiv ℝ ρ θ‖ ≤ P) (hsmall : D / ρ θ ≤ C / 2) :
    ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤
      2 / C * (2 * |C| * P ^ 2 + D * (P + 2) ^ 2 + 4 * D * P + 6 * D) := by
  have hs0 : 0 < ρ θ := zero_lt_one.trans_le hs
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hx : ρ θ • θ ≠ 0 := smul_ne_zero hs0.ne' hθ0
  have hn : ‖ρ θ • θ‖ = ρ θ := by simp [norm_smul, abs_of_pos hs0, hθ]
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  let dw := fderiv ℝ u (ρ θ • θ) -
    fderiv ℝ (fun y : E₃ => C / ‖y‖) (ρ θ • θ)
  let hw := fderiv ℝ (fderiv ℝ u) (ρ θ • θ) -
    fderiv ℝ (fderiv ℝ (fun y : E₃ => C / ‖y‖)) (ρ θ • θ)
  have hd' : fderiv ℝ u (ρ θ • θ) =
      fderiv ℝ (fun y : E₃ => C / ‖y‖) (ρ θ • θ) + dw := by dsimp [dw]; abel
  have hdd' : fderiv ℝ (fderiv ℝ u) (ρ θ • θ) =
      fderiv ℝ (fderiv ℝ (fun y : E₃ => C / ‖y‖)) (ρ θ • θ) + hw := by
    dsimp [hw]; abel
  let a := -(ρ θ) ^ 2 * fderiv ℝ u (ρ θ • θ) θ
  have had : |a - C| ≤ D / ρ θ := by
    have hid : a - C = -(ρ θ) ^ 2 * dw θ := by
      dsimp [a]
      rw [hd', (CapacitaryK.hasFDerivAt_monopole C hx).fderiv]
      simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
        real_inner_smul_left, hθθ, mul_one, hn]
      field_simp
      ring
    have hdθ : |dw θ| ≤ D / (ρ θ) ^ 3 := by
      simpa only [hθ, mul_one, Real.norm_eq_abs] using (dw.le_opNorm θ).trans
        (mul_le_mul_of_nonneg_right hd (norm_nonneg θ))
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (ρ θ))]
    calc
      _ ≤ (ρ θ) ^ 2 * (D / (ρ θ) ^ 3) := by gcongr
      _ = _ := by field_simp
  have ha : C / 2 ≤ a := by linarith [(abs_le.mp had).1]
  let L := 2 * |C| * P ^ 2 + D * (P + 2) ^ 2 + 4 * D * P + 6 * D
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hres : ‖a • fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hL
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hL
    intro f hf
    have hpe : |fderiv ℝ ρ θ e| ≤ P := by
      simpa only [he, mul_one, Real.norm_eq_abs] using
        ((fderiv ℝ ρ θ).le_opNorm e).trans
          (mul_le_mul_of_nonneg_right hp (norm_nonneg e))
    have hpf : |fderiv ℝ ρ θ f| ≤ P := by
      simpa only [hf, mul_one, Real.norm_eq_abs] using
        ((fderiv ℝ ρ θ).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hp (norm_nonneg f))
    have hid :
        a * fderiv ℝ (fderiv ℝ ρ) θ e f =
          2 * C * (ρ θ)⁻¹ * fderiv ℝ ρ θ e * fderiv ℝ ρ θ f +
          (ρ θ) ^ 2 * hw
            (fderiv ℝ ρ θ e • θ + ρ θ • (e - ⟪θ, e⟫ • θ))
            (fderiv ℝ ρ θ f • θ + ρ θ • (f - ⟪θ, f⟫ • θ)) +
          (ρ θ) ^ 2 * fderiv ℝ ρ θ e * dw (f - ⟪θ, f⟫ • θ) +
          (ρ θ) ^ 2 * fderiv ℝ ρ θ f * dw (e - ⟪θ, e⟫ • θ) +
          (ρ θ) ^ 3 * dw ((3 * ⟪θ, e⟫ * ⟪θ, f⟫ - ⟪e, f⟫) • θ -
            ⟪θ, e⟫ • f - ⟪θ, f⟫ • e) := by
      have hi := CapacitaryK.levelRadius_implicit_fderiv_two hhom hroot hθ hρ hu e f
      have hm := CapacitaryK.levelRadius_monopole_cancellation hθ hs0 C
        (fderiv ℝ ρ θ e) (fderiv ℝ ρ θ f) e f
      dsimp only at hi hm
      rw [hd', hdd'] at hi
      dsimp only [a]
      rw [hd']
      simp only [add_apply] at hi ⊢
      linear_combination (norm := (field_simp; ring))
        -(ρ θ) ^ 2 * hi + (ρ θ) ^ 2 * hm
    simp only [smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [hid]
    exact levelRadius_second_residual_bound hs hD hP hθ he hf hpe hpf dw hw hd hdd
  have hnorm : ‖a • fderiv ℝ (fderiv ℝ ρ) θ‖ =
      a * ‖fderiv ℝ (fderiv ℝ ρ) θ‖ := by
    have ha0 : 0 ≤ a := by linarith
    exact norm_smul_of_nonneg ha0 (fderiv ℝ (fderiv ℝ ρ) θ)
  rw [hnorm] at hres
  have hhalf := mul_le_mul_of_nonneg_right ha (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) θ))
  have hm := mul_le_mul_of_nonneg_left (hhalf.trans hres) (by positivity : 0 ≤ 2 / C)
  have he : 2 / C * (C / 2 * ‖fderiv ℝ (fderiv ℝ ρ) θ‖) =
      ‖fderiv ℝ (fderiv ℝ ρ) θ‖ := by field_simp
  rw [he] at hm
  exact hm

/-- Blueprint `lem:level-asymptotics`: small capacitary levels have a zero-homogeneous
radius with uniformly bounded first and second ambient derivatives on the unit sphere.
The same coefficient at infinity occurs in the value and gradient-length expansions. -/
theorem capacitary_level_radius_fderiv_two_bound
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, θ ≠ 0 → ρ θ = ρ (‖θ‖⁻¹ • θ)) ∧
          (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ M) ∧
          {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} ∧
          (∀ x : E₃, u x = ε →
            gradient u x ≠ 0 ∧ |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3) ∧
          ∀ θ : E₃, ‖θ‖ = 1 →
            ‖fderiv ℝ ρ θ‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ M := by
  obtain ⟨Cinf, hC, ⟨R, C', hR, hexp⟩, ε₀, hε₀, -, M, hM⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = R + 2 * (|C'| + 1) / Cinf + 1 + |M| := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ := capacitary_potential_contDiffOn hK hu hh
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  let P := 4 * |C'| / Cinf
  let B := 2 / Cinf *
    (2 * |Cinf| * P ^ 2 + |C'| * (P + 2) ^ 2 + 4 * |C'| * P + 6 * |C'|)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨Cinf, hC, ⟨R, C', hR, fun x hx => (hexp x hx).1⟩, min ε₀ (Cinf / T),
    lt_min hε₀ (div_pos hC hTpos), max M (max P B), fun ε hε hεε₀ => ?_⟩
  have hε₀' : ε < ε₀ := hεε₀.trans_le (min_le_left _ _)
  have hεT : T < Cinf / ε := by
    have := hεε₀.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hε]; rw [lt_div_iff₀ hTpos] at this; linarith
  obtain ⟨⟨ρ, hρs, hρb, hρeq⟩, hpt, -, -⟩ := hM ε hε hε₀'
  have hMM : M ≤ max M (max P B) := le_max_left _ _
  have hPM : P ≤ max M (max P B) := (le_max_left _ _).trans (le_max_right _ _)
  have hBM : B ≤ max M (max P B) := (le_max_right _ _).trans (le_max_right _ _)
  have hunit : ∀ θ : E₃, ‖θ‖ = 1 → R + 2 * (|C'| + 1) / Cinf + 1 ≤ ρ θ := by
    intro θ hθ
    have := (abs_le.mp (hρb θ hθ)).1
    have := le_abs_self M
    linarith
  have hunitpos : ∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ := fun θ hθ =>
    lt_of_lt_of_le (by positivity) (hunit θ hθ)
  have hPP : ∀ θ : E₃, θ ≠ 0 →
      ‖‖θ‖⁻¹ • θ‖⁻¹ • (‖θ‖⁻¹ • θ) = ‖θ‖⁻¹ • θ := by
    intro θ hθ; rw [kelvin_norm_direction hθ, inv_one, one_smul]
  let ρ' : E₃ → ℝ := fun θ => ρ (‖θ‖⁻¹ • θ)
  have hhom : ∀ θ : E₃, θ ≠ 0 → ρ' θ = ρ' (‖θ‖⁻¹ • θ) := by
    intro θ hθ
    dsimp only [ρ']
    rw [hPP θ hθ]
  have hlev : ∀ θ : E₃, θ ≠ 0 →
      ρ' θ • (‖θ‖⁻¹ • θ) ∉ K ∧ u (ρ' θ • (‖θ‖⁻¹ • θ)) = ε := by
    intro θ hθ
    have hd := kelvin_norm_direction hθ
    have hp := hunitpos _ hd
    have hn : ‖ρ' θ • (‖θ‖⁻¹ • θ)‖ = ρ' θ := by
      rw [norm_smul, hd, mul_one, Real.norm_of_nonneg hp.le]
    have hmem : ρ' θ • (‖θ‖⁻¹ • θ) ∈
        {x : E₃ | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} := by
      refine ⟨?_, ?_⟩
      · intro h0; rw [h0, norm_zero] at hn; exact hp.ne' hn.symm
      · rw [hn, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    rw [← hρeq] at hmem
    exact hmem
  have hroot : ∀ θ : E₃, ‖θ‖ = 1 → u (ρ' θ • θ) = ε := by
    intro θ hθ
    have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
    simpa only [hθ, inv_one, one_smul] using (hlev θ hθ0).2
  have hdirsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E₃ => ‖y‖⁻¹ • y) {θ | θ ≠ 0} :=
    fun θ hθ => (CapacitaryK.levelRadius_normalize_contDiffAt hθ).contDiffWithinAt
  have hρ'sm : ContDiffOn ℝ (⊤ : ℕ∞) ρ' {θ | θ ≠ 0} :=
    hρs.comp hdirsm (fun θ hθ => by
      have := kelvin_norm_direction (show θ ≠ 0 from hθ)
      intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨ρ', hρ'sm, hhom, fun θ hθ => ?_, ?_, fun x hx => ?_, fun θ₀ h1 => ?_⟩
  · simp only [ρ', hθ, inv_one, one_smul]
    exact (hρb θ hθ).trans hMM
  · rw [hρeq]
    ext x
    simp only [Set.mem_ofPred_eq, ρ']
    constructor
    · rintro ⟨hx0, hx⟩; exact ⟨hx0, by rw [hPP x hx0]; exact hx⟩
    · rintro ⟨hx0, hx⟩; exact ⟨hx0, by rw [hPP x hx0] at hx; exact hx⟩
  · obtain ⟨_, h2, _, h4, _⟩ := hpt x hx
    exact ⟨h2, h4.trans (mul_le_mul_of_nonneg_right hMM (by positivity))⟩
  have hθ0 : θ₀ ≠ 0 := by rintro rfl; simp at h1
  have hP0 : ‖θ₀‖⁻¹ • θ₀ = θ₀ := by rw [h1, inv_one, one_smul]
  have hρ0 : ρ' θ₀ = ρ θ₀ := by simp only [ρ', hP0]
  have hbig := hunit θ₀ h1
  rw [← hρ0] at hbig
  have hρ₀pos : 0 < ρ' θ₀ := lt_of_lt_of_le (by positivity) hbig
  have hlarge : 1 ≤ ρ' θ₀ := by
    have : 0 ≤ 2 * (|C'| + 1) / Cinf := by positivity
    linarith
  obtain ⟨hx₀K, hx₀ε⟩ := hlev θ₀ hθ0
  rw [hP0] at hx₀K hx₀ε
  have hρ₂ : ContDiffAt ℝ 2 ρ' θ₀ :=
    (hρ'sm.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  have hu₂ : ContDiffAt ℝ 2 u (ρ' θ₀ • θ₀) :=
    (hsm.contDiffAt (hopen.mem_nhds hx₀K)).of_le (by simp)
  have hev : ∀ᶠ θ in 𝓝 θ₀, u (ρ' θ • (‖θ‖⁻¹ • θ)) = ε :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hθ0) (fun θ hθ => (hlev θ hθ).2)
  have hn₀ : ‖ρ' θ₀ • θ₀‖ = ρ' θ₀ := by
    rw [norm_smul, h1, mul_one, Real.norm_of_nonneg hρ₀pos.le]
  have hR' : R ≤ ‖ρ' θ₀ • θ₀‖ := by
    rw [hn₀]; have : 0 ≤ 2 * (|C'| + 1) / Cinf := by positivity
    linarith
  have hsmall : |C'| / ρ' θ₀ ≤ Cinf / 2 := by
    have h2 : 2 * (|C'| + 1) / Cinf ≤ ρ' θ₀ := by linarith
    rw [div_le_iff₀ hC] at h2
    rw [div_le_iff₀ hρ₀pos]
    nlinarith
  have hp : ‖fderiv ℝ ρ' θ₀‖ ≤ P := by
    have hg := (hexp _ hR').2.1
    rw [hn₀] at hg
    simp only [div_eq_mul_inv, ← inv_pow] at hg
    have hsC : C' * (ρ' θ₀)⁻¹ ≤ Cinf / 2 := by
      rw [← div_eq_mul_inv]
      exact (div_le_div_of_nonneg_right (le_abs_self C') hρ₀pos.le).trans hsmall
    apply ContinuousLinearMap.opNorm_le_bound _ hP
    intro v
    have hid := levelRadius_implicit_identity h1
      (hρ₂.differentiableAt (by norm_num)) (hu₂.differentiableAt (by norm_num)) hev v
    have hcore := levelRadius_fderiv_bound_core hC h1 hρ₀pos hsC hg hid
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 4 * C' / Cinf * ‖v‖ := hcore
      _ ≤ P * ‖v‖ := by dsimp [P]; gcongr; exact le_abs_self C'
  refine ⟨hp.trans hPM, ?_⟩
  obtain ⟨hd, hdd⟩ := levelRadius_monopole_derivative_errors
    (smul_ne_zero hρ₀pos.ne' hθ0) (hexp _ hR').2.1 (hexp _ hR').2.2
  rw [hn₀] at hd hdd
  have hd' := hd.trans
    (div_le_div_of_nonneg_right (le_abs_self C') (pow_nonneg hρ₀pos.le 3))
  have hdd' := hdd.trans
    (div_le_div_of_nonneg_right (le_abs_self C') (pow_nonneg hρ₀pos.le 4))
  exact (levelRadius_implicit_second_bound hC (abs_nonneg C') hP hhom hroot h1
    hlarge hρ₂ hu₂ hd' hdd' hp hsmall).trans hBM

end LiquidDrop
