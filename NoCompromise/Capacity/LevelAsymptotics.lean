module

public import NoCompromise.Capacity.KelvinLevels
public import NoCompromise.Capacity.KelvinHessian
public import NoCompromise.Capacity.FluxLevel
public import NoCompromise.CapacitaryK.LevelFrame
public import NoCompromise.CapacitaryK.LevelInequality

@[expose] public section

/-!
# Asymptotics of small capacitary levels (blueprint `lem:level-asymptotics`)

With `s = |x|⁻¹` on the level `{u = ε}`, the Kelvin value, gradient and Hessian
expansions (all with the same coefficient `Cinf`) give
`w = ε² / Cinf + O(ε³)`, `H = 2ε / Cinf + O(ε²)`, and, integrating against the
flux identity `∫ w = 4π Cinf`, `∫ (H w - 4 ε⁻¹ w²) = -8π ε + O(ε²)`.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Scalar core of `lem:level-asymptotics` for `w`. -/
lemma levelAsymp_real_gradNorm {Cinf C' a ε s w : ℝ} (hC : 0 < Cinf) (ha : 0 < a)
    (hs : 0 < s) (hε1 : ε ≤ 1) (hεs : a * s ≤ ε)
    (hval : |ε - Cinf * s| ≤ C' * s ^ 2) (hw : |w - Cinf * s ^ 2| ≤ C' * s ^ 3) :
    |w - ε ^ 2 / Cinf| ≤
      (C' * a⁻¹ ^ 3 + C' * a⁻¹ ^ 2 * (C' * a⁻¹ ^ 2 + 2) / Cinf) * ε ^ 3 := by
  have hC' : 0 ≤ C' := by nlinarith [abs_nonneg (ε - Cinf * s), sq_pos_of_pos hs]
  have hε : 0 < ε := lt_of_lt_of_le (mul_pos ha hs) hεs
  have hsb : s ≤ a⁻¹ * ε := by
    rw [inv_mul_eq_div, le_div_iff₀ ha]; linarith
  have hb : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hs2 : s ^ 2 ≤ a⁻¹ ^ 2 * ε ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs.le hsb 2
  have hs3 : s ^ 3 ≤ a⁻¹ ^ 3 * ε ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs.le hsb 3
  have hd : |Cinf * s - ε| ≤ C' * a⁻¹ ^ 2 * ε ^ 2 := by
    rw [abs_sub_comm]
    calc _ ≤ C' * s ^ 2 := hval
      _ ≤ C' * (a⁻¹ ^ 2 * ε ^ 2) := mul_le_mul_of_nonneg_left hs2 hC'
      _ = _ := by ring
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hp : |Cinf * s + ε| ≤ (C' * a⁻¹ ^ 2 + 2) * ε := by
    have : Cinf * s + ε = (Cinf * s - ε) + 2 * ε := by ring
    rw [this]
    calc _ ≤ |Cinf * s - ε| + |2 * ε| := abs_add_le _ _
      _ ≤ C' * a⁻¹ ^ 2 * ε ^ 2 + 2 * ε := by
          rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * ε)]; linarith
      _ ≤ C' * a⁻¹ ^ 2 * ε + 2 * ε := by
          have : 0 ≤ C' * a⁻¹ ^ 2 := by positivity
          nlinarith
      _ = _ := by ring
  have hsplit : w - ε ^ 2 / Cinf =
      (w - Cinf * s ^ 2) + (Cinf * s - ε) * (Cinf * s + ε) / Cinf := by
    field_simp; ring
  rw [hsplit]
  calc _ ≤ |w - Cinf * s ^ 2| + |(Cinf * s - ε) * (Cinf * s + ε) / Cinf| := abs_add_le _ _
    _ = |w - Cinf * s ^ 2| + |Cinf * s - ε| * |Cinf * s + ε| / Cinf := by
        rw [abs_div, abs_mul, abs_of_pos hC]
    _ ≤ C' * (a⁻¹ ^ 3 * ε ^ 3) +
          (C' * a⁻¹ ^ 2 * ε ^ 2) * ((C' * a⁻¹ ^ 2 + 2) * ε) / Cinf := by
        gcongr
        · exact hw.trans (mul_le_mul_of_nonneg_left hs3 hC')
    _ = _ := by ring

/-- Scalar core of `lem:level-asymptotics` for `H = w⁻³ D²u(∇u, ∇u)`. -/
lemma levelAsymp_real_meanCurv {Cinf C' A s w N : ℝ} (hC : 0 < Cinf) (hs : 0 < s)
    (hs1 : s ≤ 1) (hsC : C' * s ≤ Cinf / 2)
    (hw : |w - Cinf * s ^ 2| ≤ C' * s ^ 3) (hN : |N - 2 * Cinf ^ 3 * s ^ 7| ≤ A * s ^ 8) :
    |(w ^ 3)⁻¹ * N - 2 * s| ≤ 8 * (A + 6 * C' * (Cinf + C') ^ 2) / Cinf ^ 3 * s ^ 2 := by
  have hC' : 0 ≤ C' := by nlinarith [abs_nonneg (w - Cinf * s ^ 2), pow_pos hs 3]
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  have hs32 : s ^ 3 ≤ s ^ 2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
  have hwlo : Cinf * s ^ 2 / 2 ≤ w := by nlinarith [sq_nonneg s]
  have hwhi : w ≤ (Cinf + C') * s ^ 2 := by nlinarith
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hwlo
  have hfac : 0 ≤ w ^ 2 + w * (Cinf * s ^ 2) + (Cinf * s ^ 2) ^ 2 := by positivity
  have hfac2 : w ^ 2 + w * (Cinf * s ^ 2) + (Cinf * s ^ 2) ^ 2 ≤
      3 * ((Cinf + C') ^ 2 * s ^ 4) := by
    have h1 : Cinf * s ^ 2 ≤ (Cinf + C') * s ^ 2 := by nlinarith [sq_nonneg s]
    have h0 : 0 ≤ Cinf * s ^ 2 := by positivity
    have e : (Cinf + C') ^ 2 * s ^ 4 = ((Cinf + C') * s ^ 2) ^ 2 := by ring
    rw [e]
    nlinarith [mul_le_mul hwhi hwhi hwpos.le (h0.trans h1),
      mul_le_mul hwhi h1 h0 (h0.trans h1), mul_le_mul h1 h1 h0 (h0.trans h1)]
  have hcube : |w ^ 3 - Cinf ^ 3 * s ^ 6| ≤ 3 * C' * (Cinf + C') ^ 2 * s ^ 7 := by
    have e : w ^ 3 - Cinf ^ 3 * s ^ 6 =
        (w - Cinf * s ^ 2) * (w ^ 2 + w * (Cinf * s ^ 2) + (Cinf * s ^ 2) ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg hfac]
    calc _ ≤ (C' * s ^ 3) * (3 * ((Cinf + C') ^ 2 * s ^ 4)) :=
          mul_le_mul hw hfac2 hfac (by positivity)
      _ = _ := by ring
  have hnum : |N - 2 * s * w ^ 3| ≤ (A + 6 * C' * (Cinf + C') ^ 2) * s ^ 8 := by
    have e : N - 2 * s * w ^ 3 =
        (N - 2 * Cinf ^ 3 * s ^ 7) - 2 * s * (w ^ 3 - Cinf ^ 3 * s ^ 6) := by ring
    rw [e]
    calc _ ≤ |N - 2 * Cinf ^ 3 * s ^ 7| + |2 * s * (w ^ 3 - Cinf ^ 3 * s ^ 6)| :=
          abs_sub _ _
      _ = |N - 2 * Cinf ^ 3 * s ^ 7| + 2 * s * |w ^ 3 - Cinf ^ 3 * s ^ 6| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * s)]
      _ ≤ A * s ^ 8 + 2 * s * (3 * C' * (Cinf + C') ^ 2 * s ^ 7) := by
          gcongr
      _ = _ := by ring
  have hw3 : Cinf ^ 3 * s ^ 6 / 8 ≤ w ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hwlo 3
    calc _ = (Cinf * s ^ 2 / 2) ^ 3 := by ring
      _ ≤ _ := this
  have hw3pos : 0 < w ^ 3 := pow_pos hwpos 3
  have e : (w ^ 3)⁻¹ * N - 2 * s = (N - 2 * s * w ^ 3) / w ^ 3 := by
    field_simp
  rw [e, abs_div, abs_of_pos hw3pos, div_le_iff₀ hw3pos]
  have hB : 0 ≤ 8 * (A + 6 * C' * (Cinf + C') ^ 2) / Cinf ^ 3 * s ^ 2 := by
    have hA : 0 ≤ A := by nlinarith [abs_nonneg (N - 2 * Cinf ^ 3 * s ^ 7), pow_pos hs 8]
    positivity
  calc _ ≤ (A + 6 * C' * (Cinf + C') ^ 2) * s ^ 8 := hnum
    _ = 8 * (A + 6 * C' * (Cinf + C') ^ 2) / Cinf ^ 3 * s ^ 2 * (Cinf ^ 3 * s ^ 6 / 8) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw3 hB

lemma levelAsymp_abs_inner_le (T : E₃ →L[ℝ] E₃) (v w : E₃) :
    |⟪T v, w⟫| ≤ ‖T‖ * ‖v‖ * ‖w‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg w))

lemma levelAsymp_mul3_le {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') : a * b * c ≤ a' * b' * c' :=
  mul_le_mul (mul_le_mul h1 h2 hb (ha.trans h1)) h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))

/-- Vector core: the Hessian quadratic form on the gradient, against the monopole model. -/
lemma levelAsymp_vec_quadratic {Cinf C' s : ℝ} {x g : E₃} {T : E₃ →L[ℝ] E₃}
    (hC : 0 < Cinf) (hs : 0 < s) (hs1 : s ≤ 1) (hx : ‖x‖ * s = 1)
    (hg : ‖g + (Cinf * s ^ 3) • x‖ ≤ C' * s ^ 3)
    (hT : ‖T - ((3 * Cinf * s ^ 5) • (innerSL ℝ x).smulRight x -
      (Cinf * s ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' * s ^ 4) :
    |⟪T g, g⟫ - 2 * Cinf ^ 3 * s ^ 7| ≤
      (C' * (Cinf + C') ^ 2 + 4 * Cinf * (2 * Cinf + C') * C') * s ^ 8 := by
  have hC' : 0 ≤ C' := by nlinarith [norm_nonneg (g + (Cinf * s ^ 3) • x), pow_pos hs 3]
  set g₀ : E₃ := -((Cinf * s ^ 3) • x) with hg₀
  set T₀ : E₃ →L[ℝ] E₃ := (3 * Cinf * s ^ 5) • (innerSL ℝ x).smulRight x -
      (Cinf * s ^ 3) • ContinuousLinearMap.id ℝ E₃ with hT₀
  have hgd : ‖g - g₀‖ ≤ C' * s ^ 3 := by rw [hg₀, sub_neg_eq_add]; exact hg
  have hg₀n : ‖g₀‖ = Cinf * s ^ 2 := by
    rw [hg₀, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    linear_combination (Cinf * s ^ 2) * hx
  have hgn : ‖g‖ ≤ (Cinf + C') * s ^ 2 := by
    have hs32 : s ^ 3 ≤ s ^ 2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    calc ‖g‖ = ‖g₀ + (g - g₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖g₀‖ + ‖g - g₀‖ := norm_add_le _ _
      _ ≤ Cinf * s ^ 2 + C' * s ^ 3 := by rw [hg₀n]; linarith
      _ ≤ _ := by nlinarith
  have hT₀n : ‖T₀‖ ≤ 4 * Cinf * s ^ 3 := by
    calc ‖T₀‖ ≤ ‖(3 * Cinf * s ^ 5) • (innerSL ℝ x).smulRight x‖ +
          ‖(Cinf * s ^ 3) • ContinuousLinearMap.id ℝ E₃‖ := norm_sub_le _ _
      _ ≤ 3 * Cinf * s ^ 5 * (‖x‖ * ‖x‖) + Cinf * s ^ 3 * 1 := by
          rw [norm_smul, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
            Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          gcongr
          exact ContinuousLinearMap.norm_id_le
      _ = 4 * Cinf * s ^ 3 := by linear_combination (3 * Cinf * s ^ 3 * (‖x‖ * s + 1)) * hx
  have hmodel : ⟪T₀ g₀, g₀⟫ = 2 * Cinf ^ 3 * s ^ 7 := by
    simp only [hT₀, hg₀, sub_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right,
      map_neg, map_smul, real_inner_self_eq_norm_sq, conj_trivial]
    linear_combination (Cinf ^ 3 * s ^ 7 *
      (3 * (‖x‖ * s) ^ 3 + 3 * (‖x‖ * s) ^ 2 + 2 * (‖x‖ * s) + 2)) * hx
  clear_value T₀ g₀
  have hsplit : ⟪T g, g⟫ - 2 * Cinf ^ 3 * s ^ 7 =
      ⟪(T - T₀) g, g⟫ + ⟪T₀ (g - g₀), g⟫ + ⟪T₀ g₀, g - g₀⟫ := by
    rw [← hmodel, sub_apply, map_sub, inner_sub_left, inner_sub_left,
      inner_sub_right]
    ring
  rw [hsplit]
  calc _ ≤ |⟪(T - T₀) g, g⟫| + |⟪T₀ (g - g₀), g⟫| + |⟪T₀ g₀, g - g₀⟫| :=
        abs_add_three _ _ _
    _ ≤ ‖T - T₀‖ * ‖g‖ * ‖g‖ + ‖T₀‖ * ‖g - g₀‖ * ‖g‖ + ‖T₀‖ * ‖g₀‖ * ‖g - g₀‖ := by
        gcongr <;> exact levelAsymp_abs_inner_le _ _ _
    _ ≤ (C' * s ^ 4) * ((Cinf + C') * s ^ 2) * ((Cinf + C') * s ^ 2) +
        (4 * Cinf * s ^ 3) * (C' * s ^ 3) * ((Cinf + C') * s ^ 2) +
        (4 * Cinf * s ^ 3) * (Cinf * s ^ 2) * (C' * s ^ 3) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact levelAsymp_mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hT hgn hgn
        · exact levelAsymp_mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hT₀n hgd hgn
        · exact levelAsymp_mul3_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hT₀n
            hg₀n.le hgd
    _ = _ := by ring

/-- Scalar step from `H = 2s + O(s²)` to `H = 2ε / Cinf + O(ε²)`. -/
lemma levelAsymp_real_meanCurv_eps {Cinf C' a ε s H B : ℝ} (hC : 0 < Cinf) (ha : 0 < a)
    (hs : 0 < s) (hεs : a * s ≤ ε) (hval : |ε - Cinf * s| ≤ C' * s ^ 2)
    (hH : |H - 2 * s| ≤ B * s ^ 2) :
    |H - 2 * ε / Cinf| ≤ (B + 2 * C' / Cinf) * a⁻¹ ^ 2 * ε ^ 2 := by
  have hC' : 0 ≤ C' := by nlinarith [abs_nonneg (ε - Cinf * s), sq_pos_of_pos hs]
  have hB : 0 ≤ B := by nlinarith [abs_nonneg (H - 2 * s), sq_pos_of_pos hs]
  have hsb : s ≤ a⁻¹ * ε := by
    rw [inv_mul_eq_div, le_div_iff₀ ha]; linarith
  have hs2 : s ^ 2 ≤ a⁻¹ ^ 2 * ε ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hs.le hsb 2
  have e : H - 2 * ε / Cinf = (H - 2 * s) + 2 * (Cinf * s - ε) / Cinf := by
    field_simp; ring
  rw [e]
  calc _ ≤ |H - 2 * s| + |2 * (Cinf * s - ε) / Cinf| := abs_add_le _ _
    _ = |H - 2 * s| + 2 * |ε - Cinf * s| / Cinf := by
        rw [abs_div, abs_mul, abs_of_pos hC, abs_sub_comm (Cinf * s)]; norm_num
    _ ≤ B * s ^ 2 + 2 * (C' * s ^ 2) / Cinf := by gcongr
    _ = (B + 2 * C' / Cinf) * s ^ 2 := by ring
    _ ≤ (B + 2 * C' / Cinf) * (a⁻¹ ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = _ := by ring

/-- Scalar form of the integrand: `H w - 4 ε⁻¹ w² = -(2ε / Cinf) w + O(ε² w)`. -/
lemma levelAsymp_real_integrand {Cinf ε w H M₁ MH : ℝ} (hε : 0 < ε) (hw0 : 0 ≤ w)
    (hw : |w - ε ^ 2 / Cinf| ≤ M₁ * ε ^ 3) (hH : |H - 2 * ε / Cinf| ≤ MH * ε ^ 2) :
    |(H * w - 4 * ε⁻¹ * w ^ 2) - (-2 * ε / Cinf) * w| ≤ (MH + 4 * M₁) * ε ^ 2 * w := by
  have e : (H * w - 4 * ε⁻¹ * w ^ 2) - (-2 * ε / Cinf) * w =
      w * ((H - 2 * ε / Cinf) - 4 * ε⁻¹ * (w - ε ^ 2 / Cinf)) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_nonneg hw0, mul_comm]
  apply mul_le_mul_of_nonneg_right _ hw0
  calc _ ≤ |H - 2 * ε / Cinf| + |4 * ε⁻¹ * (w - ε ^ 2 / Cinf)| := abs_sub _ _
    _ = |H - 2 * ε / Cinf| + 4 * ε⁻¹ * |w - ε ^ 2 / Cinf| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (inv_pos.mpr hε)]
    _ ≤ MH * ε ^ 2 + 4 * ε⁻¹ * (M₁ * ε ^ 3) := by gcongr
    _ = _ := by field_simp

/-- Blueprint `lem:level-asymptotics`, all pointwise and integral clauses with one and the
same Kelvin coefficient `Cinf`: the value/gradient/Hessian expansions, the smooth radial graph
`ρ` with `ρ = Cinf / ε + O(1)`, and on each small level `{u = ε}`: `|x| = Cinf / ε + O(1)`,
`w = ε² / Cinf + O(ε³)` with `∇u ≠ 0`, `H = 2ε / Cinf + O(ε²)`, the flux `∫ w = 4π Cinf`,
and `∫ (H w - 4 ε⁻¹ w²) dH² = -8π ε + O(ε²)`. The integral clause is derived from the flux
identity, not from the area element. -/
theorem capacitary_level_asymptotics
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 ∧
        ‖fderiv ℝ (gradient u) x -
          ((3 * Cinf / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
            (Cinf / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' / ‖x‖ ^ 4) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ M) ∧
          {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)}) ∧
        (∀ x : E₃, u x = ε →
          x ∉ K ∧ gradient u x ≠ 0 ∧ |‖x‖ - Cinf / ε| ≤ M ∧
          |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3 ∧
          |CapacitaryK.meanCurv u x - 2 * ε / Cinf| ≤ M * ε ^ 2) ∧
        (∫ x in u ⁻¹' {ε}, ‖gradient u x‖ ∂hausdorffMeasure2 3) = 4 * Real.pi * Cinf ∧
        |(∫ x in u ⁻¹' {ε}, (CapacitaryK.meanCurv u x * ‖gradient u x‖ -
            4 * ε⁻¹ * ‖gradient u x‖ ^ 2) ∂hausdorffMeasure2 3) + 8 * Real.pi * ε| ≤
          M * ε ^ 2 := by
  obtain ⟨Cinf, R, C', hR, hexp⟩ := kelvin_hessian_expansion hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hlower := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  have haC : a ≤ Cinf := kelvin_coefficient_ge_of_lower_bound
    (R₀ := R₀) (R := R) (C' := C') (fun x hx => hlower x (by
      intro hxK
      have hxR : ‖x‖ ≤ R₀ := by simpa using hKR hxK
      exact (not_lt_of_ge hxR) hx)) (fun x hx => (hexp x hx).1)
  have hC : 0 < Cinf := ha.trans_le haC
  obtain ⟨ε₁, hε₁, C'', hgraph⟩ := capacitary_level_radial_graph_of_expansion hK hKR hzero
    hu hh hb hinf hC (fun x hx => ⟨(hexp x hx).1, (hexp x hx).2.1⟩)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ := capacitary_potential_contDiffOn hK hu hh
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = min (min R⁻¹ 1) (Cinf / (2 * (|C'| + 1))) := ⟨_, rfl⟩
  have hSpos : 0 < S := by
    rw [hS]; exact lt_min (lt_min (inv_pos.mpr hR) one_pos) (by positivity)
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min (min ε₁ (1 / 2)) (a * S) := ⟨_, rfl⟩
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]; exact lt_min (lt_min hε₁ (by norm_num)) (mul_pos ha hSpos)
  have hε₀half : ε₀ ≤ 1 / 2 := by rw [hε₀]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₀₁ : ε₀ ≤ ε₁ := by rw [hε₀]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₀S : ε₀ ≤ a * S := by rw [hε₀]; exact min_le_right _ _
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ,
      M₁ = C' * a⁻¹ ^ 3 + C' * a⁻¹ ^ 2 * (C' * a⁻¹ ^ 2 + 2) / Cinf := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = C' * (Cinf + C') ^ 2 + 4 * Cinf * (2 * Cinf + C') * C' := ⟨_, rfl⟩
  obtain ⟨MH, hMH⟩ : ∃ MH : ℝ,
      MH = (8 * (A + 6 * C' * (Cinf + C') ^ 2) / Cinf ^ 3 + 2 * C' / Cinf) * a⁻¹ ^ 2 :=
    ⟨_, rfl⟩
  -- pointwise asymptotics on each small level
  have hpt : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x : E₃, u x = ε →
      x ∉ K ∧ gradient u x ≠ 0 ∧ |‖x‖ - Cinf / ε| ≤ C' / a ∧
      |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M₁ * ε ^ 3 ∧
      |CapacitaryK.meanCurv u x - 2 * ε / Cinf| ≤ MH * ε ^ 2 := by
    intro ε hε hεε₀ x hxε
    have hε1 : ε < 1 := by linarith
    have hxK : x ∉ K := fun hxK => by rw [hb x hxK] at hxε; linarith
    have hx0 : x ≠ 0 := fun h => hxK (h ▸ interior_subset hzero)
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hl := hlower x hxK
    rw [hxε] at hl
    set s := ‖x‖⁻¹ with hs_def
    have hs : 0 < s := inv_pos.mpr hn
    have hxs : ‖x‖ * s = 1 := mul_inv_cancel₀ hn.ne'
    have has : a * s ≤ ε := by rw [hs_def, ← div_eq_mul_inv]; exact hl
    have hsS : s < S := by
      by_contra h
      have := mul_le_mul_of_nonneg_left (le_of_not_gt h) ha.le
      linarith
    have hsR : s ≤ R⁻¹ := hsS.le.trans (by rw [hS]; exact (min_le_left _ _).trans (min_le_left _ _))
    have hs1 : s ≤ 1 := hsS.le.trans (by rw [hS]; exact (min_le_left _ _).trans (min_le_right _ _))
    have hsC : C' * s ≤ Cinf / 2 := by
      have h1 : s ≤ Cinf / (2 * (|C'| + 1)) := hsS.le.trans (by rw [hS]; exact min_le_right _ _)
      have h2 : s * (2 * (|C'| + 1)) ≤ Cinf := (le_div_iff₀ (by positivity)).mp h1
      nlinarith [le_abs_self C', abs_nonneg C']
    have hxR : R ≤ ‖x‖ := by
      have := (inv_le_inv₀ hn hR).mp hsR
      exact this
    obtain ⟨hv, hgr, hH⟩ := hexp x hxR
    simp only [div_eq_mul_inv, ← inv_pow, ← hs_def] at hv hgr hH
    rw [hxε] at hv
    have hv' : |ε - Cinf * s| ≤ C' * s ^ 2 := by simpa [mul_comm, mul_left_comm] using hv
    have hgr' : ‖gradient u x + (Cinf * s ^ 3) • x‖ ≤ C' * s ^ 3 := hgr
    have hH' : ‖fderiv ℝ (gradient u) x - ((3 * Cinf * s ^ 5) • (innerSL ℝ x).smulRight x -
        (Cinf * s ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' * s ^ 4 := hH
    have hwv : |‖gradient u x‖ - Cinf * s ^ 2| ≤ C' * s ^ 3 := by
      have hn' : ‖-((Cinf * s ^ 3) • x)‖ = Cinf * s ^ 2 := by
        rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
        linear_combination (Cinf * s ^ 2) * hxs
      rw [← hn']
      calc _ ≤ ‖gradient u x - -((Cinf * s ^ 3) • x)‖ := abs_norm_sub_norm_le _ _
        _ = _ := by rw [sub_neg_eq_add]
        _ ≤ _ := hgr'
    have hwpos : 0 < ‖gradient u x‖ := by
      obtain ⟨h1, _⟩ := abs_le.mp hwv
      have h2 : C' * s ^ 3 ≤ Cinf / 2 * s ^ 2 := by
        have := mul_le_mul_of_nonneg_right hsC (sq_nonneg s)
        have e : C' * s ^ 3 = C' * s * s ^ 2 := by ring
        linarith
      have h3 : 0 < Cinf * s ^ 2 := by positivity
      linarith
    have hg0 : gradient u x ≠ 0 := norm_pos_iff.mp hwpos
    have hrad := kelvin_level_radius_estimate (t := ‖x‖) ha hε hn hl (by
      have := (hexp x hxR).1
      rwa [hxε] at this)
    have hwε := levelAsymp_real_gradNorm hC ha hs hε1.le has hv' hwv
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) u x := hsm.contDiffAt (hopen.mem_nhds hxK)
    have hΔ := kelvin_laplacianN_eq_zero_of_distributional hopen hu.continuousOn hh x hxK
    have hmc := CapacitaryK.meanCurv_eq (hcd.of_le (by simp)) hwpos hΔ
    rw [CapacitaryK.dirHess_eq_inner (hcd.of_le (by simp))] at hmc
    have hN := levelAsymp_vec_quadratic hC hs hs1 hxs hgr' hH'
    have hHs := levelAsymp_real_meanCurv hC hs hs1 hsC hwv hN
    have hHε := levelAsymp_real_meanCurv_eps hC ha hs has hv' hHs
    refine ⟨hxK, hg0, hrad, ?_, ?_⟩
    · rw [hM₁]; exact hwε
    · rw [hmc, hMH, hA]
      exact hHε
  obtain ⟨MI, hMI⟩ : ∃ MI : ℝ, MI = (MH + 4 * M₁) * (4 * Real.pi * Cinf) := ⟨_, rfl⟩
  refine ⟨Cinf, hC, ⟨R, C', hR, hexp⟩, ε₀, hε₀pos, by linarith,
    max (max C'' (C' / a)) (max (max M₁ MH) MI), ?_⟩
  intro ε hε hεε₀
  set M := max (max C'' (C' / a)) (max (max M₁ MH) MI)
  have hC''M : C'' ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hraM : C' / a ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM₁M : M₁ ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hMHM : MH ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hMIM : MI ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨ρ, hρs, hρb, hρeq⟩ := hgraph ε hε (hεε₀.trans_le hε₀₁)
  have hP := hpt ε hε hεε₀
  have hε1 : ε < 1 := by linarith
  have hflux : (∫ x in u ⁻¹' {ε}, ‖gradient u x‖ ∂hausdorffMeasure2 3) =
      4 * Real.pi * Cinf :=
    capacitary_flux_level_of_gradient_expansion hK hu hh hb hinf hR
      (fun x hx => (hexp x hx).2.1) hε hε1 (fun x hx => (hP x hx).2.1)
  refine ⟨⟨ρ, hρs, fun θ hθ => (hρb θ hθ).trans hC''M, hρeq⟩, fun x hx => ?_, hflux, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hP x hx
    exact ⟨h1, h2, h3.trans hraM, h4.trans (mul_le_mul_of_nonneg_right hM₁M (by positivity)),
      h5.trans (mul_le_mul_of_nonneg_right hMHM (by positivity))⟩
  -- the integral clause, from the flux identity
  set L := u ⁻¹' {ε} with hL
  set μ := hausdorffMeasure2 3 with hμ
  have hLm : MeasurableSet L := hu.measurable (measurableSet_singleton ε)
  have hpi : 0 < 4 * Real.pi * Cinf := by positivity
  have hwint : IntegrableOn (fun x => ‖gradient u x‖) L μ := by
    by_contra h
    rw [integral_undef h] at hflux
    linarith
  set f : E₃ → ℝ := fun x => CapacitaryK.meanCurv u x * ‖gradient u x‖ -
    4 * ε⁻¹ * ‖gradient u x‖ ^ 2 with hf
  have hsm3 : ContDiffOn ℝ 3 u Kᶜ := hsm.of_le (by simp)
  have hfc : ContinuousOn f L := by
    intro x hx
    have hxK := (hP x hx).1
    have hwc : ContinuousAt (fun y => ‖gradient u y‖) x :=
      (CapacitaryK.continuousOn_gradNorm hopen hsm3).continuousAt (hopen.mem_nhds hxK)
    have hHc : ContinuousAt (CapacitaryK.meanCurv u) x :=
      CapacitaryK.meanCurv_continuousAt_regular (hsm3.contDiffAt (hopen.mem_nhds hxK))
        (norm_pos_iff.mpr (hP x hx).2.1)
    exact ((hHc.mul hwc).sub (continuousAt_const.mul (hwc.pow 2))).continuousWithinAt
  have hpt' : ∀ x ∈ L, |f x - (-2 * ε / Cinf) * ‖gradient u x‖| ≤
      (MH + 4 * M₁) * ε ^ 2 * ‖gradient u x‖ := by
    intro x hx
    obtain ⟨_, _, _, h4, h5⟩ := hP x hx
    exact levelAsymp_real_integrand hε (norm_nonneg _) h4 h5
  have hfint : IntegrableOn f L μ := by
    refine Integrable.mono' (hwint.const_mul ((MH + 4 * M₁) * ε ^ 2 + 2 * ε / Cinf))
      (hfc.aestronglyMeasurable hLm) (ae_restrict_of_forall_mem hLm fun x hx => ?_)
    have h := hpt' x hx
    rw [Real.norm_eq_abs]
    have hw0 := norm_nonneg (gradient u x)
    have e : f x = (f x - (-2 * ε / Cinf) * ‖gradient u x‖) +
        (-2 * ε / Cinf) * ‖gradient u x‖ := by ring
    rw [e]
    calc _ ≤ |f x - (-2 * ε / Cinf) * ‖gradient u x‖| + |(-2 * ε / Cinf) * ‖gradient u x‖| :=
          abs_add_le _ _
      _ = |f x - (-2 * ε / Cinf) * ‖gradient u x‖| + 2 * ε / Cinf * ‖gradient u x‖ := by
          rw [abs_mul, abs_of_nonneg hw0, abs_div, abs_of_pos hC, abs_mul, abs_neg,
            abs_two, abs_of_pos hε]
      _ ≤ (MH + 4 * M₁) * ε ^ 2 * ‖gradient u x‖ + 2 * ε / Cinf * ‖gradient u x‖ := by
          linarith
      _ = _ := by ring
  have hdiff : (∫ x in L, f x ∂μ) + 8 * Real.pi * ε =
      ∫ x in L, (f x - (-2 * ε / Cinf) * ‖gradient u x‖) ∂μ := by
    rw [integral_sub hfint (hwint.const_mul _), integral_const_mul, hflux]
    field_simp
    ring
  have hbound : ‖∫ x in L, (f x - (-2 * ε / Cinf) * ‖gradient u x‖) ∂μ‖ ≤
      ∫ x in L, (MH + 4 * M₁) * ε ^ 2 * ‖gradient u x‖ ∂μ :=
    norm_integral_le_of_norm_le (hwint.const_mul _)
      (ae_restrict_of_forall_mem hLm fun x hx => by rw [Real.norm_eq_abs]; exact hpt' x hx)
  rw [integral_const_mul, hflux, Real.norm_eq_abs, ← hdiff] at hbound
  calc _ ≤ (MH + 4 * M₁) * ε ^ 2 * (4 * Real.pi * Cinf) := hbound
    _ = MI * ε ^ 2 := by rw [hMI]; ring
    _ ≤ M * ε ^ 2 := mul_le_mul_of_nonneg_right hMIM (by positivity)

/-- Blueprint `lem:level-asymptotics`, radial graph and `w = ε² / Cinf + O(ε³)`; `Cinf` is
pinned by the value expansion `u = Cinf / |x| + O(|x|⁻²)`. -/
theorem capacitary_level_gradNorm_asymptotics
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ M) ∧
          {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)}) ∧
        ∀ x : E₃, u x = ε → gradient u x ≠ 0 ∧ |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3 := by
  obtain ⟨Cinf, hC, ⟨R, C', hR, hexp⟩, ε₀, hε₀, -, M, hM⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  refine ⟨Cinf, hC, ⟨R, C', hR, fun x hx => (hexp x hx).1⟩, ε₀, hε₀, M, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hρ, hpt, -, -⟩ := hM ε hε hεε₀
  exact ⟨hρ, fun x hx => ⟨(hpt x hx).2.1, (hpt x hx).2.2.2.1⟩⟩

/-- Blueprint `lem:level-asymptotics`, `H = 2ε / Cinf + O(ε²)` on small levels (normal toward
infinity, round spheres have `H = 2 / R`); `Cinf` is pinned by the value expansion. -/
theorem capacitary_level_meanCurv_asymptotics
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x : E₃, u x = ε →
        |CapacitaryK.meanCurv u x - 2 * ε / Cinf| ≤ M * ε ^ 2 := by
  obtain ⟨Cinf, hC, ⟨R, C', hR, hexp⟩, ε₀, hε₀, -, M, hM⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  exact ⟨Cinf, hC, ⟨R, C', hR, fun x hx => (hexp x hx).1⟩, ε₀, hε₀, M,
    fun ε hε hεε₀ x hx => ((hM ε hε hεε₀).2.1 x hx).2.2.2.2⟩

/-- Blueprint `lem:level-asymptotics`, final display:
`∫_{u = ε} (H w - 4 ε⁻¹ w²) dH² = -8π ε + O(ε²)`. Derived from the pointwise asymptotics and
the flux identity `∫_{u = ε} w dH² = 4π Cinf`, rather than from the area element. -/
theorem capacitary_level_Hw_integral_asymptotics
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      |(∫ x in u ⁻¹' {ε}, (CapacitaryK.meanCurv u x * ‖gradient u x‖ -
          4 * ε⁻¹ * ‖gradient u x‖ ^ 2) ∂hausdorffMeasure2 3) + 8 * Real.pi * ε| ≤
        M * ε ^ 2 := by
  obtain ⟨Cinf, -, -, ε₀, hε₀, -, M, hM⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  exact ⟨ε₀, hε₀, M, fun ε hε hεε₀ => (hM ε hε hεε₀).2.2.2⟩

end LiquidDrop
