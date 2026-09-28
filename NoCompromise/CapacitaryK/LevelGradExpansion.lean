import NoCompromise.CapacitaryK.CapacitaryRadialGraph
import NoCompromise.CapacitaryK.GradNormExpansion

/-!
# The gradient length on small capacitary levels

Chapter 31, `lem:K-level-asymptotics`, `eq:K-gradu`: on the level `{u = t}`, written as
the radial graph `s • θ + z` about the normalized dipole center `z`,
`|∇u| = t²/C + t⁴ Q(θ)/C⁴ + O(t⁵)` uniformly in `θ`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Inverting the radial expansion `s = 1/a + a k + O(a²)`. -/
theorem level_inv_radius_expansion {a k s Bk A₁ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hBk : 0 ≤ Bk) (hA₁ : 0 ≤ A₁) (hsmall : a * (Bk + A₁) ≤ 1 / 2) (hk : |k| ≤ Bk)
    (hs : |s - (1 / a + a * k)| ≤ A₁ * a ^ 2) :
    0 < s⁻¹ ∧ s⁻¹ ≤ 2 * a ∧
      |s⁻¹ - (a - k * a ^ 3)| ≤ 2 * (A₁ + Bk ^ 2 + Bk * A₁) * a ^ 4 := by
  set e := s - (1 / a + a * k) with he
  have hse : s = 1 / a + a * k + e := by rw [he]; ring
  have hk' := abs_le.mp hk
  have he' := abs_le.mp hs
  have hak : |a * k| ≤ Bk := by
    rw [abs_mul, abs_of_pos ha]; nlinarith [abs_nonneg k]
  have ha2 : A₁ * a ^ 2 ≤ A₁ := by
    have : a ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hinv : 1 / (2 * a) ≤ s := by
    have h1 : 1 / (2 * a) = 1 / a - 1 / (2 * a) := by field_simp; ring
    have h2 : Bk + A₁ ≤ 1 / (2 * a) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have := (abs_le.mp hak).1
    rw [hse]; linarith
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hinv
  have hsinv : s⁻¹ ≤ 2 * a := by
    rw [inv_le_comm₀ hspos (by positivity)]
    simpa [one_div] using hinv
  refine ⟨inv_pos.mpr hspos, hsinv, ?_⟩
  have hid : s⁻¹ - (a - k * a ^ 3) = s⁻¹ * (k ^ 2 * a ^ 4 - e * a + e * k * a ^ 3) := by
    have hne : s ≠ 0 := hspos.ne'
    have hne' : a ≠ 0 := ha.ne'
    have h1 : 1 - s * (a - k * a ^ 3) = k ^ 2 * a ^ 4 - e * a + e * k * a ^ 3 := by
      rw [hse]; field_simp; ring
    rw [← h1]; field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hspos)]
  have hb : |k ^ 2 * a ^ 4 - e * a + e * k * a ^ 3| ≤ (A₁ + Bk ^ 2 + Bk * A₁) * a ^ 3 := by
    have hea : |e| ≤ A₁ * a ^ 2 := hs
    have h1 : |k ^ 2 * a ^ 4| ≤ Bk ^ 2 * a ^ 3 := by
      rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < a ^ 4)]
      have : |k| ^ 2 ≤ Bk ^ 2 := pow_le_pow_left₀ (abs_nonneg k) hk 2
      have ha43 : a ^ 4 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
      calc |k| ^ 2 * a ^ 4 ≤ Bk ^ 2 * a ^ 4 := mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ Bk ^ 2 * a ^ 3 := mul_le_mul_of_nonneg_left ha43 (by positivity)
    have h2 : |e * a| ≤ A₁ * a ^ 3 := by
      rw [abs_mul, abs_of_pos ha]
      calc |e| * a ≤ A₁ * a ^ 2 * a := mul_le_mul_of_nonneg_right hea ha.le
        _ = A₁ * a ^ 3 := by ring
    have h3 : |e * k * a ^ 3| ≤ Bk * A₁ * a ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < a ^ 3)]
      have : |e| ≤ A₁ := hea.trans ha2
      have := mul_le_mul this hk (abs_nonneg k) hA₁
      calc |e| * |k| * a ^ 3 ≤ A₁ * Bk * a ^ 3 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = Bk * A₁ * a ^ 3 := by ring
    calc |k ^ 2 * a ^ 4 - e * a + e * k * a ^ 3|
        ≤ |k ^ 2 * a ^ 4| + |e * a| + |e * k * a ^ 3| := by
          have := abs_sub (k ^ 2 * a ^ 4) (e * a)
          have := abs_add_le (k ^ 2 * a ^ 4 - e * a) (e * k * a ^ 3)
          linarith
      _ ≤ _ := by linarith
  calc s⁻¹ * |k ^ 2 * a ^ 4 - e * a + e * k * a ^ 3|
      ≤ (2 * a) * ((A₁ + Bk ^ 2 + Bk * A₁) * a ^ 3) :=
        mul_le_mul hsinv hb (abs_nonneg _) (by positivity)
    _ = 2 * (A₁ + Bk ^ 2 + Bk * A₁) * a ^ 4 := by ring

/-- Substituting `ε = a - k a³ + O(a⁴)` into `ε² + 3 k ε⁴`. -/
theorem level_value_expansion {a k ε Bk H : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hBk : 0 ≤ Bk) (hH : 0 ≤ H) (hk : |k| ≤ Bk) (hε : 0 < ε) (hε2 : ε ≤ 2 * a)
    (hd : |ε - (a - k * a ^ 3)| ≤ H * a ^ 4) :
    |ε ^ 2 + 3 * k * ε ^ 4 - (a ^ 2 + k * a ^ 4)| ≤ (3 * H + 46 * Bk * (H + Bk)) * a ^ 5 := by
  have key : ε ^ 2 + 3 * k * ε ^ 4 - (a ^ 2 + k * a ^ 4) =
      (ε - (a - k * a ^ 3)) * (ε + a) - k * a ^ 3 * (ε - a) +
        3 * k * (ε - a) * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3) := by ring
  have ha43 : a ^ 4 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have ha65 : a ^ 6 ≤ a ^ 5 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have hδ : |ε - a| ≤ (H + Bk) * a ^ 3 := by
    have h1 : ε - a = (ε - (a - k * a ^ 3)) - k * a ^ 3 := by ring
    have h2 : |k * a ^ 3| ≤ Bk * a ^ 3 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < a ^ 3)]
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    rw [h1]
    calc _ ≤ |ε - (a - k * a ^ 3)| + |k * a ^ 3| := abs_sub _ _
      _ ≤ H * a ^ 4 + Bk * a ^ 3 := add_le_add hd h2
      _ ≤ H * a ^ 3 + Bk * a ^ 3 := by nlinarith
      _ = (H + Bk) * a ^ 3 := by ring
  have hS0 : 0 ≤ ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3 := by positivity
  have hS : ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3 ≤ 15 * a ^ 3 := by
    have e3 : ε ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ hε.le hε2 3
    have e2 : ε ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hε.le hε2 2
    have e2' : ε ^ 2 * a ≤ (2 * a) ^ 2 * a := mul_le_mul_of_nonneg_right e2 ha.le
    have e1 : ε * a ^ 2 ≤ (2 * a) * a ^ 2 := mul_le_mul_of_nonneg_right hε2 (by positivity)
    nlinarith
  have t1 : |(ε - (a - k * a ^ 3)) * (ε + a)| ≤ 3 * H * a ^ 5 := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < ε + a)]
    calc _ ≤ H * a ^ 4 * (3 * a) :=
          mul_le_mul hd (by linarith) (by linarith) (by positivity)
      _ = 3 * H * a ^ 5 := by ring
  have t2 : |k * a ^ 3 * (ε - a)| ≤ Bk * (H + Bk) * a ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < a ^ 3)]
    calc |k| * a ^ 3 * |ε - a| ≤ Bk * a ^ 3 * ((H + Bk) * a ^ 3) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hk (by positivity)) hδ (abs_nonneg _)
            (by positivity)
      _ = Bk * (H + Bk) * a ^ 6 := by ring
      _ ≤ Bk * (H + Bk) * a ^ 5 := mul_le_mul_of_nonneg_left ha65 (by positivity)
  have t3 : |3 * k * (ε - a) * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3)| ≤
      45 * Bk * (H + Bk) * a ^ 5 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hS0, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |k| * |ε - a| * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3)
        ≤ 3 * Bk * ((H + Bk) * a ^ 3) * (15 * a ^ 3) := by
          apply mul_le_mul _ hS hS0 (by positivity)
          apply mul_le_mul _ hδ (abs_nonneg _) (by positivity)
          linarith
      _ = 45 * Bk * (H + Bk) * a ^ 6 := by ring
      _ ≤ 45 * Bk * (H + Bk) * a ^ 5 := mul_le_mul_of_nonneg_left ha65 (by positivity)
  rw [key]
  calc _ ≤ |(ε - (a - k * a ^ 3)) * (ε + a)| + |k * a ^ 3 * (ε - a)| +
        |3 * k * (ε - a) * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3)| := by
        have := abs_sub ((ε - (a - k * a ^ 3)) * (ε + a)) (k * a ^ 3 * (ε - a))
        have := abs_add_le ((ε - (a - k * a ^ 3)) * (ε + a) - k * a ^ 3 * (ε - a))
          (3 * k * (ε - a) * (ε ^ 3 + ε ^ 2 * a + ε * a ^ 2 + a ^ 3))
        linarith
    _ ≤ _ := by nlinarith

/-- A vector `-(C ε²) θ + w₁ + w₂` whose perturbation has radial part `-3 q ε⁴`, with
`‖w₁‖ ≤ B ε⁴` and `‖w₂‖ ≤ M ε⁵`, has length `C ε² + 3 q ε⁴ + O(ε⁵)`. -/
theorem level_grad_vector_expansion {C B M q ε : ℝ} {θ v w₁ w₂ : E3} (hC : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M)
    (hsmall : (B + M) * ε ^ 2 ≤ C / 2) (hθ : ‖θ‖ = 1)
    (hv : v + (C * ε ^ 2) • θ = w₁ + w₂)
    (h₁ : ‖w₁‖ ≤ B * ε ^ 4) (h₁θ : ⟪w₁, θ⟫ = -3 * q * ε ^ 4) (h₂ : ‖w₂‖ ≤ M * ε ^ 5) :
    |‖v‖ - (C * ε ^ 2 + 3 * q * ε ^ 4)| ≤ (M + (B + M) ^ 2 / C) * ε ^ 5 := by
  set c := C * ε ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set w := w₁ + w₂ with hw
  have hvw : v = w - c • θ := eq_sub_of_add_eq hv
  have hε54 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hwn : ‖w‖ ≤ (B + M) * ε ^ 4 := by
    calc ‖w‖ ≤ ‖w₁‖ + ‖w₂‖ := norm_add_le _ _
      _ ≤ B * ε ^ 4 + M * ε ^ 5 := add_le_add h₁ h₂
      _ ≤ B * ε ^ 4 + M * ε ^ 4 := by nlinarith
      _ = (B + M) * ε ^ 4 := by ring
  have hwθ : |⟪w, θ⟫| ≤ ‖w‖ := by
    simpa [hθ] using abs_real_inner_le_norm w θ
  have h₂θ : |⟪w₂, θ⟫| ≤ M * ε ^ 5 := by
    have := abs_real_inner_le_norm w₂ θ
    rw [hθ, mul_one] at this
    exact this.trans h₂
  set a := c - ⟪w, θ⟫ with ha
  have ha_eq : a = C * ε ^ 2 + 3 * q * ε ^ 4 - ⟪w₂, θ⟫ := by
    rw [ha, hw, inner_add_left, h₁θ, hc]; ring
  have hnsq : ‖v‖ ^ 2 = a ^ 2 + (‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2) := by
    rw [hvw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hθ, Real.norm_eq_abs,
      mul_one, sq_abs, ha]
    ring
  have hdiff0 : 0 ≤ ‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2 := by
    have : ⟪w, θ⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [sq_le_sq, abs_norm]; exact hwθ
    linarith
  have hdiff1 : ‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2 ≤ ((B + M) * ε ^ 4) ^ 2 := by
    have : ‖w‖ ^ 2 ≤ ((B + M) * ε ^ 4) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hwn 2
    nlinarith [sq_nonneg ⟪w, θ⟫]
  have hahalf : c / 2 ≤ a := by
    have h1 : (B + M) * ε ^ 4 ≤ c / 2 := by
      rw [hc]
      have : (B + M) * ε ^ 4 = ((B + M) * ε ^ 2) * ε ^ 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hsmall (by positivity : (0 : ℝ) ≤ ε ^ 2)
      linarith
    have := (abs_le.mp (hwθ.trans (hwn.trans h1))).2
    rw [ha]; linarith
  have hapos : 0 < a := by linarith
  have hva : a ≤ ‖v‖ := by
    nlinarith [norm_nonneg v]
  have hprod : (‖v‖ - a) * c ≤ ((B + M) * ε ^ 4) ^ 2 := by
    have h1 : (‖v‖ - a) * (‖v‖ + a) ≤ ((B + M) * ε ^ 4) ^ 2 := by nlinarith
    have h2 : c ≤ ‖v‖ + a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ ‖v‖ - a)]
  have hup : ‖v‖ - a ≤ (B + M) ^ 2 / C * ε ^ 5 := by
    have h1 : ‖v‖ - a ≤ ((B + M) * ε ^ 4) ^ 2 / c := by
      rw [le_div_iff₀ hcpos]; exact hprod
    have h2 : ((B + M) * ε ^ 4) ^ 2 / c = (B + M) ^ 2 / C * ε ^ 6 := by
      rw [hc]; field_simp
    have hε65 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
    have h3 : (B + M) ^ 2 / C * ε ^ 6 ≤ (B + M) ^ 2 / C * ε ^ 5 :=
      mul_le_mul_of_nonneg_left hε65 (by positivity)
    linarith
  have hsplit : ‖v‖ - (C * ε ^ 2 + 3 * q * ε ^ 4) = (‖v‖ - a) - ⟪w₂, θ⟫ := by
    rw [ha_eq]; ring
  rw [hsplit]
  have h2' := abs_le.mp h₂θ
  have hX : 0 ≤ (B + M) ^ 2 / C * ε ^ 5 := by positivity
  have hsum : (M + (B + M) ^ 2 / C) * ε ^ 5 = M * ε ^ 5 + (B + M) ^ 2 / C * ε ^ 5 := by ring
  rw [hsum, abs_le]
  constructor <;> linarith

/-- A continuous function vanishing at `0` is eventually below any positive constant
on the right of `0`. -/
theorem level_eventually_lt_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0)
    {c : ℝ} (hc : 0 < c) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < c :=
  nhdsWithin_le_nhds ((hg.tendsto' 0 0 h0).eventually (gt_mem_nhds hc))

/-- `lem:K-level-asymptotics`, `eq:K-gradu`: on the small level `{u = t}`, at the radial
point `s • θ + z` about the normalized dipole center `z = (v 0)⁻¹ • ∇v(0)`,
`|∇u| = t²/C + t⁴ Q(θ)/C⁴ + O(t⁵)` uniformly in the unit direction `θ`, where
`C = v 0` and `Q = kelvinTranslatedQuadrupole v`. -/
theorem capacitary_level_gradNorm_expansion
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ θ : E3, ‖θ‖ = 1 → ∀ s : ℝ, 0 < s →
        u (s • θ + (v 0)⁻¹ • gradient v 0) = t →
        |‖gradient u (s • θ + (v 0)⁻¹ • gradient v 0)‖ -
          (t ^ 2 / v 0 + t ^ 4 * kelvinTranslatedQuadrupole v θ / (v 0) ^ 4)| ≤ A * t ^ 5 := by
  obtain ⟨v, r, hr, hv, he, _, hv0, hQc, hQs, _, _, R, M, hR, hW, hbound⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  refine ⟨v, r, hr, hv, he, hv0, ?_⟩
  obtain ⟨B, hB0, hB⟩ := capacitary_quadratic_div_norm_fderiv_bound
    (translated_quadrupole_contDiff v) hQs
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  let W := kelvinTranslatedRemainder u v
  let f : E3 → ℝ := fun y => kelvinTranslatedQuadrupole v y / ‖y‖ ^ 5
  have hUeq : U = fun y => (W y + v 0 / ‖y‖) + f y := by
    funext y
    dsimp [U, W, f, kelvinTranslatedRemainder]
    ring
  have hdecomp : ∀ x : E3, max (R + 1) 1 ≤ ‖x‖ →
      DifferentiableAt ℝ U x ∧
        gradient U x + (v 0 / ‖x‖ ^ 3) • x = gradient W x + gradient f x ∧
        ‖gradient W x‖ ≤ |M| / ‖x‖ ^ 5 ∧ ‖gradient f x‖ ≤ B / ‖x‖ ^ 4 := by
    intro x hx
    have hxR : R < ‖x‖ := by have := (le_max_left (R + 1) 1).trans hx; linarith
    have hx1 : 1 ≤ ‖x‖ := (le_max_right (R + 1) 1).trans hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx1
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    have hdW : DifferentiableAt ℝ W x :=
      (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hxR)).differentiableAt
        (by simp)
    obtain ⟨hdC, hgC⟩ := capacitary_gradient_const_div_norm (v 0) hx0
    obtain ⟨hdf, hbf⟩ := hB x hx0
    have hdU : DifferentiableAt ℝ U x := by
      rw [hUeq]
      exact (hdW.add hdC).add hdf
    have hg : gradient U x + (v 0 / ‖x‖ ^ 3) • x = gradient W x + gradient f x := by
      have hfd : fderiv ℝ U x = fderiv ℝ W x +
          fderiv ℝ (fun y : E3 => v 0 / ‖y‖) x + fderiv ℝ f x := by
        rw [hUeq]
        exact ((hdW.hasFDerivAt.add hdC.hasFDerivAt).add hdf.hasFDerivAt).fderiv
      rw [gradient, hfd, map_add, map_add]
      change (gradient W x + gradient (fun y : E3 => v 0 / ‖y‖) x + gradient f x) +
        (v 0 / ‖x‖ ^ 3) • x = _
      rw [hgC]
      module
    have hgW : ‖gradient W x‖ = ‖fderiv ℝ W x‖ := (toDual ℝ E3).symm.norm_map _
    have hgf : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (toDual ℝ E3).symm.norm_map _
    have hWM : ‖gradient W x‖ ≤ |M| / ‖x‖ ^ 5 := by
      rw [hgW]
      exact (hbound x hxR.le).2.1.trans
        (div_le_div_of_nonneg_right (le_abs_self M) (by positivity))
    exact ⟨hdU, hg, hWM, by rw [hgf]; exact hbf⟩
  have hgrad : ∀ x : E3, max (R + 1) 1 ≤ ‖x‖ →
      DifferentiableAt ℝ U x ∧
        ‖gradient U x + (v 0 / ‖x‖ ^ 3) • x‖ ≤ (|M| + B) / ‖x‖ ^ 4 := by
    intro x hx
    obtain ⟨hdU, hg, hWM, hfB⟩ := hdecomp x hx
    have hx1 : 1 ≤ ‖x‖ := (le_max_right (R + 1) 1).trans hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx1
    have hpow : ‖x‖ ^ 4 ≤ ‖x‖ ^ 5 := by
      nlinarith [mul_nonneg (pow_nonneg (norm_nonneg x) 4) (sub_nonneg.mpr hx1)]
    refine ⟨hdU, ?_⟩
    rw [hg]
    calc
      ‖gradient W x + gradient f x‖ ≤ ‖gradient W x‖ + ‖gradient f x‖ := norm_add_le _ _
      _ ≤ |M| / ‖x‖ ^ 4 + B / ‖x‖ ^ 4 :=
        add_le_add (hWM.trans (div_le_div_of_nonneg_left (abs_nonneg M) (by positivity) hpow))
          hfB
      _ = (|M| + B) / ‖x‖ ^ 4 := (add_div _ _ _).symm
  obtain ⟨A, hA, hev⟩ := level_radial_graph (hu.comp (continuous_id.add continuous_const))
    (fun y => capacitary_pos_everywhere hK hzero hu hh hb hinf _) hQc hQs hv0
    (lt_of_lt_of_le one_pos (le_max_right _ _))
    (fun y hy => (hbound y (by have := (le_max_left (R + 1) 1).trans hy; linarith)).1)
    hgrad
  obtain ⟨Bq, hBq0, hBq⟩ := polar_homogeneous_bound hQc hQs
  -- constants
  obtain ⟨Bk, hBk⟩ : ∃ Bk : ℝ, Bk = Bq / v 0 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = A * v 0 ^ 2 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 2 * (A₁ + Bk ^ 2 + Bk * A₁) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = |M| + (B + |M|) ^ 2 / v 0 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 3 * H + 46 * Bk * (H + Bk) := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = max (R + 1) 1 := ⟨_, rfl⟩
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hR₁1 : 1 ≤ R₁ := by rw [hR₁]; exact le_max_right _ _
  refine ⟨(32 * D + v 0 * K₂) / v 0 ^ 5, by positivity, ?_⟩
  have e2 := level_eventually_lt_of_continuous (g := fun t => t / v 0)
    (continuous_id.div_const _) (by simp) one_pos
  have e3 := level_eventually_lt_of_continuous (g := fun t => t / v 0 * (Bk + A₁))
    ((continuous_id.div_const _).mul continuous_const) (by simp)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have e4 := level_eventually_lt_of_continuous (g := fun t => 2 * (t / v 0) * R₁)
    ((continuous_const.mul (continuous_id.div_const _)).mul continuous_const) (by simp) one_pos
  have e5 := level_eventually_lt_of_continuous (g := fun t => (B + |M|) * (2 * (t / v 0)) ^ 2)
    (continuous_const.mul ((continuous_const.mul (continuous_id.div_const _)).pow 2))
    (by simp) (by positivity : 0 < v 0 / 2)
  filter_upwards [hev, self_mem_nhdsWithin, e2, e3, e4, e5] with t ht htpos h2 h3 h4 h5
  intro θ hθ s hs hut
  simp only [mem_Ioi] at htpos
  obtain ⟨s₀, _, _, hbd, huniq⟩ := ht θ hθ
  have hss : s = s₀ := huniq s hs hut
  rw [← hss] at hbd
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t / v 0 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = kelvinTranslatedQuadrupole v θ / v 0 := ⟨_, rfl⟩
  rw [← ha] at h2 h3 h4 h5
  have hapos : 0 < a := by rw [ha]; positivity
  have hθ0 : θ ≠ 0 := by intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
  have hQθ : |kelvinTranslatedQuadrupole v θ| ≤ Bq := by simpa [hθ] using hBq θ hθ0
  have hkB : |k| ≤ Bk := by
    rw [hk, hBk, abs_div, abs_of_pos hv0]
    exact div_le_div_of_nonneg_right hQθ hv0.le
  have hs' : |s - (1 / a + a * k)| ≤ A₁ * a ^ 2 := by
    have q1 : 1 / a + a * k = v 0 / t + t * kelvinTranslatedQuadrupole v θ / v 0 ^ 2 := by
      rw [ha, hk]; field_simp
    have q2 : A₁ * a ^ 2 = A * t ^ 2 := by rw [hA₁, ha]; field_simp
    rw [q1, q2]; exact hbd
  obtain ⟨hεpos, hε2a, hεexp⟩ :=
    level_inv_radius_expansion hapos h2.le hBk0 hA₁0 h3.le hkB hs'
  rw [← hH] at hεexp
  have hval := level_value_expansion hapos h2.le hBk0 hH0 hkB hεpos hε2a hεexp
  rw [← hK₂] at hval
  -- the radial point is in the far region
  have h2as : 1 ≤ 2 * a * s := by
    have := mul_le_mul_of_nonneg_right hε2a hs.le
    rwa [inv_mul_cancel₀ hs.ne'] at this
  have hsR : R₁ ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_left h2as (by linarith : (0 : ℝ) ≤ R₁),
      mul_le_mul_of_nonneg_right h4.le hs.le]
  have hny : ‖s • θ‖ = s := by
    rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  obtain ⟨_, hg, hWM, hfB⟩ := hdecomp (s • θ) (by rw [hny, ← hR₁]; exact hsR)
  rw [hny] at hg hWM hfB
  -- the gradient of the translate
  have hgu : gradient u (s • θ + (v 0)⁻¹ • gradient v 0) = gradient U (s • θ) := by
    simp only [U, gradient]
    rw [fderiv_comp_add_right]
  -- Euler's identity for the quadrupole potential
  have hy0 : s • θ ≠ 0 := smul_ne_zero hs.ne' hθ0
  have heul := inner_gradient_farQuadrupole (translated_quadrupole_contDiff v) hQs hy0
  have hfθ : ⟪gradient f (s • θ), θ⟫ = -3 * kelvinTranslatedQuadrupole v θ * s⁻¹ ^ 4 := by
    have h1 : ⟪s • θ, gradient f (s • θ)⟫ =
        -3 * (kelvinTranslatedQuadrupole v (s • θ) / ‖s • θ‖ ^ 5) := heul
    rw [real_inner_smul_left, hny, kelvinTranslatedQuadrupole_smul, real_inner_comm] at h1
    apply mul_left_cancel₀ hs.ne'
    rw [h1]
    field_simp
  have h2a : 2 * a ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hR₁1 (by positivity : (0 : ℝ) ≤ 2 * a)
    linarith
  have hε1 : s⁻¹ ≤ 1 := hε2a.trans h2a
  have hsmall : (B + |M|) * s⁻¹ ^ 2 ≤ v 0 / 2 := by
    have : s⁻¹ ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hεpos.le hε2a 2
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ B + |M|)
    linarith
  have hvec := level_grad_vector_expansion (C := v 0) (B := B) (M := |M|)
    (q := kelvinTranslatedQuadrupole v θ) (ε := s⁻¹) (θ := θ) (v := gradient U (s • θ))
    (w₁ := gradient f (s • θ)) (w₂ := gradient W (s • θ)) hv0 hεpos hε1 (abs_nonneg M)
    hsmall hθ (by
      rw [add_comm (gradient f (s • θ)), ← hg, smul_smul]
      congr 2
      field_simp)
    (by rw [inv_pow, ← div_eq_mul_inv]; exact hfB) hfθ
    (by rw [inv_pow, ← div_eq_mul_inv]; exact hWM)
  rw [← hD] at hvec
  rw [hgu]
  have q3 : t ^ 2 / v 0 + t ^ 4 * kelvinTranslatedQuadrupole v θ / v 0 ^ 4 =
      v 0 * (a ^ 2 + k * a ^ 4) := by
    rw [ha, hk]; field_simp
  have q4 : v 0 * s⁻¹ ^ 2 + 3 * kelvinTranslatedQuadrupole v θ * s⁻¹ ^ 4 =
      v 0 * (s⁻¹ ^ 2 + 3 * k * s⁻¹ ^ 4) := by
    rw [hk]; field_simp
  have q5 : (32 * D + v 0 * K₂) / v 0 ^ 5 * t ^ 5 = (32 * D + v 0 * K₂) * a ^ 5 := by
    rw [ha]; field_simp
  rw [q3, q5]
  rw [q4] at hvec
  have hε5 : s⁻¹ ^ 5 ≤ (2 * a) ^ 5 := pow_le_pow_left₀ hεpos.le hε2a 5
  have hsplit : ‖gradient U (s • θ)‖ - v 0 * (a ^ 2 + k * a ^ 4) =
      (‖gradient U (s • θ)‖ - v 0 * (s⁻¹ ^ 2 + 3 * k * s⁻¹ ^ 4)) +
        v 0 * (s⁻¹ ^ 2 + 3 * k * s⁻¹ ^ 4 - (a ^ 2 + k * a ^ 4)) := by ring
  rw [hsplit]
  calc _ ≤ |‖gradient U (s • θ)‖ - v 0 * (s⁻¹ ^ 2 + 3 * k * s⁻¹ ^ 4)| +
        |v 0 * (s⁻¹ ^ 2 + 3 * k * s⁻¹ ^ 4 - (a ^ 2 + k * a ^ 4))| := abs_add_le _ _
    _ ≤ D * s⁻¹ ^ 5 + v 0 * (K₂ * a ^ 5) := by
        rw [abs_mul, abs_of_pos hv0]
        exact add_le_add hvec (mul_le_mul_of_nonneg_left hval hv0.le)
    _ ≤ D * (2 * a) ^ 5 + v 0 * (K₂ * a ^ 5) := by
        gcongr
    _ = (32 * D + v 0 * K₂) * a ^ 5 := by ring

end LiquidDrop.CapacitaryK
