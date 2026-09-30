module

public import NoCompromise.CapacitaryK.LevelGradExpansion

@[expose] public section

/-!
# The area density of small capacitary levels

Chapter 31, `lem:K-level-asymptotics`, pointwise form of `eq:K-dA`: on the level
`{u = t}`, written as the radial graph `s • θ + z` about the normalized dipole center
`z`, the area density with respect to `dθ` is `s² |∇u| / |⟪∇u, θ⟫|`, and
`s² |∇u| / |⟪∇u, θ⟫| = C²/t² + 2 Q(θ)/C + O(t)` uniformly in `θ`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- A vector `-(C ε²) θ + w` with `‖w‖ ≤ β ε⁴` points inward along `θ`, and its length
exceeds the length of its radial component by a relative error `O(ε⁴)`. -/
theorem level_grad_ratio_expansion {C β ε : ℝ} {θ v : E3} (hC : 0 < C) (hε : 0 < ε)
    (hsmall : β * ε ^ 2 ≤ C / 2) (hθ : ‖θ‖ = 1)
    (hw : ‖v + (C * ε ^ 2) • θ‖ ≤ β * ε ^ 4) :
    ⟪v, θ⟫ < 0 ∧ |‖v‖ / |⟪v, θ⟫| - 1| ≤ 2 * β ^ 2 / C ^ 2 * ε ^ 4 := by
  set c := C * ε ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set w := v + c • θ with hwdef
  have hvw : v = w - c • θ := by rw [hwdef]; abel
  have hwθ : |⟪w, θ⟫| ≤ ‖w‖ := by
    simpa [hθ] using abs_real_inner_le_norm w θ
  have hβ : 0 ≤ β * ε ^ 4 := (norm_nonneg w).trans hw
  have h1 : β * ε ^ 4 ≤ c / 2 := by
    rw [hc]
    have : β * ε ^ 4 = (β * ε ^ 2) * ε ^ 2 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hsmall (by positivity : (0 : ℝ) ≤ ε ^ 2)
    linarith
  set a := c - ⟪w, θ⟫ with ha
  have hvθ : ⟪v, θ⟫ = -a := by
    rw [hvw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hθ, ha]
    ring
  have hahalf : c / 2 ≤ a := by
    have := (abs_le.mp (hwθ.trans (hw.trans h1))).2
    rw [ha]; linarith
  have hapos : 0 < a := by linarith
  refine ⟨by rw [hvθ]; linarith, ?_⟩
  rw [hvθ, abs_neg, abs_of_pos hapos]
  have hnsq : ‖v‖ ^ 2 = a ^ 2 + (‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2) := by
    rw [hvw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hθ, Real.norm_eq_abs,
      mul_one, sq_abs, ha]
    ring
  have hdiff0 : 0 ≤ ‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2 := by
    have : ⟪w, θ⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [sq_le_sq, abs_norm]; exact hwθ
    linarith
  have hdiff1 : ‖w‖ ^ 2 - ⟪w, θ⟫ ^ 2 ≤ (β * ε ^ 4) ^ 2 := by
    have : ‖w‖ ^ 2 ≤ (β * ε ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith [sq_nonneg ⟪w, θ⟫]
  have hva : a ≤ ‖v‖ := by
    nlinarith [norm_nonneg v]
  have hprod : (‖v‖ - a) * c ≤ (β * ε ^ 4) ^ 2 := by
    have h1 : (‖v‖ - a) * (‖v‖ + a) ≤ (β * ε ^ 4) ^ 2 := by nlinarith
    have h2 : c ≤ ‖v‖ + a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ ‖v‖ - a)]
  have hsplit : ‖v‖ / a - 1 = (‖v‖ - a) / a := by field_simp
  have hnn : 0 ≤ ‖v‖ / a - 1 := by
    rw [hsplit]; exact div_nonneg (by linarith) hapos.le
  rw [abs_of_nonneg hnn, hsplit, div_le_iff₀ hapos]
  -- `(‖v‖ - a) ≤ β² ε⁸ / c = β² ε⁶ / C ≤ (2 β² ε⁴ / C²) a`
  have hkey : (β * ε ^ 4) ^ 2 = 2 * β ^ 2 / C ^ 2 * ε ^ 4 * (c / 2) * c := by
    rw [hc]; field_simp
  have hX : 0 ≤ 2 * β ^ 2 / C ^ 2 * ε ^ 4 := by positivity
  have h3 : (‖v‖ - a) * c ≤ (2 * β ^ 2 / C ^ 2 * ε ^ 4 * a) * c := by
    rw [hkey] at hprod
    have := mul_le_mul_of_nonneg_left hahalf hX
    nlinarith
  exact le_of_mul_le_mul_right h3 hcpos

/-- Squaring the radial expansion `s = C/t + t q/C² + O(t²)`. -/
theorem level_radius_sq_expansion {C q s t A Bq : ℝ} (hC : 0 < C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 ≤ A) (hq : |q| ≤ Bq) (hs : |s - (C / t + t * q / C ^ 2)| ≤ A * t ^ 2) :
    |s ^ 2 - (C ^ 2 / t ^ 2 + 2 * q / C)| ≤
      (Bq ^ 2 / C ^ 4 + 2 * A * C + 2 * A * Bq / C ^ 2 + A ^ 2) * t := by
  set e := s - (C / t + t * q / C ^ 2) with he
  have hse : s = C / t + t * q / C ^ 2 + e := by rw [he]; ring
  have hid : s ^ 2 - (C ^ 2 / t ^ 2 + 2 * q / C) =
      t ^ 2 * q ^ 2 / C ^ 4 + 2 * (C / t) * e + 2 * (t * q / C ^ 2) * e + e ^ 2 := by
    rw [hse]; field_simp; ring
  have hBq : 0 ≤ Bq := (abs_nonneg q).trans hq
  have hea : |e| ≤ A * t ^ 2 := hs
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith
  have ht4 : t ^ 4 ≤ t := by nlinarith [pow_le_one₀ ht.le ht1 (n := 3)]
  have b1 : |t ^ 2 * q ^ 2 / C ^ 4| ≤ Bq ^ 2 / C ^ 4 * t := by
    have hq2 : q ^ 2 ≤ Bq ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg q) hq 2
    rw [abs_of_nonneg (by positivity)]
    calc t ^ 2 * q ^ 2 / C ^ 4 ≤ t * Bq ^ 2 / C ^ 4 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul ht2 hq2 (sq_nonneg q) ht.le
      _ = Bq ^ 2 / C ^ 4 * t := by ring
  have b2 : |2 * (C / t) * e| ≤ 2 * A * C * t := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (C / t))]
    calc 2 * (C / t) * |e| ≤ 2 * (C / t) * (A * t ^ 2) :=
          mul_le_mul_of_nonneg_left hea (by positivity)
      _ = 2 * A * C * t := by field_simp
  have b3 : |2 * (t * q / C ^ 2) * e| ≤ 2 * A * Bq / C ^ 2 * t := by
    rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos ht,
      abs_of_pos (by positivity : (0 : ℝ) < C ^ 2), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * (t * |q| / C ^ 2) * |e| ≤ 2 * (t * Bq / C ^ 2) * (A * t ^ 2) := by
          apply mul_le_mul _ hea (abs_nonneg e) (by positivity)
          gcongr
      _ = 2 * A * Bq / C ^ 2 * t ^ 3 := by ring
      _ ≤ 2 * A * Bq / C ^ 2 * t := mul_le_mul_of_nonneg_left ht3 (by positivity)
  have b4 : |e ^ 2| ≤ A ^ 2 * t := by
    rw [abs_pow]
    calc |e| ^ 2 ≤ (A * t ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg e) hea 2
      _ = A ^ 2 * t ^ 4 := by ring
      _ ≤ A ^ 2 * t := mul_le_mul_of_nonneg_left ht4 (by positivity)
  rw [hid]
  calc _ ≤ |t ^ 2 * q ^ 2 / C ^ 4| + |2 * (C / t) * e| + |2 * (t * q / C ^ 2) * e| +
        |e ^ 2| := by
        have := abs_add_le (t ^ 2 * q ^ 2 / C ^ 4) (2 * (C / t) * e)
        have := abs_add_le (t ^ 2 * q ^ 2 / C ^ 4 + 2 * (C / t) * e) (2 * (t * q / C ^ 2) * e)
        have := abs_add_le (t ^ 2 * q ^ 2 / C ^ 4 + 2 * (C / t) * e + 2 * (t * q / C ^ 2) * e)
          (e ^ 2)
        linarith
    _ ≤ Bq ^ 2 / C ^ 4 * t + 2 * A * C * t + 2 * A * Bq / C ^ 2 * t + A ^ 2 * t := by
        linarith
    _ = _ := by ring

/-- `lem:K-level-asymptotics`, pointwise form of `eq:K-dA`: on the small level `{u = t}`, at
the radial point `x = s • θ + z` about the normalized dipole center `z = (v 0)⁻¹ • ∇v(0)`,
the gradient points strictly inward along `θ`, and the area density
`s² |∇u(x)| / |⟪∇u(x), θ⟫|` of the radial graph with respect to `dθ` equals
`C²/t² + 2 Q(θ)/C + O(t)` uniformly in `θ`, where `C = v 0` and
`Q = kelvinTranslatedQuadrupole v`. -/
theorem capacitary_level_area_density_expansion
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ θ : E3, ‖θ‖ = 1 → ∀ s : ℝ, 0 < s →
        u (s • θ + (v 0)⁻¹ • gradient v 0) = t →
        ⟪gradient u (s • θ + (v 0)⁻¹ • gradient v 0), θ⟫ < 0 ∧
        |s ^ 2 * ‖gradient u (s • θ + (v 0)⁻¹ • gradient v 0)‖ /
            |⟪gradient u (s • θ + (v 0)⁻¹ • gradient v 0), θ⟫| -
          ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0)| ≤ A * t := by
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
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ,
      Ks = Bq ^ 2 / v 0 ^ 4 + 2 * A * v 0 + 2 * A * Bq / v 0 ^ 2 + A ^ 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = B + |M| := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = max (R + 1) 1 := ⟨_, rfl⟩
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hR₁1 : 1 ≤ R₁ := by rw [hR₁]; exact le_max_right _ _
  refine ⟨Ks + 8 * β ^ 2 / v 0 ^ 4, by positivity, ?_⟩
  have e1 := level_eventually_lt_of_continuous (g := fun t => t) continuous_id rfl one_pos
  have e2 := level_eventually_lt_of_continuous (g := fun t => t / v 0)
    (continuous_id.div_const _) (by simp) one_pos
  have e3 := level_eventually_lt_of_continuous (g := fun t => t / v 0 * (Bk + A₁))
    ((continuous_id.div_const _).mul continuous_const) (by simp)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have e4 := level_eventually_lt_of_continuous (g := fun t => 2 * (t / v 0) * R₁)
    ((continuous_const.mul (continuous_id.div_const _)).mul continuous_const) (by simp) one_pos
  have e5 := level_eventually_lt_of_continuous (g := fun t => β * (2 * (t / v 0)) ^ 2)
    (continuous_const.mul ((continuous_const.mul (continuous_id.div_const _)).pow 2))
    (by simp) (by positivity : 0 < v 0 / 2)
  filter_upwards [hev, self_mem_nhdsWithin, e1, e2, e3, e4, e5] with t ht htpos h1 h2 h3 h4 h5
  intro θ hθ s hs hut
  simp only [mem_Ioi] at htpos
  obtain ⟨s₀, _, _, hbd, huniq⟩ := ht θ hθ
  have hss : s = s₀ := huniq s hs hut
  rw [← hss] at hbd
  have hθ0 : θ ≠ 0 := by intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
  have hQθ : |kelvinTranslatedQuadrupole v θ| ≤ Bq := by simpa [hθ] using hBq θ hθ0
  have hsq := level_radius_sq_expansion hv0 htpos h1.le hA hQθ hbd
  rw [← hKs] at hsq
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t / v 0 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = kelvinTranslatedQuadrupole v θ / v 0 := ⟨_, rfl⟩
  rw [← ha] at h2 h3 h4 h5
  have hapos : 0 < a := by rw [ha]; positivity
  have hkB : |k| ≤ Bk := by
    rw [hk, hBk, abs_div, abs_of_pos hv0]
    exact div_le_div_of_nonneg_right hQθ hv0.le
  have hs' : |s - (1 / a + a * k)| ≤ A₁ * a ^ 2 := by
    have q1 : 1 / a + a * k = v 0 / t + t * kelvinTranslatedQuadrupole v θ / v 0 ^ 2 := by
      rw [ha, hk]; field_simp
    have q2 : A₁ * a ^ 2 = A * t ^ 2 := by rw [hA₁, ha]; field_simp
    rw [q1, q2]; exact hbd
  obtain ⟨hεpos, hε2a, _⟩ :=
    level_inv_radius_expansion hapos h2.le hBk0 hA₁0 h3.le hkB hs'
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
  have hgu : gradient u (s • θ + (v 0)⁻¹ • gradient v 0) = gradient U (s • θ) := by
    simp only [U, gradient]
    rw [fderiv_comp_add_right]
  have h2a : 2 * a ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hR₁1 (by positivity : (0 : ℝ) ≤ 2 * a)
    linarith
  have hε1 : s⁻¹ ≤ 1 := hε2a.trans h2a
  have hsmall : β * s⁻¹ ^ 2 ≤ v 0 / 2 := by
    have : s⁻¹ ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hεpos.le hε2a 2
    have := mul_le_mul_of_nonneg_left this hβ0
    linarith
  have hw : ‖gradient U (s • θ) + (v 0 * s⁻¹ ^ 2) • θ‖ ≤ β * s⁻¹ ^ 4 := by
    have hvec : gradient U (s • θ) + (v 0 * s⁻¹ ^ 2) • θ =
        gradient W (s • θ) + gradient f (s • θ) := by
      rw [← hg, smul_smul]
      congr 2
      field_simp
    have hε54 : s⁻¹ ^ 5 ≤ s⁻¹ ^ 4 := pow_le_pow_of_le_one hεpos.le hε1 (by norm_num)
    rw [hvec, hβ]
    calc _ ≤ ‖gradient W (s • θ)‖ + ‖gradient f (s • θ)‖ := norm_add_le _ _
      _ ≤ |M| * s⁻¹ ^ 5 + B * s⁻¹ ^ 4 := by
          rw [inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv]
          exact add_le_add hWM hfB
      _ ≤ |M| * s⁻¹ ^ 4 + B * s⁻¹ ^ 4 := by
          have := mul_le_mul_of_nonneg_left hε54 (abs_nonneg M)
          linarith
      _ = (B + |M|) * s⁻¹ ^ 4 := by ring
  obtain ⟨hneg, hratio⟩ := level_grad_ratio_expansion hv0 hεpos hsmall hθ hw
  rw [hgu]
  refine ⟨hneg, ?_⟩
  set g := gradient U (s • θ)
  have hsplit : s ^ 2 * ‖g‖ / |⟪g, θ⟫| -
      (v 0 ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0) =
      (s ^ 2 - (v 0 ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0)) +
        s ^ 2 * (‖g‖ / |⟪g, θ⟫| - 1) := by ring
  have hrest : |s ^ 2 * (‖g‖ / |⟪g, θ⟫| - 1)| ≤ 8 * β ^ 2 / v 0 ^ 4 * t := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    have hε2 : s⁻¹ ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hεpos.le hε2a 2
    have ht2 : t ^ 2 ≤ t := by
      rw [sq]
      calc t * t ≤ t * 1 := mul_le_mul_of_nonneg_left h1.le htpos.le
        _ = t := mul_one t
    calc s ^ 2 * |‖g‖ / |⟪g, θ⟫| - 1| ≤ s ^ 2 * (2 * β ^ 2 / v 0 ^ 2 * s⁻¹ ^ 4) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg s)
      _ = 2 * β ^ 2 / v 0 ^ 2 * s⁻¹ ^ 2 := by field_simp
      _ ≤ 2 * β ^ 2 / v 0 ^ 2 * (2 * a) ^ 2 :=
          mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ = 8 * β ^ 2 / v 0 ^ 4 * t ^ 2 := by rw [ha]; field_simp; ring
      _ ≤ 8 * β ^ 2 / v 0 ^ 4 * t := mul_le_mul_of_nonneg_left ht2 (by positivity)
  rw [hsplit]
  calc _ ≤ |s ^ 2 - (v 0 ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0)| +
        |s ^ 2 * (‖g‖ / |⟪g, θ⟫| - 1)| := abs_add_le _ _
    _ ≤ Ks * t + 8 * β ^ 2 / v 0 ^ 4 * t := add_le_add hsq hrest
    _ = (Ks + 8 * β ^ 2 / v 0 ^ 4) * t := by ring

end LiquidDrop.CapacitaryK
