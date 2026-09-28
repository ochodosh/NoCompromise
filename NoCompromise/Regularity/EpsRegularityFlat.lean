import NoCompromise.Regularity.Excess
import NoCompromise.Regularity.OmegaMinimal
import NoCompromise.BV.CoareaCoordinates
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Boundary flatness and differentiability of Lipschitz graphs -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- A convergent excess iteration and a general height bound give flatness at the center. -/
theorem boundary_flatness_of_iteration
    (hH : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ)
      (hE : IsOmegaMinimal E ω) (p ν : AmbientSpace) (s : ℝ),
      p ∈ frontier (densityOne E) → ‖ν‖ = 1 → 0 < s → s ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable p s ν + ω * s ≤ ε →
      ∀ y ∈ frontier (densityOne E) ∩ cylinder p (3 * s / 4) ν,
        |inner ℝ ν (y - p)| < η * s)
    (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω) (p : AmbientSpace)
    (hp : p ∈ frontier (densityOne E)) {θ C T s₀ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs₀ : 0 < s₀) (hs₀1 : s₀ ≤ 1) {ν : ℕ → AmbientSpace} {ℓ : AmbientSpace}
    (hν : ∀ j, ‖ν j‖ = 1) (hlim : Tendsto ν atTop (𝓝 ℓ))
    (hdecay : ∀ j, cylindricalExcess E hE.locallyFinite hE.nullMeasurable p (θ ^ j * s₀) (ν j)
      + ω * (θ ^ j * s₀) ≤ C * θ ^ j * T) :
    ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ frontier (densityOne E), ‖q - p‖ < ρ →
      |inner ℝ ℓ (q - p)| ≤ δ * ‖q - p‖ := by
  intro δ hδ
  obtain ⟨ε, hε, hheight⟩ := hH (δ * θ / 4) (by positivity)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1
  have hsmall : ∀ᶠ j : ℕ in atTop, C * θ ^ j * T < ε := by
    have ht : Tendsto (fun j : ℕ => C * θ ^ j * T) atTop (𝓝 0) := by
      simpa using (hpow.const_mul C).mul_const T
    exact ht.eventually (gt_mem_nhds hε)
  have hnormal : ∀ᶠ j : ℕ in atTop, ‖ν j - ℓ‖ < δ / 2 := by
    have ht : Tendsto (fun j => ‖ν j - ℓ‖) atTop (𝓝 0) := by
      simpa using (hlim.sub (tendsto_const_nhds (x := ℓ))).norm
    exact ht.eventually (gt_mem_nhds (by positivity : 0 < δ / 2))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsmall.and hnormal)
  refine ⟨θ ^ J * s₀ / 2, by positivity, ?_⟩
  intro q hq hqp
  by_cases hzero : q - p = 0
  · simp [hzero]
  have hnorm : 0 < ‖q - p‖ := norm_pos_iff.mpr hzero
  have hex : ∃ m : ℕ, θ ^ m * s₀ / 2 ≤ ‖q - p‖ := by
    have ht : Tendsto (fun m : ℕ => θ ^ m * s₀ / 2) atTop (𝓝 0) := by
      simpa using (hpow.mul_const s₀).div_const 2
    obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hnorm)).exists
    exact ⟨m, hm.le⟩
  let m := Nat.find hex
  have hm : θ ^ m * s₀ / 2 ≤ ‖q - p‖ := Nat.find_spec hex
  have hJm : J < m := by
    by_contra hn
    have hpowle : θ ^ J ≤ θ ^ m := pow_le_pow_of_le_one hθ.le hθ1.le (by omega)
    have := mul_le_mul_of_nonneg_right hpowle hs₀.le
    linarith
  have hmpos : 0 < m := by omega
  let j := m - 1
  have hj : J ≤ j := by omega
  have hjm : j + 1 = m := by omega
  have hprev : ‖q - p‖ < θ ^ j * s₀ / 2 := by
    exact lt_of_not_ge (Nat.find_min hex (show j < m by omega))
  have hs : 0 < θ ^ j * s₀ := by positivity
  have hs1 : θ ^ j * s₀ ≤ 1 := by
    calc
      θ ^ j * s₀ ≤ 1 * s₀ := mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hs₀.le
      _ ≤ 1 := by simpa using hs₀1
  have hqc : q ∈ cylinder p (3 * (θ ^ j * s₀) / 4) (ν j) := by
    apply ball_subset_cylinder p _ (hν j)
    change ‖q - p‖ < _
    linarith
  have hh := hheight E ω hE p (ν j) (θ ^ j * s₀) hp (hν j) hs hs1
    ((hdecay j).trans (hJ j hj).1.le) q ⟨hq, hqc⟩
  have hlower : θ * (θ ^ j * s₀) / 2 ≤ ‖q - p‖ := by
    rw [← hjm, pow_succ] at hm
    nlinarith [hm]
  have hhalf : |inner ℝ (ν j) (q - p)| ≤ δ / 2 * ‖q - p‖ := by
    have := mul_le_mul_of_nonneg_left hlower (show 0 ≤ δ / 2 by positivity)
    nlinarith
  have herror : |inner ℝ (ℓ - ν j) (q - p)| ≤ δ / 2 * ‖q - p‖ := by
    calc
      _ ≤ ‖ℓ - ν j‖ * ‖q - p‖ := abs_real_inner_le_norm _ _
      _ ≤ δ / 2 * ‖q - p‖ := by
        rw [norm_sub_rev ℓ]
        exact mul_le_mul_of_nonneg_right (hJ j hj).2.le hnorm.le
  calc
    |inner ℝ ℓ (q - p)| = |inner ℝ (ν j) (q - p) + inner ℝ (ℓ - ν j) (q - p)| := by
      congr 1
      rw [inner_sub_left]
      ring
    _ ≤ |inner ℝ (ν j) (q - p)| + |inner ℝ (ℓ - ν j) (q - p)| := abs_add_le _ _
    _ ≤ δ * ‖q - p‖ := by linarith

private lemma flat_projection_norm_le (v : AmbientSpace) : ‖graphProjectionN 2 v‖ ≤ ‖v‖ := by
  have h := norm_sq_graphProjectionN v
  nlinarith [sq_nonneg (v (Fin.last 2)), norm_nonneg v, norm_nonneg (graphProjectionN 2 v)]

private lemma flat_last_abs_le (v : AmbientSpace) : |v 2| ≤ ‖v‖ := by
  have h := norm_sq_graphProjectionN v
  change ‖v‖ ^ 2 = ‖graphProjectionN 2 v‖ ^ 2 + (v 2) ^ 2 at h
  nlinarith [sq_nonneg ‖graphProjectionN 2 v‖, sq_abs (v 2), abs_nonneg (v 2), norm_nonneg v]

/-- Normals with positive last coordinates determine quantitatively close graph slopes. -/
theorem graphSlope_sub_norm_le {a b : AmbientSpace} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha2 : 1 / 2 ≤ a 2) (hb2 : 1 / 2 ≤ b 2) :
    ‖(-(a 2)⁻¹ • innerSL ℝ (graphProjectionN 2 a)) -
        (-(b 2)⁻¹ • innerSL ℝ (graphProjectionN 2 b))‖ ≤ 8 * ‖a - b‖ := by
  have ha0 : 0 < a 2 := by linarith
  have hb0 : 0 < b 2 := by linarith
  have hai : (a 2)⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) ha2
    norm_num [one_div] at this ⊢
    exact this
  have hbi : (b 2)⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb2
    norm_num [one_div] at this ⊢
    exact this
  have hinv : |(b 2)⁻¹ - (a 2)⁻¹| ≤ 4 * ‖a - b‖ := by
    have heq : (b 2)⁻¹ - (a 2)⁻¹ = (a 2)⁻¹ * (b 2)⁻¹ * (a 2 - b 2) := by
      field_simp [ne_of_gt ha0, ne_of_gt hb0]
    rw [heq, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha0), abs_of_pos (inv_pos.mpr hb0)]
    have hab : |a 2 - b 2| ≤ ‖a - b‖ := flat_last_abs_le (a - b)
    have hi : (a 2)⁻¹ * (b 2)⁻¹ ≤ 4 := by
      calc
        _ ≤ 2 * 2 := mul_le_mul hai hbi (inv_nonneg.mpr hb0.le) (by norm_num)
        _ = 4 := by norm_num
    exact (mul_le_mul_of_nonneg_left hab (by positivity)).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have hproj : ‖graphProjectionN 2 a - graphProjectionN 2 b‖ ≤ ‖a - b‖ := by
    simpa only [map_sub] using flat_projection_norm_le (a - b)
  have hpb : ‖graphProjectionN 2 b‖ ≤ 1 := (flat_projection_norm_le b).trans hb.le
  have heq : (-(a 2)⁻¹ • innerSL ℝ (graphProjectionN 2 a)) -
      (-(b 2)⁻¹ • innerSL ℝ (graphProjectionN 2 b)) =
      innerSL ℝ (-(a 2)⁻¹ • (graphProjectionN 2 a - graphProjectionN 2 b) +
        ((b 2)⁻¹ - (a 2)⁻¹) • graphProjectionN 2 b) := by
    ext z
    simp only [sub_apply, smul_apply,
      innerSL_apply_apply, inner_add_left, inner_sub_left, real_inner_smul_left, smul_eq_mul]
    ring
  rw [heq, innerSL_apply_norm]
  calc
    _ ≤ ‖-(a 2)⁻¹ • (graphProjectionN 2 a - graphProjectionN 2 b)‖ +
        ‖((b 2)⁻¹ - (a 2)⁻¹) • graphProjectionN 2 b‖ := norm_add_le _ _
    _ = (a 2)⁻¹ * ‖graphProjectionN 2 a - graphProjectionN 2 b‖ +
        |(b 2)⁻¹ - (a 2)⁻¹| * ‖graphProjectionN 2 b‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
    _ ≤ 2 * ‖a - b‖ + (4 * ‖a - b‖) * 1 :=
      add_le_add (mul_le_mul hai hproj (norm_nonneg _) (by positivity))
        (mul_le_mul hinv hpb (norm_nonneg _) (by positivity))
    _ ≤ 8 * ‖a - b‖ := by nlinarith [norm_nonneg (a - b)]

private lemma flat_graphAppend_sub (y x : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    graphAppendN y t - graphAppendN x s = graphAppendN (y - x) (t - s) := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change graphAppendN y t (Fin.last 2) - graphAppendN x s (Fin.last 2) =
      graphAppendN (y - x) (t - s) (Fin.last 2)
    simp only [graphAppendN_last]
  · simp

/-- Flatness of a Lipschitz graph with a transverse normal gives its derivative. -/
theorem hasFDerivAt_of_graph_flat {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hfL : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ ‖x - y‖)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) {ℓ : AmbientSpace} (hℓ : 0 < ℓ 2)
    (hflat : ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ U,
      ‖graphAppendN y (f y) - graphAppendN x (f x)‖ < ρ →
      |inner ℝ ℓ (graphAppendN y (f y) - graphAppendN x (f x))| ≤
        δ * ‖graphAppendN y (f y) - graphAppendN x (f x)‖) :
    HasFDerivAt f (-(ℓ 2)⁻¹ • (innerSL ℝ (graphProjectionN 2 ℓ))) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hr⟩ := hflat (ε * ℓ 2 / 2) (by positivity)
  filter_upwards [hU.mem_nhds hx, ball_mem_nhds x (half_pos hρ)] with y hy hyd
  have hydist : ‖y - x‖ < ρ / 2 := hyd
  have hgraph : ‖graphAppendN y (f y) - graphAppendN x (f x)‖ ≤ 2 * ‖y - x‖ := by
    rw [flat_graphAppend_sub]
    have hn := norm_sq_graphProjectionN (graphAppendN (y - x) (f y - f x))
    simp only [graphProjectionN_append, graphAppendN_last] at hn
    have hl := hfL y hy x hx
    have hsq : (f y - f x) ^ 2 ≤ ‖y - x‖ ^ 2 := by
      nlinarith [sq_abs (f y - f x), abs_nonneg (f y - f x), norm_nonneg (y - x)]
    nlinarith [norm_nonneg (graphAppendN (y - x) (f y - f x)), norm_nonneg (y - x),
      sq_nonneg ‖y - x‖]
  have hh := hr y hy (by linarith : ‖graphAppendN y (f y) - graphAppendN x (f x)‖ < ρ)
  have heq : ℓ 2 * (f y - f x -
      (-(ℓ 2)⁻¹ • innerSL ℝ (graphProjectionN 2 ℓ)) (y - x)) =
      inner ℝ ℓ (graphAppendN y (f y) - graphAppendN x (f x)) := by
    rw [flat_graphAppend_sub, inner_graphAppendN]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    change ℓ 2 * (f y - f x - (-(ℓ 2)⁻¹ * inner ℝ (graphProjectionN 2 ℓ) (y - x))) =
      inner ℝ (graphProjectionN 2 ℓ) (y - x) + ℓ 2 * (f y - f x)
    field_simp [ne_of_gt hℓ]
    ring
  rw [← heq, abs_mul, abs_of_pos hℓ] at hh
  rw [Real.norm_eq_abs]
  apply (mul_le_mul_iff_right₀ hℓ).mp
  calc
    _ ≤ (ε * ℓ 2 / 2) * ‖graphAppendN y (f y) - graphAppendN x (f x)‖ := hh
    _ ≤ (ε * ℓ 2 / 2) * (2 * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hgraph (by positivity)
    _ = _ := by ring

end LiquidDrop
