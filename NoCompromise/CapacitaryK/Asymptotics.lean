import NoCompromise.CapacitaryK.OneDim
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Far-field normalisation (chapter 31, `lem:K-far-field`, limit step)

`lem:K-far-field` states `F(t) = 4πt² + O(t⁵)` and `F'(t) = 8πt + O(t⁴)` as `t ↓ 0`, and deduces the
limits `eq:K-far-field-limits`:
`(F(t) - 4πt²)/t⁴ → 0` and `F'(t) - 4F(t)/t + 8πt → 0`.

This file proves the deduction of the limits from the two expansions (`K_far_field_limits`), with
`p` in place of `F'` (all small levels are regular and `p = F'` there, `prop:K-structure`), so that
the second limit is exactly `levelH F p → 0`, the hypothesis `hh0` of
`CapacitaryK.K_two_ineq_core`. `F_expansion_of_p_expansion` derives `F(t) = 4πt² + O(t⁵)` from
`F' = p`, `F(0+) = 0` and `eq:K-p-expansion` `p(t) = 8πt + O(t⁴)`. The `p`-expansion itself (from
`lem:K-level-asymptotics`) is not formalised here.
-/

noncomputable section

open Real Set Filter Asymptotics Topology

namespace LiquidDrop.CapacitaryK

/-- `lem:K-far-field`, limit step: from `F(t) = 4πt² + O(t⁵)` and `p(t) = 8πt + O(t⁴)` as `t ↓ 0`,
`(F(t) - 4πt²)/t⁴ → 0` and `h(t) = p(t) - 4F(t)/t + 8πt → 0` (`eq:K-far-field-limits`). -/
theorem K_far_field_limits {F p : ℝ → ℝ}
    (hF : (fun t => F t - 4 * π * t ^ 2) =O[𝓝[>] 0] (fun t => t ^ 5))
    (hp : (fun t => p t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4)) :
    Tendsto (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (levelH F p) (𝓝[>] 0) (𝓝 0) := by
  have hne : ∀ᶠ t in 𝓝[>] (0:ℝ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht using ne_of_gt ht
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  -- `(F - 4πt²)/t⁴ = O(t)`.
  have hz : (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) =O[𝓝[>] 0] (fun t => t) := by
    have h1 := hF.mul (isBigO_refl (fun t : ℝ => (t ^ 4)⁻¹) (𝓝[>] 0))
    refine (h1.congr' ?_ ?_)
    · exact Eventually.of_forall fun t => by simp [div_eq_mul_inv]
    · filter_upwards [hne] with t ht
      field_simp
  -- `(F - 4πt²)/t = O(t⁴)`.
  have hz' : (fun t => (F t - 4 * π * t ^ 2) / t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
    have h1 := hF.mul (isBigO_refl (fun t : ℝ => t⁻¹) (𝓝[>] 0))
    refine (h1.congr' ?_ ?_)
    · exact Eventually.of_forall fun t => by simp [div_eq_mul_inv]
    · filter_upwards [hne] with t ht
      field_simp
  have h4 : Tendsto (fun t : ℝ => t ^ 4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hid.pow 4
  refine ⟨hz.trans_tendsto hid, ?_⟩
  have hsum : Tendsto (fun t => (p t - 8 * π * t) - 4 * ((F t - 4 * π * t ^ 2) / t))
      (𝓝[>] (0:ℝ)) (𝓝 (0 - 4 * 0)) :=
    (hp.trans_tendsto h4).sub ((hz'.trans_tendsto h4).const_mul 4)
  rw [show (0:ℝ) - 4 * 0 = 0 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [hne] with t ht
  simp only [levelH]
  field_simp
  ring

/-- `lem:K-far-field`, the `F`-expansion from `F' = p` and `eq:K-p-expansion`: if `F` is a
primitive of `p` on `(0,1)`, `F(t) → 0` as `t ↓ 0`, and `p(t) = 8πt + O(t⁴)`, then
`F(t) = 4πt² + O(t⁵)`. -/
theorem F_expansion_of_p_expansion {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p MeasureTheory.volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hF0 : Tendsto F (𝓝[>] 0) (𝓝 0))
    (hp : (fun t => p t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4)) :
    (fun t => F t - 4 * π * t ^ 2) =O[𝓝[>] 0] (fun t => t ^ 5) := by
  obtain ⟨C, hC0, hC⟩ := hp.exists_nonneg
  rw [IsBigOWith_def] at hC
  obtain ⟨δ, hδ, hδs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC
  set δ' := min δ (1 / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hbound : ∀ t, 0 < t → t < δ' → |p t - 8 * π * t| ≤ C * t ^ 4 := by
    intro t ht0 ht1
    have := hδs ⟨ht0, lt_of_lt_of_le ht1 (min_le_left _ _)⟩
    simpa [Real.norm_eq_abs, abs_of_pos ht0] using this
  have hmain : ∀ b, 0 < b → b < δ' → |F b - 4 * π * b ^ 2| ≤ C * b ^ 5 := by
    intro b hb0 hb1
    have hstep : ∀ a, 0 < a → a < b →
        |F b - F a - 4 * π * (b ^ 2 - a ^ 2)| ≤ C * b ^ 5 := by
      intro a ha hab
      have hb1' : b < 1 := hb1.trans hδ'1
      have hlin : IntervalIntegrable (fun t : ℝ => 8 * π * t) MeasureTheory.volume a b :=
        (continuous_const.mul continuous_id).intervalIntegrable a b
      have hint : ∫ t in a..b, (p t - 8 * π * t) = F b - F a - 4 * π * (b ^ 2 - a ^ 2) := by
        rw [intervalIntegral.integral_sub (hpint a b ha hab.le hb1') hlin,
          intervalIntegral.integral_const_mul, integral_id, hF a b ha hab.le hb1']
        ring
      rw [← hint]
      have hle : ∀ t ∈ Set.uIoc a b, ‖p t - 8 * π * t‖ ≤ C * b ^ 4 := by
        intro t ht
        rw [uIoc_of_le hab.le] at ht
        rw [Real.norm_eq_abs]
        refine (hbound t (ha.trans ht.1) (lt_of_le_of_lt ht.2 hb1)).trans ?_
        have : t ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ (ha.trans ht.1).le ht.2 4
        nlinarith
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
      rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at h
      calc _ ≤ C * b ^ 4 * (b - a) := h
        _ ≤ C * b ^ 4 * b := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = C * b ^ 5 := by ring
    have hlim : Tendsto (fun a => |F b - F a - 4 * π * (b ^ 2 - a ^ 2)|) (𝓝[>] 0)
        (𝓝 |F b - 0 - 4 * π * (b ^ 2 - 0 ^ 2)|) := by
      have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      exact ((tendsto_const_nhds.sub hF0).sub
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hid.pow 2)))).abs
    have hfin : |F b - 0 - 4 * π * (b ^ 2 - 0 ^ 2)| ≤ C * b ^ 5 := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT hb0] with a ha
      exact hstep a ha.1 ha.2
    simpa using hfin
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT hδ'0] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht.1 5)]
  exact hmain t ht.1 ht.2

end LiquidDrop.CapacitaryK
