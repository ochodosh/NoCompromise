module

public import NoCompromise.Energy.Scaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Elementary dilation quotients

The quotients have removable values at one. Explicit bounds on the larger
interval `[0,2]` are convenient for a quantitative volume penalty.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma dilation_quotient_two_eq {r : ℝ} (hr : 0 ≤ r) (hne : r ≠ 1) :
    |r ^ 2 - 1| / |r ^ 3 - 1| = (r + 1) / (r ^ 2 + r + 1) := by
  have hd : 0 < r ^ 2 + r + 1 := by positivity
  rw [show r ^ 2 - 1 = (r - 1) * (r + 1) by ring,
    show r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r + 1), abs_of_pos hd]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr (sub_ne_zero.mpr hne))

lemma dilation_quotient_five_eq {r : ℝ} (hr : 0 ≤ r) (hne : r ≠ 1) :
    |r ^ 5 - 1| / |r ^ 3 - 1| =
      (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) / (r ^ 2 + r + 1) := by
  have hd : 0 < r ^ 2 + r + 1 := by positivity
  have hn : 0 ≤ r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by positivity
  rw [show r ^ 5 - 1 = (r - 1) * (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) by ring,
    show r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) by ring,
    abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos hd]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr (sub_ne_zero.mpr hne))

lemma abs_dilation_two_sub_one_le {r : ℝ} (hr : 0 ≤ r) (_hR : r ≤ 2) :
    |r ^ 2 - 1| ≤ 3 * |r ^ 3 - 1| := by
  rw [show r ^ 2 - 1 = (r - 1) * (r + 1) by ring,
    show r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r + 1),
    abs_of_nonneg (by positivity : 0 ≤ r ^ 2 + r + 1)]
  have h := mul_le_mul_of_nonneg_left
    (show r + 1 ≤ 3 * (r ^ 2 + r + 1) by nlinarith [sq_nonneg r]) (abs_nonneg (r - 1))
  nlinarith only [h]

lemma abs_dilation_five_sub_one_le {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ 2) :
    |r ^ 5 - 1| ≤ 31 * |r ^ 3 - 1| := by
  have h2 : r ^ 2 ≤ 4 := by nlinarith
  have h3 : r ^ 3 ≤ 8 := by nlinarith [mul_le_mul h2 hR hr (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : r ^ 4 ≤ 16 := by nlinarith [sq_nonneg (r ^ 2)]
  rw [show r ^ 5 - 1 = (r - 1) * (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) by ring,
    show r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 4 + r ^ 3 + r ^ 2 + r + 1),
    abs_of_nonneg (by positivity : 0 ≤ r ^ 2 + r + 1)]
  have h := mul_le_mul_of_nonneg_left
    (show r ^ 4 + r ^ 3 + r ^ 2 + r + 1 ≤ 31 * (r ^ 2 + r + 1) by nlinarith [sq_nonneg r])
    (abs_nonneg (r - 1))
  nlinarith only [h]

/-- Blueprint `lem:dilation-quotients`: the limits are the removable values,
with explicit bounds on a fixed neighborhood of one. -/
theorem dilation_quotients :
    Tendsto (fun r : ℝ => |r ^ 2 - 1| / |r ^ 3 - 1|) (𝓝[≠] 1) (𝓝 (2 / 3 : ℝ)) ∧
      Tendsto (fun r : ℝ => |r ^ 5 - 1| / |r ^ 3 - 1|) (𝓝[≠] 1) (𝓝 (5 / 3 : ℝ)) ∧
      ∀ r ∈ Icc (1 / 2 : ℝ) 2,
        |r ^ 2 - 1| / |r ^ 3 - 1| ≤ 3 ∧ |r ^ 5 - 1| / |r ^ 3 - 1| ≤ 31 := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[≠] 1, 0 ≤ r :=
    nhdsWithin_le_nhds (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1))
  have hne : ∀ᶠ r : ℝ in 𝓝[≠] 1, r ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hr
  have ht2 : Tendsto (fun r : ℝ => (r + 1) / (r ^ 2 + r + 1)) (𝓝[≠] 1)
      (𝓝 (2 / 3 : ℝ)) := by
    have hc : ContinuousAt (fun r : ℝ => (r + 1) / (r ^ 2 + r + 1)) 1 := by
      fun_prop (disch := norm_num)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have ht5 : Tendsto (fun r : ℝ =>
      (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) / (r ^ 2 + r + 1)) (𝓝[≠] 1)
      (𝓝 (5 / 3 : ℝ)) := by
    have hc : ContinuousAt (fun r : ℝ =>
        (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) / (r ^ 2 + r + 1)) 1 := by
      fun_prop (disch := norm_num)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  refine ⟨ht2.congr' ?_, ht5.congr' ?_, ?_⟩
  · filter_upwards [hpos, hne] with r hr hn
    exact (dilation_quotient_two_eq hr hn).symm
  · filter_upwards [hpos, hne] with r hr hn
    exact (dilation_quotient_five_eq hr hn).symm
  · intro r hr
    by_cases hn : r = 1
    · simp [hn]
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hd : 0 < |r ^ 3 - 1| := abs_pos.mpr (by
      intro hz
      have : r = 1 := by nlinarith [sq_nonneg (r - 1)]
      exact hn this)
    exact ⟨(div_le_iff₀ hd).mpr (abs_dilation_two_sub_one_le hr0 hr.2),
      (div_le_iff₀ hd).mpr (abs_dilation_five_sub_one_le hr0 hr.2)⟩

/-- A quantitative energy comparison using the two dilation exponents. -/
lemma dilation_energy_le {r a b : ℝ} (hr : 0 ≤ r) (hR : r ≤ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    r ^ 2 * a + r ^ 5 * b ≤ a + b + 31 * (a + b) * |r ^ 3 - 1| := by
  have h2 : r ^ 2 - 1 ≤ 31 * |r ^ 3 - 1| := by
    calc
      _ ≤ |r ^ 2 - 1| := le_abs_self _
      _ ≤ 3 * |r ^ 3 - 1| := abs_dilation_two_sub_one_le hr hR
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  have h5 : r ^ 5 - 1 ≤ 31 * |r ^ 3 - 1| :=
    (le_abs_self _).trans (abs_dilation_five_sub_one_le hr hR)
  have h2a := mul_le_mul_of_nonneg_right h2 ha
  have h5b := mul_le_mul_of_nonneg_right h5 hb
  nlinarith only [h2a, h5b]

end LiquidDrop
