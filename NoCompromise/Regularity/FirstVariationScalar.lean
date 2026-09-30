module

public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! # Two-sided variation of an almost-minimum -/

open Filter Set
open scoped Topology

namespace LiquidDrop

/-- The two signs of a perturbation bound its first variation by the limiting
absolute perturbation cost. No differentiability of the cost is required. -/
lemma abs_derivative_le_of_variation_cost {f g : ℝ → ℝ} {L I ω : ℝ}
    (hf : HasDerivAt f L 0)
    (hg : Tendsto (fun t => g t / |t|) (𝓝[≠] 0) (𝓝 I))
    (hmin : ∀ᶠ t in 𝓝 0, f 0 ≤ f t + ω * g t) : |L| ≤ ω * I := by
  have hfr : Tendsto (fun t => (f t - f 0) / t) (𝓝[>] 0) (𝓝 L) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hf.tendsto_slope_zero_right
  have hfl : Tendsto (fun t => (f t - f 0) / t) (𝓝[<] 0) (𝓝 L) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hf.tendsto_slope_zero_left
  have hl : L ≤ ω * I := by
    apply le_of_tendsto_of_tendsto hfl
      ((hg.mono_left (nhdsLT_le_nhdsNE 0)).const_mul ω)
    filter_upwards [hmin.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hmt ht
    have ht' : t < 0 := ht
    have h := div_le_div_of_nonneg_right (show f 0 - f t ≤ ω * g t by linarith)
      (neg_nonneg.mpr ht'.le)
    rw [abs_of_neg ht']
    convert h using 1 <;> ring
  have hr : -L ≤ ω * I := by
    apply le_of_tendsto_of_tendsto hfr.neg
      ((hg.mono_left (nhdsGT_le_nhdsNE 0)).const_mul ω)
    filter_upwards [hmin.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hmt ht
    have ht' : 0 < t := ht
    have h := div_le_div_of_nonneg_right (show f 0 - f t ≤ ω * g t by linarith) ht'.le
    rw [abs_of_pos ht']
    convert h using 1 <;> ring
  exact abs_le.mpr ⟨by linarith, hl⟩

end LiquidDrop
