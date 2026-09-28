import NoCompromise.Regularity.GeometricRecurrence

/-! # The fixed scale chosen after the universal tilt constant -/

noncomputable section
namespace LiquidDrop

def excessDecayScale (C : ℝ) : ℝ := min (1 / 64) (1 / (4 * C))

lemma excessDecayScale_bounds {C : ℝ} (hC : 1 ≤ C) :
    0 < excessDecayScale C ∧ excessDecayScale C < 1 / 32 ∧
      C * (excessDecayScale C) ^ 2 ≤ excessDecayScale C / 4 ∧
      (C + 1) * excessDecayScale C ≤ 1 / 2 := by
  have hC0 : 0 < C := by linarith
  have ht : 0 < excessDecayScale C := lt_min (by norm_num) (by positivity)
  have hsmall : excessDecayScale C ≤ 1 / 64 := min_le_left _ _
  have hsmall' : excessDecayScale C ≤ 1 / (4 * C) := min_le_right _ _
  have hc : C * excessDecayScale C ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hsmall'
    linarith
  have hc' := mul_le_mul_of_nonneg_right hc ht.le
  have ht' : excessDecayScale C ≤ C * excessDecayScale C := by
    nlinarith
  exact ⟨ht, by linarith, by nlinarith, by linarith⟩

lemma excessDecayScale_preserves_smallness {C e ω r ε : ℝ} (hC : 1 ≤ C)
    (he : 0 ≤ e) (hω : 0 ≤ ω) (hr : 0 ≤ r) (hsmall : e + ω * r ≤ ε) :
    (excessDecayScale C / 2 * e + C * excessDecayScale C * ω * r) +
      ω * (excessDecayScale C * r) ≤ ε / 2 := by
  obtain ⟨ht, ht32, _, hb⟩ := excessDecayScale_bounds hC
  have h1 := mul_le_mul_of_nonneg_right (show excessDecayScale C / 2 ≤ 1 / 2 by
    linarith) he
  have h2 := mul_le_mul_of_nonneg_right hb (mul_nonneg hω hr)
  nlinarith

end LiquidDrop
