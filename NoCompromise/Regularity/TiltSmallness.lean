import NoCompromise.Regularity.TiltSlab

/-! # Explicit smallness conditions for the tilted slab -/

noncomputable section
open Set MeasureTheory Metric
namespace LiquidDrop

lemma tilt_affine_smallness {θ τ a Ch m d : ℝ}
    (v : EuclideanSpace ℝ (Fin 2)) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hτ : τ ≤ θ / 1024) (hac : a * Ch ≤ θ / 1024)
    (hm : |m| ≤ τ) (hd : |d| + ‖v‖ ≤ Ch) :
    |m + a * d| ≤ θ / 512 ∧ ‖a • v‖ ≤ θ / 1024 ∧
      ‖graphUnitNormal (a • v) - EuclideanSpace.single 2 1‖ ≤ 1 / 8 ∧
      |m + a * d| + (1 / 4 : ℝ) * (2 * θ) < 2 * θ ∧
      τ + |m + a * d| + ‖a • v‖ * (3 * θ) < (1 / 4 : ℝ) * (2 * θ) := by
  have hd' : |d| ≤ Ch := by linarith [norm_nonneg v]
  have hv' : ‖v‖ ≤ Ch := by linarith [abs_nonneg d]
  have hm' : |m + a * d| ≤ θ / 512 := by
    have hb := abs_add_le m (a * d)
    rw [abs_mul, abs_of_nonneg ha] at hb
    have hb' := mul_le_mul_of_nonneg_left hd' ha
    linarith
  have hv : ‖a • v‖ ≤ θ / 1024 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hv' ha).trans hac
  refine ⟨hm', hv, ?_, ?_, ?_⟩
  · exact (graphUnitNormal_sub_vertical_le (a • v)).trans (by linarith)
  · linarith
  · have hb := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ 3 * θ)
    nlinarith

lemma tilt_slab_width {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < θ ^ 3 / 1024 ∧ θ ^ 3 / 1024 ≤ θ / 1024 ∧
      (θ ^ 3 / 1024) ^ 2 ≤ θ ^ 6 ∧ θ ^ 3 / 1024 < θ ∧
      θ ^ 3 / 1024 < 1 / 4 := by
  have hc : θ ^ 3 ≤ θ := by
    have hs : θ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs hθ.le]
  refine ⟨by positivity, by linarith, ?_, by linarith, by linarith⟩
  have hid : (θ ^ 3) ^ 2 = θ ^ 6 := by ring
  nlinarith [sq_nonneg (θ ^ 3)]

lemma tilt_sqrt_smallness {s θ Ch : ℝ} (hθ : 0 < θ) (hCh : 0 < Ch)
    (hsmall : s ≤ (θ / (1024 * Ch)) ^ 2) :
    Real.sqrt s * Ch ≤ θ / 1024 := by
  have hb : Real.sqrt s ≤ θ / (1024 * Ch) := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsmall⟩
  have hm := mul_le_mul_of_nonneg_right hb hCh.le
  have he : θ / (1024 * Ch) * Ch = θ / 1024 := by field_simp
  exact he ▸ hm

end LiquidDrop
