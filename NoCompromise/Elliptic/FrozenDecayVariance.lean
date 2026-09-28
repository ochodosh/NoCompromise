import NoCompromise.Elliptic.CampanatoComparisonTests
import Mathlib.MeasureTheory.Integral.Average

/-! The mean minimizes squared Euclidean oscillation on a finite measure
space. This gives the centered-energy comparison needed at the larger scales. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_integral_norm_sub_average_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) (c : E) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x - c‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  have hg : MemLp (fun x => f x - m) 2 μ := hf.sub (memLp_const m)
  have hgi : Integrable (fun x => f x - m) μ := hg.integrable (by norm_num)
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Integrable (fun x => inner ℝ (m - c) (f x - m)) μ := hgi.const_inner _
  have he (x) : ‖f x - c‖ ^ 2 = ‖f x - m‖ ^ 2 +
      2 * inner ℝ (m - c) (f x - m) + ‖m - c‖ ^ 2 := by
    have hh := norm_add_sq_real (f x - m) (m - c)
    rw [sub_add_sub_cancel] at hh
    rw [real_inner_comm] at hh
    linarith
  have hzero : (∫ x, inner ℝ (m - c) (f x - m) ∂μ) = 0 := by
    rw [integral_inner hgi, integral_sub_average, inner_zero_right]
  simp_rw [he]
  have hsum : Integrable (fun x => ‖f x - m‖ ^ 2 +
      2 * inner ℝ (m - c) (f x - m)) μ := hg2.add (hi.const_mul 2)
  rw [integral_add hsum (integrable_const _),
    integral_add hg2 (hi.const_mul 2), integral_const_mul, hzero, mul_zero, add_zero]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

end LiquidDrop
