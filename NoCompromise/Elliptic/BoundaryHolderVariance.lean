module

public import NoCompromise.Elliptic.FrozenDecayVariance

@[expose] public section

/-!
# Boundary excess over normal affine functions

Projection of the mean gradient onto a fixed unit normal minimizes the squared
error among normal constants. Subtracting the corresponding normal affine
function preserves the flat zero Dirichlet condition. The ordinary variance is
bounded by this boundary excess.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The best scalar normal component of the mean field. -/
def boundaryNormalMean {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (n : E) (f : α → E) (μ : Measure α) : ℝ :=
  inner ℝ n (⨍ x, f x ∂μ)

/-- Squared oscillation relative to normal constants, preserving zero flat trace. -/
def boundaryNormalExcess {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (n : E) (f : α → E) (μ : Measure α) : ℝ :=
  ∫ x, ‖f x - boundaryNormalMean n f μ • n‖ ^ 2 ∂μ

lemma boundary_normal_excess_minimizes {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (n : E) (hn : ‖n‖ = 1) (c : ℝ) :
    boundaryNormalExcess n f μ ≤ ∫ x, ‖f x - c • n‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  let b := boundaryNormalMean n f μ
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hg : MemLp (fun x => f x - b • n) 2 μ := hf.sub (memLp_const _)
  have hgi := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Integrable (fun x => inner ℝ ((b - c) • n) (f x - b • n)) μ := hgi.const_inner _
  have hzero : (∫ x, inner ℝ ((b - c) • n) (f x - b • n) ∂μ) = 0 := by
    have he (x) : inner ℝ n (f x - b • n) = inner ℝ n (f x - m) := by
      simp only [inner_sub_right, real_inner_smul_right, hnn, mul_one]
      rfl
    simp_rw [real_inner_smul_left, he]
    have hfm : Integrable (fun x => f x - m) μ :=
      (hf.sub (memLp_const m)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [integral_const_mul, integral_inner hfm, integral_sub_average, inner_zero_right, mul_zero]
  have he (x) : ‖f x - c • n‖ ^ 2 = ‖f x - b • n‖ ^ 2 +
      2 * inner ℝ ((b - c) • n) (f x - b • n) + ‖(b - c) • n‖ ^ 2 := by
    have hh := norm_add_sq_real (f x - b • n) ((b - c) • n)
    have heq : f x - b • n + (b - c) • n = f x - c • n := by module
    rw [heq, real_inner_comm] at hh
    linarith
  simp_rw [he]
  have hsum : Integrable (fun x => ‖f x - b • n‖ ^ 2 +
      2 * inner ℝ ((b - c) • n) (f x - b • n)) μ := hg2.add (hi.const_mul 2)
  rw [integral_add hsum (integrable_const _),
    integral_add hg2 (hi.const_mul 2), integral_const_mul, hzero, mul_zero, add_zero]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

lemma boundary_normal_excess_le_energy {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (n : E) (hn : ‖n‖ = 1) :
    boundaryNormalExcess n f μ ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  simpa only [zero_smul, sub_zero] using boundary_normal_excess_minimizes hf n hn 0

lemma boundary_variance_le_normal_excess {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) (n : E) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤ boundaryNormalExcess n f μ :=
  frozen_integral_norm_sub_average_le hf (boundaryNormalMean n f μ • n)

end LiquidDrop
