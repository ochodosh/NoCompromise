module

public import NoCompromise.Regularity.GraphAffineHeightComparison
public import NoCompromise.Regularity.GraphAffineHeightErrors

@[expose] public section

/-! # Radius-independent affine-height estimate for the tilt argument -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Full boundary height above the new affine plane, with a constant independent
of `θ`. All graph loss, clamping, harmonic approximation, and affine remainder
hypotheses concern the actual functions and measures. -/
theorem graphAffineHeight_tilt_moment
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {f h : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1)
    (hh : HasH1GradientOn h (gradient h) (ball 0 (1 / 4)))
    (hc : ContinuousOn h (ball 0 (1 / 4)))
    {a τ θ A H L : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hθ : 0 < θ) (hθ32 : θ < 1 / 32)
    (ha2 : a ^ 2 ≤ θ ^ 6) (hτ2 : τ ^ 2 ≤ θ ^ 6)
    (hfheight : ∀ x, |f x| ≤ τ)
    (hheight : ∀ z ∈ reducedBoundary E hE hmE ∩ standardCylinder (1 / 2), |z 2| ≤ τ)
    (hh0 : |h 0| ≤ H) (hhgrad : ‖gradient h 0‖ ≤ H)
    (hloss : (hausdorffMeasure2 3).real
      ((reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) \
        graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ≤ L * a ^ 2)
    (hnorm : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
      |harmonicBlowupFunction f a x - h x| ^ 2) ≤ θ ^ 6)
    (haffine : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (4 * θ),
      ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2) ≤ A * θ ^ 6) :
    (∫ z in cylinder 0 (2 * θ) (graphUnitNormal (a • gradient h 0)),
      (inner ℝ (graphUnitNormal (a • gradient h 0)) z -
        ((⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y) + a * h 0) /
          Real.sqrt (1 + ‖a • gradient h 0‖ ^ 2)) ^ 2
        ∂canonicalPerimeterMeasure E hE hmE) ≤
      (4 * (1 + A) + 8 * L * (1 + H ^ 2)) * a ^ 2 * θ ^ 6 := by
  let p := a • gradient h 0
  let m := ⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y
  let b := m + a * h 0
  let U := cylinder 0 (2 * θ) (graphUnitNormal p)
  let M := 2 * τ + 2 * a * H
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hUC : U ⊆ standardCylinder (1 / 2) := by
    intro z hz
    have ht := rotated_cylinder_two_subset_standard_three (norm_graphUnitNormal p) hθ hz
    exact ⟨ht.1.trans_le (by linarith), ht.2.trans_le (by linarith)⟩
  have hproj : ∀ z ∈ U, graphProjectionN 2 z ∈ ball 0 (4 * θ) := by
    intro z hz
    have ht := rotated_cylinder_two_subset_standard_three (norm_graphUnitNormal p) hθ hz
    exact mem_ball_zero_iff.mpr (ht.1.trans (by linarith))
  have hm : |m| ≤ τ := graphAffineHeight_average_le hτ hfheight
  have hb : |b| ≤ τ + a * H := by
    have ht := abs_add_le m (a * h 0)
    rw [abs_mul, abs_of_pos ha] at ht
    have hh' := mul_le_mul_of_nonneg_left hh0 ha.le
    dsimp only [b]
    linarith
  have hp : ‖p‖ ≤ a * H := by
    dsimp only [p]
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact mul_le_mul_of_nonneg_left hhgrad ha.le
  have hbound : ∀ z ∈ reducedBoundary E hE hmE ∩ U,
      |z 2 - b - inner ℝ p (graphProjectionN 2 z)| ≤ M := by
    intro z hz
    have hh' := hheight z ⟨hz.1, hUC hz.2⟩
    have hbase : ‖graphProjectionN 2 z‖ ≤ 1 := (hUC hz.2).1.le.trans (by norm_num)
    have hi := (abs_real_inner_le_norm p (graphProjectionN 2 z)).trans
      ((mul_le_mul_of_nonneg_left hbase (norm_nonneg p)).trans (by simpa using hp))
    have ht := abs_sub_le (z 2 - b) 0 (inner ℝ p (graphProjectionN 2 z))
    have ht' := abs_sub_le (z 2) 0 b
    simp only [sub_zero, zero_sub, abs_neg] at ht ht'
    dsimp only [M]
    linarith
  have hcomp := graphAffineHeight_boundary_moment_le E hE hmE hf hK p b
    (isOpen_cylinder _ _ _).measurableSet hUC hproj hM hbound
  have hbase := graphAffineHeight_base_error_le hf hh hc ha hθ32 hnorm haffine
  have hMsq : M ^ 2 ≤ 8 * (1 + H ^ 2) * θ ^ 6 := by
    have hm := mul_le_mul_of_nonneg_right ha2 (sq_nonneg H)
    have hs := sq_nonneg (τ - a * H)
    dsimp only [M]
    nlinarith
  have hbad1 := mul_le_mul_of_nonneg_left hloss (sq_nonneg M)
  have hbad2 := mul_le_mul_of_nonneg_right hMsq (mul_nonneg hL (sq_nonneg a))
  have hgood := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 2)
  dsimp only [p, b, m, U] at hcomp
  nlinarith

end LiquidDrop
