import NoCompromise.Regularity.ApproxHarmonicTest
import NoCompromise.Regularity.ApproxHarmonicSupport
import NoCompromise.Regularity.SlabGeometry

/-! # A fixed admissible compact vertical variation for approximate harmonicity -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A fixed smooth cutoff, flat on the quarter-height slab. -/
def approxHarmonicCutoff : ContDiffBump (0 : ℝ) :=
  ⟨1 / 3, 5 / 12, by norm_num, by norm_num⟩

lemma approxHarmonicCutoff_support :
    tsupport approxHarmonicCutoff ⊆ Ioo (-(1 / 2)) (1 / 2) := by
  intro t ht
  rw [approxHarmonicCutoff.tsupport_eq] at ht
  have hh : |t| ≤ 5 / 12 := by simpa [approxHarmonicCutoff, Real.dist_eq] using ht
  exact abs_lt.mp (hh.trans_lt (by norm_num))

lemma approxHarmonicCutoff_flat {t : ℝ} (ht : |t| ≤ 1 / 4) :
    approxHarmonicCutoff t = 1 ∧ deriv approxHarmonicCutoff t = 0 := by
  have hm : t ∈ ball 0 approxHarmonicCutoff.rIn := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ht.trans_lt (by
      change (1 / 4 : ℝ) < 1 / 3
      norm_num)
  refine ⟨approxHarmonicCutoff.one_of_mem_closedBall (ball_subset_closedBall hm), ?_⟩
  have he := (approxHarmonicCutoff.eventuallyEq_one_of_mem_ball hm).deriv_eq
  simpa only [Pi.one_def, deriv_const] using he

/-- The actual vertical field used in the perimeter first variation. -/
def approxHarmonicField (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) (z : AmbientSpace) : AmbientSpace :=
  (ζ (graphProjectionN 2 z) * approxHarmonicCutoff (z 2)) • EuclideanSpace.single 2 1

lemma approxHarmonicField_admissible {ζ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2)) :
    ContDiff ℝ 1 (approxHarmonicField ζ) ∧ HasCompactSupport (approxHarmonicField ζ) ∧
      tsupport (approxHarmonicField ζ) ⊆ standardCylinder (1 / 2) ∧
      tsupport (approxHarmonicField ζ) ⊆ ball (0 : AmbientSpace) 1 := by
  have hs := tsupport_vertical_field_subset_cylinder hsζ approxHarmonicCutoff_support
  refine ⟨?_, vertical_field_compact_support hcζ approxHarmonicCutoff.hasCompactSupport,
    hs, hs.trans standardCylinder_half_subset_unit_ball⟩
  exact ((hζ.comp (graphProjectionN 2).contDiff).mul
    (approxHarmonicCutoff.contDiff.comp
      (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).contDiff)).smul contDiff_const

lemma approxHarmonicField_normal_flux_le
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) (z v : AmbientSpace) (hv : ‖v‖ = 1) :
    |inner ℝ (approxHarmonicField ζ z) v| ≤ |ζ (graphProjectionN 2 z)| := by
  apply (abs_real_inner_le_norm _ _).trans
  rw [hv, mul_one]
  simp only [approxHarmonicField, norm_smul, Real.norm_eq_abs, abs_mul,
    show ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 by simp, mul_one]
  rw [abs_of_nonneg approxHarmonicCutoff.nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _) approxHarmonicCutoff.le_one

lemma approxHarmonicField_tangential_bound
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (ν : AmbientSpace → AmbientSpace) (z : AmbientSpace)
    (hν : ‖ν z‖ = 1) (hz : |z 2| ≤ 1 / 4) :
    |tangentialDivergence (approxHarmonicField ζ) ν z| ≤
      ‖gradient ζ (graphProjectionN 2 z)‖ := by
  obtain ⟨hp, hdp⟩ := approxHarmonicCutoff_flat hz
  change |tangentialDivergence
    (fun x : AmbientSpace => (ζ (graphProjectionN 2 x) * approxHarmonicCutoff (x 2)) •
      EuclideanSpace.single 2 1) ν z| ≤ _
  rw [tangentialDivergence_vertical_tensor hζ
    approxHarmonicCutoff.contDiff ν z hp hdp, abs_neg, abs_mul]
  have hc : |ν z 2| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hν] using PiLp.norm_apply_le (ν z) 2
  have hb : ‖graphProjectionN 2 (ν z)‖ ≤ 1 := by
    simpa only [hν] using norm_graphProjectionN_le (ν z)
  have hi : |fderiv ℝ ζ (graphProjectionN 2 z) (graphProjectionN 2 (ν z))| ≤
      ‖gradient ζ (graphProjectionN 2 z)‖ := by
    rw [← inner_gradient_left]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hb)
  exact (mul_le_mul hc hi (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma approxHarmonicField_tangential_zero_off_cylinder
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    (ν : AmbientSpace → AmbientSpace) {z : AmbientSpace}
    (hz : z ∉ standardCylinder (1 / 2)) :
    tangentialDivergence (approxHarmonicField ζ) ν z = 0 :=
  tangentialDivergence_eq_zero_of_notMem_tsupport
    (fun ht => hz (tsupport_vertical_field_subset_cylinder hsζ approxHarmonicCutoff_support ht))

end LiquidDrop
