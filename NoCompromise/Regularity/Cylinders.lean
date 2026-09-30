module

public import NoCompromise.Conventions
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-! # Intrinsic open cylinders about a unit axis -/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- Projection onto the plane perpendicular to a unit vector. -/
def cylinderProjection (ν : AmbientSpace) : AmbientSpace →L[ℝ] AmbientSpace :=
  ContinuousLinearMap.id ℝ AmbientSpace - (innerSL ℝ ν).smulRight ν

/-- The rotated cylinder of radius and half-height r, centered at x with axis ν. -/
def cylinder (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) : Set AmbientSpace :=
  {y | ‖cylinderProjection ν (y - x)‖ < r ∧ |inner ℝ ν (y - x)| < r}

lemma cylinderProjection_apply (ν y : AmbientSpace) :
    cylinderProjection ν y = y - (inner ℝ ν y) • ν := rfl

lemma norm_cylinderProjection_sq {ν : AmbientSpace} (hν : ‖ν‖ = 1) (y : AmbientSpace) :
    ‖cylinderProjection ν y‖ ^ 2 = ‖y‖ ^ 2 - (inner ℝ ν y) ^ 2 := by
  rw [cylinderProjection_apply, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, hν, mul_one, sq_abs, real_inner_comm y ν]
  ring

lemma norm_cylinderProjection_le {ν : AmbientSpace} (hν : ‖ν‖ = 1) (y : AmbientSpace) :
    ‖cylinderProjection ν y‖ ≤ ‖y‖ := by
  have he := norm_cylinderProjection_sq hν y
  nlinarith [norm_nonneg y, norm_nonneg (cylinderProjection ν y), sq_nonneg (inner ℝ ν y)]

lemma isOpen_cylinder (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) :
    IsOpen (cylinder x r ν) := by
  exact (isOpen_lt ((cylinderProjection ν).continuous.comp
    (continuous_id.sub continuous_const)).norm continuous_const).inter
      (isOpen_lt ((innerSL ℝ ν).continuous.comp
        (continuous_id.sub continuous_const)).abs continuous_const)

lemma ball_subset_cylinder (x : AmbientSpace) (r : ℝ) {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ball x r ⊆ cylinder x r ν := by
  intro y hy
  have hy' : ‖y - x‖ < r := hy
  refine ⟨(norm_cylinderProjection_le hν _).trans_lt hy', ?_⟩
  have hi := norm_inner_le_norm (𝕜 := ℝ) ν (y - x)
  simpa only [Real.norm_eq_abs, hν, one_mul] using hi.trans_lt (by simpa [hν] using hy')

lemma cylinder_subset_ball (x : AmbientSpace) {r : ℝ} (hr : 0 ≤ r)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    cylinder x r ν ⊆ ball x (Real.sqrt 2 * r) := by
  intro y hy
  have hp := norm_cylinderProjection_sq hν (y - x)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ht : ‖cylinderProjection ν (y - x)‖ ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hr).mpr hy.1
  have hn : (inner ℝ ν (y - x)) ^ 2 < r ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hr).mpr hy.2
  change ‖y - x‖ < Real.sqrt 2 * r
  apply (sq_lt_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hr)).mp
  rw [mul_pow, hsq]
  nlinarith

lemma isBounded_cylinder (x : AmbientSpace) (r : ℝ) {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    Bornology.IsBounded (cylinder x r ν) := by
  by_cases hr : 0 ≤ r
  · exact isBounded_ball.subset (cylinder_subset_ball x hr hν)
  · have he : cylinder x r ν = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact (not_le.mp hr).not_ge ((norm_nonneg _).trans hy.1.le)
    rw [he]
    exact Bornology.isBounded_empty

lemma cylinder_mono {x ν : AmbientSpace} {r s : ℝ} (hrs : r ≤ s) :
    cylinder x r ν ⊆ cylinder x s ν := fun _ hy => ⟨hy.1.trans_le hrs, hy.2.trans_le hrs⟩

lemma cylinder_subset_add_radius {x z ν : AmbientSpace} {r s : ℝ}
    (hz : z ∈ cylinder x r ν) : cylinder z s ν ⊆ cylinder x (r + s) ν := by
  intro y hy
  have he : y - x = (y - z) + (z - x) := by abel
  constructor
  · rw [he, map_add]
    exact (norm_add_le _ _).trans_lt (by linarith [hy.1, hz.1])
  · change |inner ℝ ν (y - x)| < r + s
    rw [he, inner_add_right]
    exact (abs_add_le _ _).trans_lt (by linarith [hy.2, hz.2])

lemma cylinder_eighth_subset {x z ν : AmbientSpace} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ cylinder x (r / 8) ν) : cylinder z (r / 8) ν ⊆ cylinder x r ν :=
  (cylinder_subset_add_radius hz).trans (cylinder_mono (by linarith))

end LiquidDrop
