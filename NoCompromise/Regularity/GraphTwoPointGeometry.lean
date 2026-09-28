import NoCompromise.Regularity.GraphProjectedLocal

/-! # The geometric contradiction in the good-base Lipschitz estimate -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma mem_vertical_cylinder_iff (p q : AmbientSpace) (r : ℝ) :
    q ∈ cylinder p r (EuclideanSpace.single 2 1) ↔
      dist (graphProjectionN 2 q) (graphProjectionN 2 p) < r ∧ |q 2 - p 2| < r := by
  have he : q ∈ cylinder p r (EuclideanSpace.single 2 1) ↔ q - p ∈ standardCylinder r := by
    rw [standardCylinder_eq_cylinder]
    simp only [cylinder, mem_ofPred_eq, sub_zero]
  rw [he]
  simp only [standardCylinder, mem_ofPred_eq, map_sub, PiLp.sub_apply, dist_eq_norm]

lemma graph_two_point_radius_positive {γ d h : ℝ} (hγ : 0 < γ) (hd : 0 ≤ d)
    (hh : γ * d < h) : 0 < 2 * max d h := by
  have hp : 0 < h := (mul_nonneg hγ.le hd).trans_lt hh
  exact mul_pos (by norm_num) (hp.trans_le (le_max_right _ _))

lemma graph_two_point_mem_cylinder (p q : AmbientSpace) {γ : ℝ} (hγ : 0 < γ)
    (hh : γ * dist (graphProjectionN 2 q) (graphProjectionN 2 p) < |q 2 - p 2|) :
    q ∈ cylinder p
      (3 * (2 * max (dist (graphProjectionN 2 q) (graphProjectionN 2 p)) |q 2 - p 2|) / 4)
      (EuclideanSpace.single 2 1) := by
  rw [mem_vertical_cylinder_iff]
  have hm := graph_two_point_radius_positive hγ dist_nonneg hh
  have hd := le_max_left (dist (graphProjectionN 2 q) (graphProjectionN 2 p)) |q 2 - p 2|
  have hh' := le_max_right (dist (graphProjectionN 2 q) (graphProjectionN 2 p)) |q 2 - p 2|
  constructor <;> linarith

lemma graph_two_point_height_contradiction {γ d h : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hd : 0 ≤ d) (hh : γ * d < h)
    (hb : h < (γ / 4) * (2 * max d h)) : False := by
  have hp : 0 < h := (mul_nonneg hγ.le hd).trans_lt hh
  by_cases hdh : d ≤ h
  · rw [max_eq_right hdh] at hb
    have ht := mul_le_mul_of_nonneg_right hγ1 hp.le
    nlinarith
  · rw [max_eq_left (le_of_not_ge hdh)] at hb
    nlinarith [mul_nonneg hγ.le hd]

end LiquidDrop
