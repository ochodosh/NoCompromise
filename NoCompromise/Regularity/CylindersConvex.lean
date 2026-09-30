module

public import NoCompromise.Regularity.Cylinders
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-! # Convexity of intrinsic cylinders -/

noncomputable section
open Set Metric
namespace LiquidDrop

lemma convex_cylinder (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) :
    Convex ℝ (cylinder x r ν) := by
  have hp := (convex_ball (0 : AmbientSpace) r).linear_preimage
    (cylinderProjection ν).toLinearMap
  have hn := (convex_ball (0 : ℝ) r).linear_preimage (innerSL ℝ ν).toLinearMap
  have ht := (hp.inter hn).translate_preimage_right (-x)
  have he : cylinder x r ν = (fun y => -x + y) ⁻¹'
      ((cylinderProjection ν) ⁻¹' ball 0 r ∩ (innerSL ℝ ν) ⁻¹' ball 0 r) := by
    ext y
    simp [cylinder, sub_eq_add_neg, add_comm]
  rw [he]
  exact ht


end LiquidDrop
