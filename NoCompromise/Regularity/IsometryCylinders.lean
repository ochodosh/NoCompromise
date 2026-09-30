module

public import NoCompromise.Regularity.Cylinders

@[expose] public section

/-! # Exact covariance of intrinsic cylinders under orthogonal maps -/

noncomputable section
open Set Metric
namespace LiquidDrop

lemma cylinderProjection_linearIsometry
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (ν y : AmbientSpace) :
    cylinderProjection (Q ν) (Q y) = Q (cylinderProjection ν y) := by
  simp only [cylinderProjection_apply, map_sub, map_smul, Q.inner_map_map]

lemma mem_cylinder_linearIsometry
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x y ν : AmbientSpace) (r : ℝ) :
    Q y ∈ cylinder (Q x) r (Q ν) ↔ y ∈ cylinder x r ν := by
  change (‖cylinderProjection (Q ν) (Q y - Q x)‖ < r ∧
    |inner ℝ (Q ν) (Q y - Q x)| < r) ↔ _
  rw [← Q.map_sub, cylinderProjection_linearIsometry, Q.norm_map, Q.inner_map_map]
  rfl

lemma image_cylinder_linearIsometry
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x ν : AmbientSpace) (r : ℝ) :
    Q '' cylinder x r ν = cylinder (Q x) r (Q ν) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_cylinder_linearIsometry Q x z ν r).mpr hz
  · intro hy
    refine ⟨Q.symm y, ?_, Q.apply_symm_apply y⟩
    apply (mem_cylinder_linearIsometry Q x (Q.symm y) ν r).mp
    simpa only [Q.apply_symm_apply] using hy

end LiquidDrop
