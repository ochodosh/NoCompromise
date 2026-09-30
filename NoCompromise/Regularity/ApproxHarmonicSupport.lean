module

public import NoCompromise.Regularity.FluxDefectTests

@[expose] public section

/-! # Compact support of the vertical graph variation -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma tsupport_vertical_tensor_subset
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) (ψ : ℝ → ℝ) :
    tsupport (fun x : AmbientSpace => ζ (graphProjectionN 2 x) * ψ (x 2)) ⊆
      graphProjectionN 2 ⁻¹' tsupport ζ ∩
        (fun x : AmbientSpace => x 2) ⁻¹' tsupport ψ := by
  apply closure_minimal
  · intro x hx
    refine ⟨subset_tsupport ζ ?_, subset_tsupport ψ ?_⟩
    · intro hz
      exact hx (by simp only [hz, zero_mul])
    · intro hp
      exact hx (by simp only [hp, mul_zero])
  · exact ((isClosed_tsupport ζ).preimage (graphProjectionN 2).continuous).inter
      ((isClosed_tsupport ψ).preimage (EuclideanSpace.proj (2 : Fin 3)).continuous)

lemma tsupport_vertical_field_subset_cylinder
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ} {r : ℝ}
    (hζ : tsupport ζ ⊆ ball 0 r) (hψ : tsupport ψ ⊆ Ioo (-r) r) :
    tsupport (fun x : AmbientSpace => (ζ (graphProjectionN 2 x) * ψ (x 2)) •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ⊆ standardCylinder r := by
  intro x hx
  have hs := tsupport_vertical_tensor_subset ζ ψ
    (tsupport_smul_subset_left _ _ hx)
  exact ⟨mem_ball_zero_iff.mp (hζ hs.1), abs_lt.mpr (hψ hs.2)⟩

lemma standardCylinder_half_subset_unit_ball :
    standardCylinder (1 / 2) ⊆ ball (0 : AmbientSpace) 1 := by
  rw [standardCylinder_eq_cylinder]
  apply (cylinder_subset_ball 0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (ν := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (by simp)).trans
  apply ball_subset_ball
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

lemma vertical_field_compact_support
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hζ : HasCompactSupport ζ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x : AmbientSpace => (ζ (graphProjectionN 2 x) * ψ (x 2)) •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :=
  (hasCompactSupport_vertical_tensor hζ hψ).smul_right

end LiquidDrop
