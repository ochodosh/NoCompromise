module

public import NoCompromise.Elliptic.BoundaryHolderOddField

@[expose] public section

/-! Centered oscillations of the actual reflected field. Normal constants are
preserved by odd scalar reflection, so boundary normal excess controls full-ball
oscillation without introducing an artificial boundary jump. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_variance_congr_ae {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {F G : X → E}
    (he : F =ᵐ[μ] G) :
    (∫ x, ‖F x - ⨍ y, F y ∂μ‖ ^ 2 ∂μ) = ∫ x, ‖G x - ⨍ y, G y ∂μ‖ ^ 2 ∂μ := by
  have hm : (⨍ y, F y ∂μ) = ⨍ y, G y ∂μ := by
    rw [average_eq, average_eq, integral_congr_ae he]
  rw [hm]
  exact integral_congr_ae (he.mono fun _ hx => by dsimp only at hx ⊢; rw [hx])

lemma boundaryOddField_average_reflect (F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    (⨍ x in ball (coordinateReflection (Fin.last 2) c) r, boundaryOddField F x) =
      -coordinateReflection (Fin.last 2) (⨍ x in ball c r, boundaryOddField F x) := by
  rw [← boundary_reflection_average_ball]
  simp_rw [boundaryOddField_reflect]
  have hi : (∫ x in ball c r, coordinateReflection (Fin.last 2) (boundaryOddField F x)) =
      coordinateReflection (Fin.last 2) (∫ x in ball c r, boundaryOddField F x) :=
    (coordinateReflection (Fin.last 2)).toLinearIsometry.integral_comp_comm (boundaryOddField F)
  rw [average_eq, integral_neg, hi]
  simp only [average_eq, map_smul, smul_neg]

lemma boundaryOddField_variance_reflect (F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    (∫ x in ball (coordinateReflection (Fin.last 2) c) r,
      ‖boundaryOddField F x - ⨍ y in ball (coordinateReflection (Fin.last 2) c) r,
        boundaryOddField F y‖ ^ 2) =
    ∫ x in ball c r, ‖boundaryOddField F x - ⨍ y in ball c r, boundaryOddField F y‖ ^ 2 := by
  rw [← boundary_reflection_integral_ball
    (fun x => ‖boundaryOddField F x - ⨍ y in ball (coordinateReflection (Fin.last 2) c) r,
      boundaryOddField F y‖ ^ 2) c r]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [boundaryOddField_reflect, boundaryOddField_average_reflect, neg_sub_neg]
  rw [← map_sub, (coordinateReflection (Fin.last 2)).norm_map, norm_sub_rev]

lemma boundaryOddField_variance_upper {F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} {c : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hsub : ball c r ⊆ boundaryHalfBall 1) :
    (∫ x in ball c r, ‖boundaryOddField F x - ⨍ y in ball c r, boundaryOddField F y‖ ^ 2) =
    ∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2 := by
  apply boundary_variance_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact boundaryOddField_eq_upper F (hsub hx)

lemma boundaryOddField_variance_flat_ball {F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1)))
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hsub : ball (graphAppendN z 0) r ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∫ x in ball (graphAppendN z 0) r,
      ‖boundaryOddField F x - ⨍ y in ball (graphAppendN z 0) r, boundaryOddField F y‖ ^ 2) ≤
      4 * boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
        (volume.restrict (ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)})) := by
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  let B := ball (graphAppendN z 0) r
  let V := B ∩ {y : EuclideanSpace ℝ (Fin 3) | 0 < y (Fin.last 2)}
  let b := boundaryNormalMean n F (volume.restrict V)
  let : IsFiniteMeasure (volume.restrict B) :=
    ⟨by simpa [B] using (isBounded_ball (x := graphAppendN z 0) (r := r)).measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top 1⟩
  have hconst := ae_restrict_of_ae_restrict_of_subset hsub (boundaryOddField_normal_ae b)
  have he : (fun x => boundaryOddField F x - b • n) =ᵐ[volume.restrict B]
      boundaryOddField (fun x => F x - b • n) := by
    filter_upwards [hconst] with x hx
    rw [boundaryOddField_sub]
    exact congrArg (fun v => boundaryOddField F x - v) hx.symm
  calc
    _ ≤ ∫ x in B, ‖boundaryOddField F x - b • n‖ ^ 2 :=
      frozen_integral_norm_sub_average_le ((boundaryOddField_memLp hF).restrict B) (b • n)
    _ = ∫ x in B, ‖boundaryOddField (fun x => F x - b • n) x‖ ^ 2 :=
      integral_congr_ae (he.mono fun _ hx => by dsimp only at hx ⊢; rw [hx])
    _ ≤ 4 * ∫ x in V, ‖F x - b • n‖ ^ 2 :=
      boundaryOddField_energy_flat_ball (hF.sub (memLp_const _)) z r hsub
    _ = _ := rfl

lemma boundaryOddField_energy_unit {F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1))) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖boundaryOddField F x‖ ^ 2) ≤
      4 * ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
  have hz : graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) 0 = 0 := by
    simp only [graphAppendN, map_zero, zero_smul, add_zero]
  simpa only [hz, boundaryHalfBall] using boundaryOddField_energy_flat_ball hF 0 1
    (by simpa only [hz] using
      (Subset.rfl : ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ ball 0 1))

end LiquidDrop
