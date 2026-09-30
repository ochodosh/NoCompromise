module

public import NoCompromise.Elliptic.BoundaryHolderGeometry

@[expose] public section

/-! The explicitly reflected gradient field used for boundary Campanato
embedding. Reflection preserves its actual Lebesgue integrals; no continuity
or differentiability of the original representative is presumed. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The odd scalar reflection has even normal and odd tangential gradient.
The half-ball cutoff makes this field globally square integrable. -/
def boundaryOddField (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (boundaryHalfBall 1).indicator F x - coordinateReflection (Fin.last 2)
    ((boundaryHalfBall 1).indicator F (coordinateReflection (Fin.last 2) x))

lemma boundary_reflection_last (x : EuclideanSpace ℝ (Fin 3)) :
    coordinateReflection (Fin.last 2) x (Fin.last 2) = -x (Fin.last 2) := by
  simp only [coordinateReflection_apply, ite_true]

lemma boundary_reflection_twice (x : EuclideanSpace ℝ (Fin 3)) :
    coordinateReflection (Fin.last 2) (coordinateReflection (Fin.last 2) x) = x :=
  coordinateReflection_involutive _ x

lemma boundary_reflection_flat (z : EuclideanSpace ℝ (Fin 2)) :
    coordinateReflection (Fin.last 2) (graphAppendN z 0) = graphAppendN z 0 := by
  ext i
  by_cases hi : i = Fin.last 2
  · subst i
    simp only [boundary_reflection_last, graphAppendN_last, neg_zero]
  · simp only [coordinateReflection_apply, ite_eq_right hi]

lemma boundary_reflection_normal (b : ℝ) :
    coordinateReflection (Fin.last 2) (b • EuclideanSpace.single (Fin.last 2) 1) =
      -(b • EuclideanSpace.single (Fin.last 2) 1) := by
  ext i
  fin_cases i <;> norm_num [coordinateReflection_apply, PiLp.single_apply, Fin.last]

lemma boundary_reflection_integral_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin 3) → E) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    (∫ x in ball c r, f (coordinateReflection (Fin.last 2) x)) =
      ∫ x in ball (coordinateReflection (Fin.last 2) c) r, f x := by
  let R := coordinateReflection (Fin.last 2)
  have he : R ⁻¹' ball (R c) r = ball c r := by
    ext x
    simp only [mem_preimage, mem_ball, R.dist_map]
  have hh := (R.measurePreserving.restrict_preimage
    (measurableSet_ball (x := R c) (ε := r))).integral_comp
    R.toHomeomorph.measurableEmbedding f
  rwa [he] at hh

lemma boundary_reflection_average_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin 3) → E) (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    (⨍ x in ball c r, f (coordinateReflection (Fin.last 2) x)) =
      ⨍ x in ball (coordinateReflection (Fin.last 2) c) r, f x := by
  have hv := boundary_reflection_integral_ball (fun _ => (1 : ℝ)) c r
  simp only [integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at hv
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ,
    boundary_reflection_integral_ball, hv]

lemma boundaryOddField_reflect (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryOddField F (coordinateReflection (Fin.last 2) x) =
      -coordinateReflection (Fin.last 2) (boundaryOddField F x) := by
  simp only [boundaryOddField, map_sub, boundary_reflection_twice, neg_sub]

lemma boundaryOddField_eq_upper (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall 1) :
    boundaryOddField F x = F x := by
  have hn : coordinateReflection (Fin.last 2) x ∉ boundaryHalfBall 1 := by
    intro hh
    have hp : 0 < coordinateReflection (Fin.last 2) x (Fin.last 2) := hh.2
    rw [boundary_reflection_last] at hp
    have hxpos : 0 < x (Fin.last 2) := hx.2
    linarith
  simp only [boundaryOddField, indicator_of_mem hx, indicator_of_notMem hn, map_zero, sub_zero]

lemma boundaryOddField_memLp {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1))) :
    MemLp (boundaryOddField F) 2 volume := by
  have hz := (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hF
  let R := coordinateReflection (Fin.last 2)
  exact hz.sub (R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hz.comp_measurePreserving R.measurePreserving))

lemma boundaryOddField_sub (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    boundaryOddField (fun x => F x - G x) =
      fun x => boundaryOddField F x - boundaryOddField G x := by
  funext x
  simp only [boundaryOddField, indicator_sub, map_sub]
  abel

lemma boundaryOddField_normal_ae (b : ℝ) :
    boundaryOddField (fun _ => b • EuclideanSpace.single (Fin.last 2) 1)
      =ᵐ[volume.restrict (ball 0 1)] fun _ => b • EuclideanSpace.single (Fin.last 2) 1 := by
  filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero (Fin.last 2)),
    ae_restrict_mem measurableSet_ball] with x hx hxball
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hupper : coordinateReflection (Fin.last 2) x ∈ boundaryHalfBall 1 := by
      refine ⟨?_, ?_⟩
      · simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map]
          using hxball
      · change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2)
        rw [boundary_reflection_last]
        linarith
    have hh := boundaryOddField_reflect (fun _ => b • EuclideanSpace.single (Fin.last 2) 1)
      (coordinateReflection (Fin.last 2) x)
    rw [boundary_reflection_twice, boundaryOddField_eq_upper _ hupper,
      boundary_reflection_normal, neg_neg] at hh
    exact hh
  · exact boundaryOddField_eq_upper _ ⟨hxball, hpos⟩

/-- A rough factor four is sufficient; the actual symmetric field has an exact
factor two identity away from the null flat plane. -/
lemma boundaryOddField_energy_flat_ball {F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)} (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1)))
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hsub : ball (graphAppendN z 0) r ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∫ x in ball (graphAppendN z 0) r, ‖boundaryOddField F x‖ ^ 2) ≤
      4 * ∫ x in ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}, ‖F x‖ ^ 2 := by
  let Z := (boundaryHalfBall 1).indicator F
  let R := coordinateReflection (Fin.last 2)
  let B := ball (graphAppendN z 0) r
  have hZ : MemLp Z 2 volume :=
    (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hF
  have hRZ := R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hZ.comp_measurePreserving R.measurePreserving)
  have hi := campanato_integral_norm_sq_le_twice
    ((hZ.sub hRZ).restrict B) (hZ.restrict B)
  simp only [Pi.sub_apply, Function.comp_def, sub_sub_cancel_left, norm_neg] at hi
  change (∫ x in B, ‖Z x - R (Z (R x))‖ ^ 2) ≤
    2 * (∫ x in B, ‖R (Z (R x))‖ ^ 2) + 2 * (∫ x in B, ‖Z x‖ ^ 2) at hi
  have he : (∫ x in B, ‖R (Z (R x))‖ ^ 2) = ∫ x in B, ‖Z x‖ ^ 2 := by
    simp only [R.norm_map]
    change (∫ x in ball (graphAppendN z 0) r, ‖Z (coordinateReflection (Fin.last 2) x)‖ ^ 2) = _
    rw [boundary_reflection_integral_ball (fun x => ‖Z x‖ ^ 2), boundary_reflection_flat]
  have hbase : (∫ x in B, ‖Z x‖ ^ 2) =
      ∫ x in B ∩ {y | 0 < y (Fin.last 2)}, ‖F x‖ ^ 2 := by
    let U := {y : EuclideanSpace ℝ (Fin 3) | 0 < y (Fin.last 2)}
    calc
      _ = ∫ x in B, U.indicator (fun y => ‖F y‖ ^ 2) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        by_cases hp : x ∈ U
        · simp only [Z, indicator_of_mem (show x ∈ boundaryHalfBall 1 from ⟨hsub hx, hp⟩),
            indicator_of_mem hp]
        · have hn : x ∉ boundaryHalfBall 1 := fun hh => hp hh.2
          simp only [Z, indicator_of_notMem hn, norm_zero, zero_pow (by decide : 2 ≠ 0),
            indicator_of_notMem hp]
      _ = _ := by
        rw [integral_indicator boundary_holder_open_upper.measurableSet,
          Measure.restrict_restrict boundary_holder_open_upper.measurableSet, inter_comm U B]
  change (∫ x in B, ‖Z x - R (Z (R x))‖ ^ 2) ≤ _
  rw [he, hbase] at hi
  linarith

end LiquidDrop
