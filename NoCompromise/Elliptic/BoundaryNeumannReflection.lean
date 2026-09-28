import NoCompromise.Elliptic.BoundaryHolderOddField

/-!
# Even reflection for the homogeneous conormal problem

The scalar and vector extensions are cut off outside the unit ball. Their
values on the null flat plane are zero; the coefficient and datum extensions
used for continuity are defined separately.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

def boundaryEvenFunction (w : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (boundaryHalfBall 1).indicator w x +
    (boundaryHalfBall 1).indicator w (coordinateReflection (Fin.last 2) x)

def boundaryEvenField (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (boundaryHalfBall 1).indicator F x + coordinateReflection (Fin.last 2)
    ((boundaryHalfBall 1).indicator F (coordinateReflection (Fin.last 2) x))

lemma boundary_reflection_not_upper {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ boundaryHalfBall 1) :
    coordinateReflection (Fin.last 2) x ∉ boundaryHalfBall 1 := by
  intro hh
  have hp := hh.2
  change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2) at hp
  rw [boundary_reflection_last] at hp
  exact (not_lt_of_ge hx.2.le) (neg_pos.mp hp)

lemma boundaryEvenFunction_eq_upper (w : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall 1) :
    boundaryEvenFunction w x = w x := by
  simp only [boundaryEvenFunction, indicator_of_mem hx,
    indicator_of_notMem (boundary_reflection_not_upper hx), add_zero]

lemma boundaryEvenField_eq_upper (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall 1) :
    boundaryEvenField F x = F x := by
  simp only [boundaryEvenField, indicator_of_mem hx,
    indicator_of_notMem (boundary_reflection_not_upper hx), map_zero, add_zero]

lemma boundaryEvenFunction_reflect (w : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryEvenFunction w (coordinateReflection (Fin.last 2) x) = boundaryEvenFunction w x := by
  simp only [boundaryEvenFunction, boundary_reflection_twice, add_comm]

lemma boundaryEvenField_reflect (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryEvenField F (coordinateReflection (Fin.last 2) x) =
      coordinateReflection (Fin.last 2) (boundaryEvenField F x) := by
  simp only [boundaryEvenField, map_add, boundary_reflection_twice, add_comm]

lemma boundaryEvenFunction_memLp {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : MemLp w 2 (volume.restrict (boundaryHalfBall 1))) :
    MemLp (boundaryEvenFunction w) 2 volume := by
  have hz := (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hw
  exact hz.add (hz.comp_measurePreserving (coordinateReflection (Fin.last 2)).measurePreserving)

lemma boundaryEvenField_memLp {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1))) :
    MemLp (boundaryEvenField F) 2 volume := by
  have hz := (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hF
  let R := coordinateReflection (Fin.last 2)
  exact hz.add (R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hz.comp_measurePreserving R.measurePreserving))

lemma boundaryEvenField_sub (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    boundaryEvenField (fun x => F x - G x) =
      fun x => boundaryEvenField F x - boundaryEvenField G x := by
  funext x
  simp only [boundaryEvenField, indicator_sub, map_sub]
  abel

/-- The summands have disjoint support, so the energy identity is exact. -/
lemma boundaryEvenField_norm_sq (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖boundaryEvenField F x‖ ^ 2 =
      ‖(boundaryHalfBall 1).indicator F x‖ ^ 2 +
        ‖(boundaryHalfBall 1).indicator F (coordinateReflection (Fin.last 2) x)‖ ^ 2 := by
  by_cases hx : x ∈ boundaryHalfBall 1
  · simp only [boundaryEvenField_eq_upper F hx, indicator_of_mem hx,
      indicator_of_notMem (boundary_reflection_not_upper hx), norm_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero]
  · simp only [boundaryEvenField, indicator_of_notMem hx, zero_add,
      (coordinateReflection (Fin.last 2)).norm_map, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]

lemma boundaryEvenField_energy {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1))) :
    (∫ x in ball 0 1, ‖boundaryEvenField F x‖ ^ 2) =
      2 * ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
  let Z := (boundaryHalfBall 1).indicator F
  let R := coordinateReflection (Fin.last 2)
  have hZ : MemLp Z 2 volume :=
    (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hF
  have hi : Integrable (fun x => ‖Z x‖ ^ 2) := hZ.integrable_norm_pow (by norm_num)
  have hiR : Integrable (fun x => ‖Z (R x)‖ ^ 2) :=
    (hZ.comp_measurePreserving R.measurePreserving).integrable_norm_pow (by norm_num)
  have hreflect : (∫ x in ball 0 1, ‖Z (R x)‖ ^ 2) = ∫ x in ball 0 1, ‖Z x‖ ^ 2 := by
    simpa only [map_zero] using
      boundary_reflection_integral_ball (fun x => ‖Z x‖ ^ 2) 0 1
  simp_rw [boundaryEvenField_norm_sq]
  rw [integral_add hi.integrableOn hiR.integrableOn, hreflect]
  have hz : (∫ x in ball 0 1, ‖Z x‖ ^ 2) =
      ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
    have he : (fun x => ‖Z x‖ ^ 2) = (boundaryHalfBall 1).indicator (fun x => ‖F x‖ ^ 2) := by
      funext x
      by_cases hx : x ∈ boundaryHalfBall 1 <;> simp [Z, hx]
    rw [he, integral_indicator (isOpen_boundaryHalfBall 1).measurableSet,
      Measure.restrict_restrict (isOpen_boundaryHalfBall 1).measurableSet,
      inter_eq_left.mpr (show boundaryHalfBall 1 ⊆ ball 0 1 from inter_subset_left)]
  change (∫ x in ball 0 1, ‖Z x‖ ^ 2) + (∫ x in ball 0 1, ‖Z x‖ ^ 2) = _
  rw [hz]
  ring

end LiquidDrop
