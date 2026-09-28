import NoCompromise.Regularity.GraphProjectedExcess

/-! # The quantitative good-base estimate for graph approximation -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma projectedExcessMeasure_base_disk (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    projectedExcessMeasure E hE hmE (ball 0 (3 / 4)) =
      projectedExcessMeasure E hE hmE univ := by
  rw [projectedExcessMeasure_apply E hE hmE measurableSet_ball,
    projectedExcessMeasure_apply E hE hmE MeasurableSet.univ, preimage_univ, univ_inter]
  congr 2
  have hs : (graphProjectionN 2 ⁻¹' ball 0 (3 / 4)) ∩ standardCylinder (3 / 4) =
      standardCylinder (3 / 4) := by
    apply inter_eq_right.mpr
    intro x hx
    simpa only [mem_preimage, mem_ball, dist_zero_right] using hx.1
  rw [hs]

/-- The first good-base estimate, with the explicit five-covering constant 25. -/
theorem projectedExcessMaximal_weak_bound (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    volume {x | ENNReal.ofReal (c * γ ^ 2) < projectedExcessMaximal E hE hmE x} ≤
      ENNReal.ofReal (25 / (c * γ ^ 2)) *
        projectedExcessMeasure E hE hmE (ball 0 (3 / 4)) := by
  rw [projectedExcessMeasure_base_disk]
  exact truncatedMaximalMeasure_weak_bound _ _ (mul_pos hc (sq_pos_of_pos hγ))

/-- Full blueprint `lem:good-base`: the omitted part of the half-unit base disk
is bounded by the genuine unit-cylinder excess, with C = 25. -/
theorem good_base_measure_bound (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ goodExcessBase E hE hmE c γ) ≤
      ENNReal.ofReal (25 / (c * γ ^ 2)) *
        ENNReal.ofReal (cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1)) := by
  have hs : ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ goodExcessBase E hE hmE c γ ⊆
      {x | ENNReal.ofReal (c * γ ^ 2) < projectedExcessMaximal E hE hmE x} := by
    intro x hx
    by_contra hh
    change ¬ ENNReal.ofReal (c * γ ^ 2) < projectedExcessMaximal E hE hmE x at hh
    exact hx.2 ⟨not_lt.mp hh, hx.1⟩
  apply (measure_mono hs).trans
  apply (projectedExcessMaximal_weak_bound E hE hmE hc hγ).trans
  rw [projectedExcessMeasure_base_disk]
  exact mul_le_mul' le_rfl (projectedExcessMeasure_mass_le E hE hmE)

end LiquidDrop
