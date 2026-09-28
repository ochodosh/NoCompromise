import NoCompromise.Regularity.GraphProjectedExcess

/-! # The maximal-density condition controls genuine excess at good centers -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma projectedExcessMeasure_eq_normalExcessIntegral
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) :
    projectedExcessMeasure E hE hmE A = ENNReal.ofReal
      (normalExcessIntegral E hE hmE
        ((graphProjectionN 2 ⁻¹' A) ∩ standardCylinder (3 / 4))
        (EuclideanSpace.single 2 1)) := by
  rw [projectedExcessMeasure, Measure.map_apply (graphProjectionN 2).measurable hA,
    withDensity_apply _ (hA.preimage (graphProjectionN 2).measurable),
    Measure.restrict_restrict (hA.preimage (graphProjectionN 2).measurable),
    canonicalPerimeterMeasure_eq_reducedBoundary_area]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_normal_excess E hE hmE
      ((isBounded_standardCylinder (3 / 4)).subset inter_subset_right) _)
      (Eventually.of_forall fun _ => sq_nonneg _)).symm

lemma vertical_cylinder_subset_projected_ball (p : AmbientSpace) (r : ℝ) :
    cylinder p r (EuclideanSpace.single 2 1) ⊆
      graphProjectionN 2 ⁻¹' ball (graphProjectionN 2 p) r := by
  intro y hy
  have hy' : y - p ∈ standardCylinder r := by
    rw [standardCylinder_eq_cylinder]
    simpa only [cylinder, mem_ofPred_eq, sub_zero] using hy
  change dist (graphProjectionN 2 y) (graphProjectionN 2 p) < r
  simpa only [dist_eq_norm, map_sub] using hy'.1

/-- The exact local estimate used in the two-point graph argument. -/
theorem cylindricalExcess_le_of_good_base
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {c γ : ℝ} (hc : 0 ≤ c)
    {p : AmbientSpace} (hp : p ∈ standardCylinder (1 / 2))
    (hg : graphProjectionN 2 p ∈ goodExcessBase E hE hmE c γ)
    {r : ℝ} (hr : 0 < r) (hr8 : r < 1 / 8) :
    cylindricalExcess E hE hmE p r (EuclideanSpace.single 2 1) ≤ Real.pi * c * γ ^ 2 := by
  let A := ball (graphProjectionN 2 p) r
  let V := (graphProjectionN 2 ⁻¹' A) ∩ standardCylinder (3 / 4)
  have hsub : cylinder p r (EuclideanSpace.single 2 1) ⊆ V := by
    intro y hy
    refine ⟨vertical_cylinder_subset_projected_ball p r hy, ?_⟩
    rw [standardCylinder_eq_cylinder] at hp ⊢
    exact cylinder_mono (by linarith : (1 / 2 : ℝ) + r ≤ 3 / 4)
      (cylinder_subset_add_radius hp hy)
  have hn : ENNReal.ofReal
      (normalExcessIntegral E hE hmE (cylinder p r (EuclideanSpace.single 2 1))
        (EuclideanSpace.single 2 1)) ≤ projectedExcessMeasure E hE hmE A := by
    rw [projectedExcessMeasure_eq_normalExcessIntegral E hE hmE measurableSet_ball]
    exact ENNReal.ofReal_le_ofReal (normalExcessIntegral_mono E hE hmE
      ((isBounded_standardCylinder (3 / 4)).subset inter_subset_right) hsub _)
  have hratio : projectedExcessMeasure E hE hmE A / volume A ≤
      ENNReal.ofReal (c * γ ^ 2) := by
    apply le_trans _ hg.1
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hr8 le_rfl))
  have hv0 : volume A ≠ 0 := (measure_ball_pos volume _ hr).ne'
  have hvt : volume A ≠ ∞ := measure_ball_lt_top.ne
  have hmass : projectedExcessMeasure E hE hmE A ≤
      ENNReal.ofReal (c * γ ^ 2) * volume A :=
    (ENNReal.div_le_iff hv0 hvt).mp hratio
  have hvol : volume A = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hr.le, mul_comm]
  have hcg : 0 ≤ c * γ ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hh := hn.trans hmass
  rw [hvol, ← ENNReal.ofReal_mul hcg] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hcg (mul_nonneg Real.pi_pos.le (sq_nonneg r)))).mp hh
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith only [hh']

end LiquidDrop
