import NoCompromise.Regularity.FluxDefect

/-! # Genuine height moments and volume bounds in the original scale -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integrableOn_cylindrical_height (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (r c : ℝ) :
    IntegrableOn (fun x : AmbientSpace => (x 2 - c) ^ 2) (standardCylinder r)
      (canonicalPerimeterMeasure E hE hmE) := by
  let : IsFiniteMeasureOnCompacts (canonicalPerimeterMeasure E hE hmE) :=
    (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  have hc : Continuous (fun x : AmbientSpace => (x 2 - c) ^ 2) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact
    (isBounded_standardCylinder r).isCompact_closure).mono_set subset_closure

lemma surface_height_moment_eq (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (r c : ℝ) :
    (∫ x in standardCylinder r ∩ reducedBoundary E hE hmE, (x 2 - c) ^ 2
      ∂hausdorffMeasure2 3) =
        ∫ x in standardCylinder r, (x 2 - c) ^ 2 ∂canonicalPerimeterMeasure E hE hmE := by
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet]

lemma lintegral_surface_height_moment_eq (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (r c : ℝ) :
    (∫⁻ x in standardCylinder r ∩ reducedBoundary E hE hmE,
      ENNReal.ofReal ((x 2 - c) ^ 2) ∂hausdorffMeasure2 3) =
      ENNReal.ofReal (∫ x in standardCylinder r ∩ reducedBoundary E hE hmE,
        (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) := by
  rw [surface_height_moment_eq]
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet]
  have hi := integrableOn_cylindrical_height E hE hmE r c
  rw [IntegrableOn, canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet] at hi
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)).symm

lemma volume_cylindricalCore_le {r s : ℝ} (hr : 0 < r) :
    volume (cylindricalCore r s) ≤ ENNReal.ofReal ((32 * Real.pi / 3) * r ^ 3) := by
  have hs : cylindricalCore r s ⊆ ball (0 : AmbientSpace) (2 * r) := by
    apply (inter_subset_right : cylindricalCore r s ⊆ standardCylinder r).trans
    rw [standardCylinder_eq_cylinder]
    have hn : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by simp
    apply (cylinder_subset_ball 0 hr.le hn).trans
    apply ball_subset_ball
    apply mul_le_mul_of_nonneg_right _ hr.le
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  apply (measure_mono hs).trans
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * r) ^ 3)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_rfl

end LiquidDrop
