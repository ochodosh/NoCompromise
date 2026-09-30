module

public import NoCompromise.Regularity.GraphAffineHeightArea

@[expose] public section

/-! # Full boundary height from a graph piece and its actual omitted area -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A genuine surface moment comparison on any bounded Borel subset of the half
cylinder. The omitted area is that of the actual boundary outside the extension
graph. The only pointwise error bound concerns actual boundary points. -/
theorem graphAffineHeight_boundary_moment_le
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) (p : EuclideanSpace ℝ (Fin 2)) (b : ℝ)
    {U : Set AmbientSpace} (hU : MeasurableSet U)
    (hUC : U ⊆ standardCylinder (1 / 2)) {ρ : ℝ}
    (hproj : ∀ z ∈ U, graphProjectionN 2 z ∈ ball 0 ρ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ reducedBoundary E hE hmE ∩ U,
      |z 2 - b - inner ℝ p (graphProjectionN 2 z)| ≤ M) :
    (∫ z in U, (inner ℝ (graphUnitNormal p) z -
      b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2 ∂canonicalPerimeterMeasure E hE hmE) ≤
      2 * (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        (f x - b - inner ℝ p x) ^ 2) +
      M ^ 2 * (hausdorffMeasure2 3).real
        ((reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) \
          graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let q := fun z : AmbientSpace => (inner ℝ (graphUnitNormal p) z -
    b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2
  let A := reducedBoundary E hE hmE ∩ U
  let T := reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)
  let S := graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)
  have hA : MeasurableSet A := (measurableSet_reducedBoundary E hE hmE).inter hU
  have hS : MeasurableSet S := (measurableEmbedding_graphMap hf).measurableSet_image.mpr
    measurableSet_ball
  have hq : Continuous q := by dsimp only [q]; fun_prop
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  have hqi : IntegrableOn q U μ :=
    (hq.continuousOn.integrableOn_compact
      ((isBounded_standardCylinder (1 / 2)).subset hUC).isCompact_closure).mono_set subset_closure
  have hqA : IntegrableOn q A (hausdorffMeasure2 3) := by
    simpa only [IntegrableOn, μ, canonicalPerimeterMeasure_eq_reducedBoundary_area,
      Measure.restrict_restrict hU, inter_comm, A] using hqi
  have hmoment : (∫ z in U, q z ∂μ) = ∫ z in A, q z ∂hausdorffMeasure2 3 := by
    dsimp only [μ]
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area,
      Measure.restrict_restrict hU, inter_comm]
  have hgraph := graphAffineHeight_integral_graph_le hf hK p b
    (A := ball 0 ρ) measurableSet_ball isBounded_ball
  have hgoodsub : A ∩ S ⊆ graphMap f '' ball 0 ρ := by
    rintro z ⟨hz, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simpa only [graphAffineHeight_projection] using hproj (graphMap f x) hz.2
  have hgood : (∫ z in A ∩ S, q z ∂hausdorffMeasure2 3) ≤
      ∫ z in graphMap f '' ball 0 ρ, q z ∂hausdorffMeasure2 3 :=
    setIntegral_mono_set hgraph.1 (ae_of_all _ fun z => sq_nonneg _)
      (ae_of_all _ hgoodsub)
  have hT : hausdorffMeasure2 3 T < ∞ := by
    dsimp only [T]
    rw [inter_comm, ← canonicalPerimeterMeasure_apply_eq_reducedBoundary_area E hE hmE
      (isOpen_standardCylinder _).measurableSet]
    exact (isBounded_standardCylinder (1 / 2)).measure_lt_top
  have hbadsub : A \ S ⊆ T \ S := fun z hz => ⟨⟨hz.1.1, hUC hz.1.2⟩, hz.2⟩
  have hfinite : hausdorffMeasure2 3 (T \ S) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt hT).ne
  let : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (A \ S)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_mono hbadsub).trans_lt (lt_top_iff_ne_top.mpr hfinite)⟩
  have hb : (∫ z in A \ S, q z ∂hausdorffMeasure2 3) ≤
      M ^ 2 * (hausdorffMeasure2 3).real (T \ S) := by
    have hh : (∫ z in A \ S, q z ∂hausdorffMeasure2 3) ≤
        (hausdorffMeasure2 3).real (A \ S) * M ^ 2 := by
      have hd := integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg
        (inner ℝ (graphUnitNormal p) z - b / Real.sqrt (1 + ‖p‖ ^ 2)))
        (integrable_const (μ := (hausdorffMeasure2 3).restrict (A \ S)) (M ^ 2)) ?_
      · simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] using hd
      · filter_upwards [ae_restrict_mem (hA.diff hS)] with z hz
        exact (graphAffineHeight_sq_le p b z).trans
          (by simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hM).mpr (hbound z hz.1))
    exact hh.trans (by
      have hm := mul_le_mul_of_nonneg_right (measureReal_mono hbadsub hfinite) (sq_nonneg M)
      simpa only [mul_comm] using hm)
  change (∫ z in U, q z ∂μ) ≤ _
  rw [hmoment, ← integral_inter_add_sdiff hS hqA]
  exact add_le_add (hgood.trans hgraph.2) hb

end LiquidDrop
