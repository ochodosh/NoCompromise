import NoCompromise.Regularity.GraphBaseCoverage
import NoCompromise.Regularity.GraphBadBase
import NoCompromise.Area.Graph

/-! # Quantitative loss of the actual Lipschitz graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

lemma graphMap_eq_graphAppend (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : graphMap f x = graphAppendN x (f x) := by
  ext i
  fin_cases i <;> simp [graphMap, graphAppendN, graphBaseN, Fin.sum_univ_two]

lemma reducedBoundary_graphBaseRegion_measure_lt_top
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : MeasurableSet B) :
    hausdorffMeasure2 3 (reducedBoundary E hE hmE ∩ graphBaseRegion B) < ∞ := by
  let : IsFiniteMeasureOnCompacts (canonicalPerimeterMeasure E hE hmE) :=
    (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  rw [inter_comm, ← canonicalPerimeterMeasure_apply_eq_reducedBoundary_area E hE hmE
    (measurableSet_graphBaseRegion hB)]
  exact (isBounded_graphBaseRegion B).measure_lt_top

lemma HasGraphCapPhases.goodBase_real_measure_bound
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ) ≤
      (25 / (c * γ ^ 2)) * cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  have hn : 0 ≤ cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE hmE (cylinder 0 1 (EuclideanSpace.single 2 1))
        (EuclideanSpace.single 2 1)
  have he := ENNReal.toReal_mono (by finiteness) (h.goodBase_measure_bound hE hmE hc hγ)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hn] at he
  exact he

/-- Actual omitted base area plus actual omitted reduced-boundary area is
controlled by the genuine unit excess. The maximal threshold c is explicit. -/
theorem HasGraphCapPhases.graph_loss
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hG : MeasurableSet (graphGoodBase E hE hmE c γ))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hfix : ∀ p ∈ graphGoodBoundary E hE hmE c γ, f (graphProjectionN 2 p) = p 2) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ) +
      (hausdorffMeasure2 3).real ((reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) \
        (graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) ≤
      (50 / (c * γ ^ 2) + 3 / 2) *
        cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  let B := ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ
  have hB : MeasurableSet B := measurableSet_ball.diff hG
  have hBB : B ⊆ ball 0 (1 / 2) := sdiff_subset
  have hs : (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) \
      (graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ⊆
        reducedBoundary E hE hmE ∩ graphBaseRegion B := by
    simpa only [graphMap_eq_graphAppend, graphBaseRegion, inter_assoc] using
      reducedBoundary_sdiff_graph_subset_badBase E hE hmE c γ f hfix
  have hm := measureReal_mono hs
    (reducedBoundary_graphBaseRegion_measure_lt_top E hE hmE hB).ne
  have ha := hm.trans
    ((h.bad_base_area hE hmE hB hBB).1.trans (h.bad_base_area hE hmE hB hBB).2)
  have hb := h.goodBase_real_measure_bound hE hmE hc hγ
  change volume.real B ≤ _ at hb
  change volume.real B + _ ≤ _
  have hcval : 50 / (c * γ ^ 2) = 2 * (25 / (c * γ ^ 2)) := by ring
  rw [hcval]
  nlinarith

end LiquidDrop
