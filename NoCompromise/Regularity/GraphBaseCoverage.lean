import NoCompromise.Regularity.GraphGoodBaseLoss
import NoCompromise.Regularity.GraphSlices

/-! # The actual good graph misses only a null part of the maximal-function good set -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma HasGraphCapPhases.goodBase_ae_eq
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (c γ : ℝ) :
    (graphGoodBase E hE hmE c γ : Set (EuclideanSpace ℝ (Fin 2))) =ᵐ[volume]
      (goodExcessBase E hE hmE c γ : Set (EuclideanSpace ℝ (Fin 2))) :=
  graphGoodBase_ae_eq_goodExcessBase_of_fibers E hE hmE c γ
    ((ae_restrict_iff' measurableSet_ball).mp (h.ae_vertical_fiber hE hmE))

theorem HasGraphCapPhases.goodBase_measure_bound
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ graphGoodBase E hE hmE c γ) ≤
      ENNReal.ofReal (25 / (c * γ ^ 2)) *
        ENNReal.ofReal (cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1)) :=
  graphGoodBase_measure_bound_of_fibers E hE hmE hc hγ
    ((ae_restrict_iff' measurableSet_ball).mp (h.ae_vertical_fiber hE hmE))

end LiquidDrop
