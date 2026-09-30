module

public import NoCompromise.Regularity.GraphEnergyExtension
public import NoCompromise.Regularity.GraphDirichlet

@[expose] public section

/-! # Global graph energy without a prescribed clamping height -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

theorem HasGraphCapPhases.graph_energy
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : MeasurableSet (graphGoodBase E hE hmE c γ))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : LipschitzWith ⟨γ, hγ.le⟩ f)
    (hgraph : (reducedBoundary E hE hmE ∩ standardCylinder (1 / 2)) ∩
      graphProjectionN 2 ⁻¹' graphGoodBase E hE hmE c γ =
        graphMap f '' graphGoodBase E hE hmE c γ) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
      (2 + 25 / c) * cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  have hred : graphMap f '' graphGoodBase E hE hmE c γ ⊆ reducedBoundary E hE hmE := by
    rw [← hgraph]
    exact inter_subset_left.trans inter_subset_left
  have hU : graphMap f '' graphGoodBase E hE hmE c γ ⊆ standardCylinder 1 := by
    rw [← hgraph]
    apply (inter_subset_left.trans inter_subset_right).trans
    rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
    exact cylinder_mono (by norm_num)
  have hi := graph_dirichlet_le_normalExcess E hE hmE hf hγ1 hG hred
    (isOpen_standardCylinder 1).measurableSet (isBounded_standardCylinder 1) hU
  have hgood : (∫ x in graphGoodBase E hE hmE c γ, ‖gradient f x‖ ^ 2) ≤
      2 * cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one, standardCylinder_eq_cylinder] using hi.2
  have hext := h.graph_extension_energy hE hmE hc hγ hG hf
  nlinarith

end LiquidDrop
