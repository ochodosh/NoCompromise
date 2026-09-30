module

public import NoCompromise.Regularity.GraphGoodExtension
public import NoCompromise.Regularity.GraphEnergyExtension
public import NoCompromise.Regularity.GraphDirichlet

@[expose] public section

/-!
# Actual graph approximation for each fixed Lipschitz constant

All objects are constructed from quasiminimality and small excess. The constants
are quantified after the target Lipschitz constant, consistently with the
blueprint's order of choice. Uniform dependence on that parameter is not asserted.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

/-- Genuine graph approximation, with every constant chosen before the set and
quasiminimality coefficient. Both actual area loss and Dirichlet energy are
controlled; the correctly oriented phases and cleared caps are retained. -/
theorem graph_approximation_fixed_lipschitz {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ C > 0, ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasGraphCapPhases E ∧
      IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable (1 / 2) 0 (1 / 2) ∧
      ∃ (G : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        MeasurableSet G ∧ G ⊆ ball 0 (1 / 2) ∧ LipschitzWith ⟨γ, hγ.le⟩ f ∧
        (∀ x, |f x| ≤ 1 / 16) ∧
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
            graphProjectionN 2 ⁻¹' G = graphMap f '' G ∧
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
          (hausdorffMeasure2 3).real
            ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
              (graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) ≤
            (C / γ ^ 2) * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
              (EuclideanSpace.single 2 1) ∧
        IntegrableOn (fun x => ‖gradient f x‖ ^ 2) (ball 0 (1 / 2)) volume ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
          C * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) := by
  obtain ⟨c, hc, εg, hεg, hg⟩ := exists_good_graph_extension hγ hγ8
  obtain ⟨εp, hεp, hp⟩ := graph_phase_caps
  let C := 50 / c + 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, min εg εp, lt_min hεg hεp, fun E ω hE h0 he => ?_⟩
  obtain ⟨hphase, _, _, hcap⟩ := hp E ω hE h0 (he.trans (min_le_right _ _))
  obtain ⟨hG, _, f, hf, hheight, hfix, hgraph⟩ :=
    hg E ω hE h0 (he.trans (min_le_left _ _))
  let G := graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ
  have hGB : G ⊆ ball 0 (1 / 2) := graphGoodBase_subset_ball _ _ _ _ _
  have heq : (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
      graphProjectionN 2 ⁻¹' G = graphMap f '' G := by
    simpa only [graphMap_eq_graphAppend] using hgraph
  have hred : graphMap f '' G ⊆ reducedBoundary E hE.locallyFinite hE.nullMeasurable := by
    rw [← heq]
    exact inter_subset_left.trans inter_subset_left
  have hU : graphMap f '' G ⊆ standardCylinder 1 := by
    rw [← heq]
    apply (inter_subset_left.trans inter_subset_right).trans
    rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
    exact cylinder_mono (by norm_num)
  have hn : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
  have hloss := hphase.graph_loss hE.locallyFinite hE.nullMeasurable hc hγ hG f hfix
  have hcoef : 50 / (c * γ ^ 2) + 3 / 2 ≤ C / γ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    have he : 50 / (c * γ ^ 2) * γ ^ 2 = 50 / c := by field_simp [hc.ne', hγ.ne']
    rw [add_mul, he]
    have hγ1 : γ ≤ 1 := by linarith
    have hs : γ ^ 2 ≤ 1 := by nlinarith
    dsimp [C]
    nlinarith
  have hi := graph_dirichlet_le_normalExcess E hE.locallyFinite hE.nullMeasurable hf
    (by change γ ≤ 1; linarith) hG hred
    (isOpen_standardCylinder 1).measurableSet (isBounded_standardCylinder 1) hU
  have hgood : (∫ x in G, ‖gradient f x‖ ^ 2) ≤
      2 * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one, standardCylinder_eq_cylinder] using hi.2
  have hext := hphase.graph_extension_energy hE.locallyFinite hE.nullMeasurable hc hγ hG hf
  have hcsmall : 25 / c ≤ 50 / c := div_le_div_of_nonneg_right (by norm_num) hc.le
  refine ⟨hphase, hcap, G, f, hG, hGB, hf, hheight, heq,
    hloss.trans (mul_le_mul_of_nonneg_right hcoef hn),
    integrableOn_sq_gradient_of_lipschitz hf isBounded_ball.measure_lt_top, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hcsmall hn
  dsimp [C]
  change (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
    (∫ x in G, ‖gradient f x‖ ^ 2) + _ at hext
  nlinarith

end LiquidDrop
