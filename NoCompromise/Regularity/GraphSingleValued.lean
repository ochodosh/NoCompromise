module

public import NoCompromise.Regularity.GraphGoodExtension
public import NoCompromise.Regularity.GraphBaseCoverage

@[expose] public section

/-! # Actual oriented slices and the single-valued Borel good graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

/-- On almost every vertical fiber, a genuine binary BV representative has
finitely many interior jumps, with outward oriented jump sum exactly one. -/
def HasOrientedGraphSlices (E : Set AmbientSpace) : Prop :=
  ∀ᵐ p : EuclideanSpace ℝ (Fin 2) ∂volume.restrict (ball 0 (1 / 2)),
    ∃ g : ℝ → ℝ,
      IsBinaryBVRepresentativeOn
        (fun t => E.indicator (fun _ => (1 : ℝ)) (graphAppendN p t))
        g (-(3 / 4)) (3 / 4) ∧
      {t ∈ Ioo (-(1 / 2)) (1 / 2) | oneDimensionalJump g t ≠ 0}.Finite ∧
      -(∑ᶠ t : ℝ, (Ioo (-(1 / 2)) (1 / 2)).indicator (oneDimensionalJump g) t) = 1

lemma HasGraphCapPhases.oriented_graph_slices
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    HasOrientedGraphSlices E := by
  obtain ⟨τ, s, κ, σ, g, _, hj⟩ := h.exists_oriented_slices hE hmE
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [hj] with p hp hpB
  obtain ⟨hb, hf, _, hs⟩ := hp (ball_subset_ball (by norm_num) hpB)
  exact ⟨g p (-(3 / 4)) (3 / 4), hb, hf, hs⟩

/-- The genuine small-excess hypotheses produce the oriented slice property,
an actual Borel graph, and a Lipschitz extension. The good base agrees almost
everywhere with the maximal-function good set. -/
theorem graph_single_valued {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ c > 0, ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasOrientedGraphSlices E ∧
      MeasurableSet (graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ) ∧
      graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ ⊆
        goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ ∧
      (graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ :
          Set (EuclideanSpace ℝ (Fin 2))) =ᵐ[volume]
        (goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ :
          Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        LipschitzWith ⟨γ, hγ.le⟩ f ∧ (∀ x, |f x| ≤ 1 / 16) ∧
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
            graphProjectionN 2 ⁻¹' graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ =
          (fun x => graphAppendN x (f x)) ''
            graphGoodBase E hE.locallyFinite hE.nullMeasurable c γ := by
  obtain ⟨c, hc, εg, hεg, hg⟩ := exists_good_graph_extension hγ hγ8
  obtain ⟨εp, hεp, hp⟩ := graph_phase_caps
  refine ⟨c, hc, min εg εp, lt_min hεg hεp, fun E ω hE h0 he => ?_⟩
  obtain ⟨hmG, hGG, f, hf, hb, _, hgraph⟩ := hg E ω hE h0 (he.trans (min_le_left _ _))
  have hphase := (hp E ω hE h0 (he.trans (min_le_right _ _))).1
  exact ⟨hphase.oriented_graph_slices hE.locallyFinite hE.nullMeasurable,
    hmG, hGG, hphase.goodBase_ae_eq hE.locallyFinite hE.nullMeasurable c γ,
    f, hf, hb, hgraph⟩

end LiquidDrop
