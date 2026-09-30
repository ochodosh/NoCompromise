module

public import NoCompromise.Regularity.ApproxHarmonicEstimateBounds
public import NoCompromise.Regularity.GraphApproxHeight

@[expose] public section

/-!
# Genuine graph approximation with approximate harmonicity

The constants are chosen after the prescribed Lipschitz constant and before the
height clamp, the set, and the quasiminimality coefficient. No uniform growth in
the Lipschitz parameter is asserted here.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Actual small excess gives a graph with controlled loss and energy and the
full compact-C1 test residual. The same constant works for every positive
requested height clamp. -/
theorem graph_approximation_approximate_harmonic
    {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ C > 0, ∀ τ : ℝ, 0 < τ → ∃ ε > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasGraphCapPhases E ∧
      IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable (1 / 2) 0 (1 / 2) ∧
      ∃ (G : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        MeasurableSet G ∧ G ⊆ ball 0 (1 / 2) ∧ LipschitzWith ⟨γ, hγ.le⟩ f ∧
        (∀ x, |f x| ≤ τ) ∧
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
            graphProjectionN 2 ⁻¹' G = graphMap f '' G ∧
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
          (hausdorffMeasure2 3).real
            ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
              (graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) ≤
            C * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
              (EuclideanSpace.single 2 1) ∧
        IntegrableOn (fun x => ‖gradient f x‖ ^ 2) (ball 0 (1 / 2)) volume ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
          C * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) ∧
        ∀ (ζ : EuclideanSpace ℝ (Fin 2) → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ ball 0 (1 / 2) → ∀ M : ℝ, 0 ≤ M →
          (∀ p, ‖gradient ζ p‖ ≤ M) →
          |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
            inner ℝ (gradient f p) (gradient ζ p)| ≤
            C * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
              (EuclideanSpace.single 2 1) + ω) * M := by
  obtain ⟨A, hA, hgraphs⟩ := graph_approximation_arbitrary_height hγ hγ8
  let C := A + 2 * (A / γ ^ 2) + 2 + Real.pi
  have hquot : 0 ≤ A / γ ^ 2 := div_nonneg hA.le (sq_nonneg γ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith [Real.pi_pos]
  have hBC : A / γ ^ 2 ≤ C := by dsimp [C]; linarith [Real.pi_pos]
  refine ⟨C, hC, fun τ hτ => ?_⟩
  obtain ⟨ε, hε, hg⟩ := hgraphs τ hτ
  refine ⟨min ε 1, lt_min hε (by norm_num), fun E ω hE h0 he => ?_⟩
  obtain ⟨hphase, hcap, G, f, hG, hGB, hf, hfh, hgraph, hloss, hi, henergy⟩ :=
    hg E ω hE h0 (he.trans (min_le_left _ _))
  have hex : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
  have hex1 : cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) ≤ 1 := by
    have hh := he.trans (min_le_right _ _)
    linarith [hE.nonneg]
  have hbase : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) ≤
      (A / γ ^ 2) * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) :=
    (le_add_of_nonneg_right measureReal_nonneg).trans hloss
  have hheight : ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2), |z 2| ≤ 1 / 4 := by
    intro z hz
    have hh := hcap.1.2.2.2.2 z hz
    simp only [sub_zero] at hh
    linarith
  refine ⟨hphase, hcap, G, f, hG, hGB, hf, hfh, hgraph,
    hloss.trans (mul_le_mul_of_nonneg_right hBC hex), hi,
    henergy.trans (mul_le_mul_of_nonneg_right hAC hex), ?_⟩
  intro ζ hζ hcζ hsζ M hM hζM
  exact approxHarmonic_residual_of_bounds hE hphase hheight hf
    (by change γ ≤ 1; linarith) hG hGB hgraph hquot hA.le hbase henergy hex1
    hζ hcζ hsζ hM hζM

end LiquidDrop
