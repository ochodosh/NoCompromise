module

public import NoCompromise.Regularity.ApproxHarmonicEstimateDecomposition
public import NoCompromise.Regularity.ApproxHarmonicEstimateError
public import NoCompromise.Regularity.ApproxHarmonicEstimateTestBounds

@[expose] public section

/-! # Combining the genuine graph-variation and extension errors -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- An actual graph subset of the reduced boundary gives a residual controlled
by its Dirichlet energy, omitted base, omitted boundary, and true volume error. -/
theorem approxHarmonic_residual_from_graph
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG : MeasurableSet G) (hGB : G ⊆ ball 0 (1 / 2))
    (hgraph : graphMap f '' G ⊆
      reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2))
    (hfheight : ∀ p ∈ G, |f p| ≤ 1 / 4)
    (hheight : ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2), |z 2| ≤ 1 / 4)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    {M N : ℝ} (hM : 0 ≤ M) (hζM : ∀ p, ‖gradient ζ p‖ ≤ M)
    (hζN : ∀ p, |ζ p| ≤ N) :
    |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      inner ℝ (gradient f p) (gradient ζ p)| ≤
      M * ((∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f p‖ ^ 2) +
        (K : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
        (hausdorffMeasure2 3).real
          ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
            graphMap f '' G)) +
      ω * N * (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).real
        (standardCylinder (1 / 2)) := by
  let B := ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)
  let L := fun p => inner ℝ (gradient f p) (gradient ζ p)
  let Q := fun p => inner ℝ (gradient f p) (gradient ζ p) /
    Real.sqrt (1 + ‖gradient f p‖ ^ 2)
  have hi := integrableOn_approxHarmonic_flux hf (A := B) isBounded_ball hM hζM
  have hsplit : (∫ p in B, L p) = (∫ p in G, L p) + ∫ p in B \ G, L p := by
    have he := setIntegral_sdiff hG hi.1 hGB
    change (∫ p in B \ G, L p) = (∫ p in B, L p) - ∫ p in G, L p at he
    linarith
  have hn := approxHarmonic_integral_nonlinear_error hf hK
    (isBounded_ball.subset hGB) hM hζM
  have hb := approxHarmonic_bad_base_integral hf
    (isBounded_ball.subset (sdiff_subset : B \ G ⊆ B)) hM hζM
  have hv := approxHarmonic_graph_flux_bound hE hf hG hgraph hfheight hheight
    hζ hcζ hsζ hζM hζN
  have henergy : (∫ p in G, ‖gradient f p‖ ^ 2) ≤ ∫ p in B, ‖gradient f p‖ ^ 2 :=
    setIntegral_mono_set hi.2.2 (ae_of_all _ fun _ => sq_nonneg _)
      (ae_of_all _ hGB)
  have henergyM := mul_le_mul_of_nonneg_left henergy hM
  have hgood : |∫ p in G, L p| ≤ |(∫ p in G, L p) - ∫ p in G, Q p| + |∫ p in G, Q p| := by
    have he := abs_add_le ((∫ p in G, L p) - ∫ p in G, Q p) (∫ p in G, Q p)
    simpa only [sub_add_cancel] using he
  change |∫ p in B, L p| ≤ _
  rw [hsplit]
  apply (abs_add_le _ _).trans
  dsimp only [L, Q] at hgood ⊢
  nlinarith

end LiquidDrop
