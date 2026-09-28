import NoCompromise.Regularity.ApproxHarmonicTest
import NoCompromise.Regularity.ApproxHarmonicAlgebra

/-! # Signed graph area and the actual vertical first-variation density -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The graph area pushforward also gives signed real integrals. No separate
integrability premise is needed for this identity of Bochner integrals. -/
theorem integral_graphMap_image {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG : MeasurableSet G) (q : AmbientSpace → ℝ) :
    (∫ z in graphMap f '' G, q z ∂hausdorffMeasure2 3) =
      ∫ p in G, Real.sqrt (1 + ‖gradient f p‖ ^ 2) * q (graphMap f p) := by
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    (measurableEmbedding_graphMap hf).integral_map,
    integral_withDensity_eq_integral_toReal_smul (measurable_graphAreaDensity f)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]

/-- Integrability of a signed graph integrand is equivalent to integrability
of its weighted pullback to the actual base. -/
theorem integrableOn_graphMap_image_iff
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG : MeasurableSet G) (q : AmbientSpace → ℝ) :
    IntegrableOn q (graphMap f '' G) (hausdorffMeasure2 3) ↔
      IntegrableOn (fun p => Real.sqrt (1 + ‖gradient f p‖ ^ 2) * q (graphMap f p))
        G volume := by
  unfold IntegrableOn
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    (measurableEmbedding_graphMap hf).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul' (measurable_graphAreaDensity f)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul, Function.comp_def]

/-- At a graph point with either actual unit-normal orientation and a flat
vertical cutoff, the weighted tangential divergence is the nonlinear graph flux. -/
lemma approxHarmonic_graph_density
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hψ : ContDiff ℝ 1 ψ)
    (ν : AmbientSpace → AmbientSpace) (p : EuclideanSpace ℝ (Fin 2))
    (hp : ψ (f p) = 1) (hdp : deriv ψ (f p) = 0)
    (hν : ν (graphMap f p) = graphUnitNormal (gradient f p) ∨
      ν (graphMap f p) = -graphUnitNormal (gradient f p)) :
    Real.sqrt (1 + ‖gradient f p‖ ^ 2) *
      tangentialDivergence
        (fun x : AmbientSpace => (ζ (graphProjectionN 2 x) * ψ (x 2)) •
          EuclideanSpace.single 2 1) ν (graphMap f p) =
      inner ℝ (gradient f p) (gradient ζ p) / Real.sqrt (1 + ‖gradient f p‖ ^ 2) := by
  have hp' : ψ (graphMap f p 2) = 1 := by simpa [graphMap] using hp
  have hdp' : deriv ψ (graphMap f p 2) = 0 := by simpa [graphMap] using hdp
  rw [tangentialDivergence_vertical_tensor hζ hψ ν _ hp' hdp']
  have hproj : graphProjectionN 2 (graphMap f p) = p := by
    ext i
    fin_cases i <;> simp [graphMap, graphProjectionN_apply]
  rw [hproj]
  have he := approxHarmonic_weighted_vertical_density (fderiv ℝ ζ p) (gradient f p)
  have hi : fderiv ℝ ζ p (gradient f p) = inner ℝ (gradient f p) (gradient ζ p) := by
    rw [← inner_gradient_left, real_inner_comm]
  rw [hi] at he
  rcases hν with hν | hν
  · rw [hν, mul_comm]
    exact he
  · rw [hν]
    simp only [PiLp.neg_apply, map_neg]
    convert he using 1
    ring

end LiquidDrop
