module

public import NoCompromise.Regularity.ApproxHarmonic
public import NoCompromise.Regularity.ApproxHarmonicEstimateScaling
public import NoCompromise.Regularity.HeightBoundBoundaryScaling
public import NoCompromise.Regularity.ExcessScaling

@[expose] public section

/-! # Approximate harmonicity at every admissible physical scale -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- At radius `r`, an actual normalized graph of the blown-up set supplies the
physical graph height `x ↦ r * f (r⁻¹ • x)`. Its residual has the exact `r²`
factor and the actual scaled volume error `ω*r`. All constants precede the set
and radius, and the same constant works for every requested height clamp. -/
theorem graph_approximation_approximate_harmonic_scaled
    {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ C > 0, ∀ τ : ℝ, 0 < τ → ∃ ε > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      ∀ r : ℝ, ∀ hr : 0 < r, r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε →
      ∃ (G : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        MeasurableSet G ∧ G ⊆ ball 0 (1 / 2) ∧ LipschitzWith ⟨γ, hγ.le⟩ f ∧
        (∀ x, |f x| ≤ τ) ∧
        (reducedBoundary (blowupSet E 0 r)
            (hE.locallyFinite.blowupSet (by norm_num) 0 hr)
            (nullMeasurableSet_blowupSet hE.nullMeasurable 0 hr) ∩
          standardCylinder (1 / 2)) ∩ graphProjectionN 2 ⁻¹' G = graphMap f '' G ∧
        ∀ (ζ : EuclideanSpace ℝ (Fin 2) → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ ball 0 (r / 2) → ∀ M : ℝ, 0 ≤ M →
          (∀ p, ‖gradient ζ p‖ ≤ M) →
          |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 2),
            inner ℝ (gradient (fun y => r * f (r⁻¹ • y)) p) (gradient ζ p)| ≤
            C * r ^ 2 * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r) * M := by
  obtain ⟨C, hC, hc⟩ := graph_approximation_approximate_harmonic hγ hγ8
  refine ⟨C, hC, fun τ hτ => ?_⟩
  obtain ⟨ε, hε, hh⟩ := hc τ hτ
  refine ⟨ε, hε, fun E ω hE h0 r hr hr1 he => ?_⟩
  have hB : IsOmegaMinimal (blowupSet E 0 r) (ω * r) := by
    apply IsOmegaMinimalAtScales.blowupSet hE 0 hr (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  have h0B : (0 : AmbientSpace) ∈ frontier (densityOne (blowupSet E 0 r)) := by
    simpa only [smul_zero] using (height_mem_frontier_blowup_zero E hr 0).mpr h0
  have heB : cylindricalExcess (blowupSet E 0 r) hB.locallyFinite hB.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + ω * r ≤ ε := by
    simpa only [cylindricalExcess_blowupSet_unit E hE.locallyFinite hE.nullMeasurable 0 hr]
      using he
  obtain ⟨_, _, G, f, hG, hGB, hf, hheight, hgraph, _, _, _, hres⟩ :=
    hh (blowupSet E 0 r) (ω * r) hB h0B heB
  refine ⟨G, f, hG, hGB, hf, hheight, hgraph, fun ζ hζ hcζ hsζ M hM hζM => ?_⟩
  have ha := approxHarmonic_residual_rescale hres hr hζ hcζ hsζ hM hζM
  simpa only [cylindricalExcess_blowupSet_unit E hE.locallyFinite hE.nullMeasurable 0 hr]
    using ha

end LiquidDrop
