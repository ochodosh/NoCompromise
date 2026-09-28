import NoCompromise.Regularity.HarmonicPointBounds
import NoCompromise.Regularity.GraphApproxHeight

/-!
# The actual graph and harmonic data for tilt improvement

The graph parameter is fixed at `1 / 16`. The graph, harmonic energy, and
center value/slope constants are chosen before the error scale and the requested
clamp height. All data are constructed from quasiminimality and small excess.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- A globally clamped Lipschitz graph has its genuine disk mean within the
same clamp interval. -/
lemma tiltAnalytic_mean_bound {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {τ : ℝ} (hb : ∀ x, |f x| ≤ τ) :
    |⨍ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f x| ≤ τ := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (ball 0 (1 / 2))
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin 2)))
        (r := (1 / 2 : ℝ)))⟩
  have hm : μ ≠ 0 := by
    intro he
    have he' := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin 2)) => ν univ) he
    simp only [μ, Measure.restrict_apply_univ] at he'
    change volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) = 0 at he'
    exact (measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1 / 2)).ne' he'
  have hi : Integrable f μ := (harmonicBlowup_hasH1_lipschitz hf).memLp_function.integrable
    (by norm_num)
  obtain ⟨x, hx⟩ := exists_le_average hm hi
  obtain ⟨y, hy⟩ := exists_average_le hm hi
  exact abs_le.mpr ⟨(abs_le.mp (hb x)).1.trans hx, hy.trans (abs_le.mp (hb y)).2⟩

/-- The complete analytic input to tilt improvement, with fixed graph parameter
`1 / 16` and constants independent of the scale and chosen clamp height. -/
theorem exists_tilt_analytic_data :
    ∃ Cg > 0, ∃ Cb > 0, ∃ Ch : ℝ, 1 ≤ Ch ∧
      ∀ θ : ℝ, 0 < θ → ∀ τ : ℝ, 0 < τ → ∃ ε > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      0 < cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasGraphCapPhases E ∧
      IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable (1 / 2) 0 (1 / 2) ∧
      ∃ (G : Set (EuclideanSpace ℝ (Fin 2))) (f h : EuclideanSpace ℝ (Fin 2) → ℝ),
        MeasurableSet G ∧ G ⊆ ball 0 (1 / 2) ∧
        LipschitzWith (⟨1 / 16, by norm_num⟩ : ℝ≥0) f ∧
        (∀ x, |f x| ≤ τ) ∧
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
          graphProjectionN 2 ⁻¹' G = graphMap f '' G ∧
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
          (hausdorffMeasure2 3).real
            ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
              graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ≤
          (256 * Cg) * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) ∧
        IntegrableOn (fun x => ‖gradient f x‖ ^ 2) (ball 0 (1 / 2)) volume ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
          Cg * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) ∧
        |⨍ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f x| ≤ τ ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 4)) ∧
        HasH1GradientOn h (gradient h) (ball 0 (1 / 4)) ∧
        HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), laplacianN h x = 0) ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          |harmonicBlowupFunction f
            (Real.sqrt (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
              (EuclideanSpace.single 2 1) + ω)) x - h x| ^ 2) ≤ θ ^ 6 ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          |h x| ^ 2 + ‖gradient h x‖ ^ 2) ≤ Cb ∧
        |h 0| + ‖gradient h 0‖ ≤ Ch := by
  obtain ⟨Cg, hCg, hg⟩ := graph_approximation_arbitrary_height
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1 / 8)
  obtain ⟨Cb, hCb, hh⟩ := harmonic_approximation_uniform
    (show 0 ≤ 256 * Cg by positivity) hCg.le
  obtain ⟨Ch, hCh, hp⟩ := harmonic_center_value_gradient_bound Cb hCb.le
  refine ⟨Cg, hCg, Cb, hCb, Ch, hCh, fun θ hθ τ hτ => ?_⟩
  obtain ⟨εg, hεg, hgraph⟩ := hg τ hτ
  obtain ⟨ε, hε, hεg', hhar⟩ := hh εg hεg (θ ^ 6) (by positivity)
  refine ⟨ε, hε, fun E ω hE h0 hpos hsmall => ?_⟩
  obtain ⟨hphase, hcap, G, f, hG, hGB, hf, hheight, hfix, hloss, hi, he⟩ :=
    hgraph E ω hE h0 (hsmall.trans hεg')
  have hloss' : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
      (hausdorffMeasure2 3).real
        ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
          graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ≤
      (256 * Cg) * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) := by
    convert hloss using 1
    ring
  have hbase : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) ≤
      (256 * Cg) * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) :=
    (le_add_of_nonneg_right ENNReal.toReal_nonneg).trans hloss'
  have hf1 : LipschitzWith 1 f := hf.weaken (by
    change (1 / 16 : ℝ) ≤ 1
    norm_num)
  obtain ⟨h, hc, hH1, hd, hz, herr, henergy⟩ :=
    hhar E ω hE h0 hpos hsmall G f hG hGB hf1 hfix hbase he
  exact ⟨hphase, hcap, G, f, h, hG, hGB, hf, hheight, hfix, hloss', hi, he,
    tiltAnalytic_mean_bound hf hheight, hc, hH1, hd, hz, herr, henergy,
    hp h hc.continuousOn hH1 hd henergy⟩

end LiquidDrop
