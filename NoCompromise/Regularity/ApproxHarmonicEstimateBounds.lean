module

public import NoCompromise.Regularity.ApproxHarmonicEstimate

@[expose] public section

/-! # Quantitative residual for every furnished actual graph -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The boundary omitted by the good graph is exactly the boundary above its
omitted base. This uses the actual graph equality, not a graph parametrization
of all of the boundary. -/
lemma approxHarmonic_omitted_graph_eq
    {S : Set AmbientSpace} {G : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : (S ∩ standardCylinder (1 / 2)) ∩ graphProjectionN 2 ⁻¹' G =
      graphMap f '' G) :
    (S ∩ standardCylinder (1 / 2)) \ graphMap f '' G =
      S ∩ graphBaseRegion (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) := by
  rw [← hgraph]
  ext z
  simp only [graphBaseRegion, Set.mem_sdiff, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨hz, hc⟩, hn⟩
    exact ⟨hz, hc, mem_ball_zero_iff.mpr hc.1, fun hg => hn ⟨⟨hz, hc⟩, hg⟩⟩
  · rintro ⟨hz, hc, _, hn⟩
    exact ⟨⟨hz, hc⟩, fun hg => hn hg.2⟩

/-- A uniform estimate for every genuine graph with the supplied quantitative
loss and energy bounds. Constants are explicit; no graph is chosen here. -/
theorem approxHarmonic_residual_of_bounds
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    (hphase : HasGraphCapPhases E)
    (hheight : ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2), |z 2| ≤ 1 / 4)
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG : MeasurableSet G) (hGB : G ⊆ ball 0 (1 / 2))
    (hgraph : (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2)) ∩ graphProjectionN 2 ⁻¹' G = graphMap f '' G)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbase : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) ≤
      B * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1))
    (henergy : (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f p‖ ^ 2) ≤
      D * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1))
    (hexcess : cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) ≤ 1)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    {M : ℝ} (hM : 0 ≤ M) (hζM : ∀ p, ‖gradient ζ p‖ ≤ M) :
    |∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      inner ℝ (gradient f p) (gradient ζ p)| ≤
      (D + 2 * B + 2 + Real.pi) *
        (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
          (EuclideanSpace.single 2 1) + ω) * M := by
  let e := cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
    (EuclideanSpace.single 2 1)
  have he : 0 ≤ e := by
    simpa only [e, cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
  have hsub : graphMap f '' G ⊆ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2) := by rw [← hgraph]; exact inter_subset_left
  have hfh : ∀ p ∈ G, |f p| ≤ 1 / 4 := by
    intro p hp
    simpa only [graphMap_apply_two] using hheight (graphMap f p) (hsub ⟨p, hp, rfl⟩)
  have hN := approxHarmonic_test_value_le_gradient_bound hζ hsζ hM hζM
  have hr := approxHarmonic_residual_from_graph hE hf hK hG hGB hsub hfh hheight
    hζ hcζ hsζ hM hζM hN
  have ha := hphase.bad_base_area hE.locallyFinite hE.nullMeasurable
    (measurableSet_ball.diff hG)
    (sdiff_subset : ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G ⊆ _)
  have ha' := ha.1.trans ha.2
  rw [← approxHarmonic_omitted_graph_eq hgraph] at ha'
  have hm := hphase.cylinder_half_mass_le hE.locallyFinite hE.nullMeasurable
  have hm' : (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).real
      (standardCylinder (1 / 2)) ≤ Real.pi / 4 + 1 / 2 := by linarith
  have hb' : (K : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) ≤
      B * e :=
    (mul_le_mul_of_nonneg_right hK (measureReal_nonneg)).trans (by simpa using hbase)
  have hs : (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f p‖ ^ 2) +
      (K : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) +
      (hausdorffMeasure2 3).real
        ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
          graphMap f '' G) ≤ (D + 2 * B + 3 / 2) * e := by
    dsimp only [e] at hb' ⊢
    nlinarith
  apply hr.trans
  calc
    _ ≤ M * ((D + 2 * B + 3 / 2) * e) + ω * M * (Real.pi / 4 + 1 / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hs hM)
        (mul_le_mul_of_nonneg_left hm' (mul_nonneg hE.nonneg hM))
    _ ≤ (D + 2 * B + 2 + Real.pi) * (e + ω) * M := by
      have hp := Real.pi_pos
      have h1 : D + 2 * B + 3 / 2 ≤ D + 2 * B + 2 + Real.pi := by linarith
      have h2 : Real.pi / 4 + 1 / 2 ≤ D + 2 * B + 2 + Real.pi := by linarith
      have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg he hM)
      have h4 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hE.nonneg hM)
      nlinarith

end LiquidDrop
