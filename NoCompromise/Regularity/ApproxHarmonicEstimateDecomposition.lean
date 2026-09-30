module

public import NoCompromise.Regularity.ApproxHarmonicEstimateVariation
public import NoCompromise.Regularity.ApproxHarmonicEstimateArea
public import NoCompromise.Regularity.GraphNormal

@[expose] public section

/-! # Genuine first variation split into the graph and omitted boundary -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual graph flux is controlled by the true first variation and the
area omitted by the graph. The normal identification is proved from the graph
subset of the reduced boundary, and either orientation gives the same density. -/
theorem approxHarmonic_graph_flux_bound
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {f ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hgraph : graphMap f '' G ⊆
      reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2))
    (hfheight : ∀ p ∈ G, |f p| ≤ 1 / 4)
    (hheight : ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2), |z 2| ≤ 1 / 4)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    {M N : ℝ} (hζM : ∀ p, ‖gradient ζ p‖ ≤ M) (hζN : ∀ p, |ζ p| ≤ N) :
    |∫ p in G, inner ℝ (gradient f p) (gradient ζ p) /
        Real.sqrt (1 + ‖gradient f p‖ ^ 2)| ≤
      ω * N * (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).real
        (standardCylinder (1 / 2)) +
      M * (hausdorffMeasure2 3).real
        ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
          graphMap f '' G) := by
  let μ := canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
  let ν := reducedNormal E hE.locallyFinite hE.nullMeasurable
  let C := standardCylinder (1 / 2)
  let S := graphMap f '' G
  let T := tangentialDivergence (approxHarmonicField ζ) ν
  have hS : MeasurableSet S := measurableSet_graphMap_image hf hG
  have hC : MeasurableSet C := (isOpen_standardCylinder _).measurableSet
  have hSC : S ⊆ C := fun z hz => (hgraph hz).2
  have hSR : S ⊆ reducedBoundary E hE.locallyFinite hE.nullMeasurable :=
    fun z hz => (hgraph hz).1
  let : IsFiniteMeasureOnCompacts μ :=
    (canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict C) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isBounded_standardCylinder (1 / 2)).measure_lt_top⟩
  let : IsFiniteMeasure (μ.restrict (C \ S)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono sdiff_subset)
      (isBounded_standardCylinder (1 / 2)).measure_lt_top⟩
  obtain ⟨hX, hcX, _, _⟩ := approxHarmonicField_admissible hζ hcζ hsζ
  have hi : IntegrableOn T C μ := integrable_tangentialDivergence hX hcX
    (measurable_reducedNormal E hE.locallyFinite hE.nullMeasurable)
    ((ae_restrict_of_ae (ae_mem_reducedBoundary E hE.locallyFinite hE.nullMeasurable)).mono
      fun z hz => norm_reducedNormal E hE.locallyFinite hE.nullMeasurable hz)
  have hμS : μ.restrict S = (hausdorffMeasure2 3).restrict S := by
    rw [show μ = canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable from rfl,
      canonicalPerimeterMeasure_eq_reducedBoundary_area, Measure.restrict_restrict hS,
      inter_eq_left.mpr hSR]
  have hnormal := ae_reducedNormal_eq_graphUnitNormal_or_neg_base E
    hE.locallyFinite hE.nullMeasurable hf hG hSR
  have hflux : (∫ z in S, T z ∂μ) =
      ∫ p in G, inner ℝ (gradient f p) (gradient ζ p) /
        Real.sqrt (1 + ‖gradient f p‖ ^ 2) := by
    rw [hμS, integral_graphMap_image hf hG]
    apply integral_congr_ae
    filter_upwards [hnormal, ae_restrict_mem hG] with p hp hpG
    obtain ⟨hpψ, hdpψ⟩ := approxHarmonicCutoff_flat (hfheight p hpG)
    exact approxHarmonic_graph_density hζ approxHarmonicCutoff.contDiff ν p hpψ hdpψ hp
  have hbad : |∫ z in C \ S, T z ∂μ| ≤ M * μ.real (C \ S) := by
    have hb : ∀ᵐ z ∂μ.restrict (C \ S), ‖T z‖ ≤ M := by
      filter_upwards [ae_restrict_mem (hC.diff hS),
        ae_restrict_of_ae (ae_mem_reducedBoundary E hE.locallyFinite hE.nullMeasurable)]
        with z hz hzR
      rw [Real.norm_eq_abs]
      exact (approxHarmonicField_tangential_bound hζ ν z
        (norm_reducedNormal E hE.locallyFinite hE.nullMeasurable hzR)
        (hheight z ⟨hzR, hz.1⟩)).trans (hζM _)
    have hb' := norm_integral_le_of_norm_le_const hb
    simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ, mul_comm] using hb'
  have hmass : μ.real (C \ S) = (hausdorffMeasure2 3).real
      ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ C) \ S) := by
    have hs : (C \ S) ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable =
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ C) \ S := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff]
      tauto
    rw [Measure.real, canonicalPerimeterMeasure_apply_eq_reducedBoundary_area
      E hE.locallyFinite hE.nullMeasurable (hC.diff hS), hs]
    rfl
  have hsplit := setIntegral_sdiff hS hi hSC
  rw [hflux] at hsplit
  have he : (∫ p in G, inner ℝ (gradient f p) (gradient ζ p) /
      Real.sqrt (1 + ‖gradient f p‖ ^ 2)) = (∫ z in C, T z ∂μ) - ∫ z in C \ S, T z ∂μ := by
    linarith
  rw [he]
  apply (abs_sub _ _).trans
  have hv := hE.approxHarmonic_vertical_variation hζ hcζ hsζ hζN
  rw [hmass] at hbad
  exact add_le_add hv hbad

end LiquidDrop
