import NoCompromise.Regularity.ApproxHarmonicEstimateField
import NoCompromise.Regularity.GraphBadBase

/-! # The genuine perimeter first variation for the fixed vertical field -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The signed phase information gives the exact total area in the half cylinder. -/
lemma HasGraphCapPhases.cylinder_half_mass_eq
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    (canonicalPerimeterMeasure E hE hmE).real (standardCylinder (1 / 2)) =
      Real.pi / 4 + (1 / 2 : ℝ) * normalExcessIntegral E hE hmE
        (standardCylinder (1 / 2)) (EuclideanSpace.single 2 1) := by
  have hs : graphBaseRegion (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) =
      standardCylinder (1 / 2) := inter_eq_left.mpr fun x hx => mem_ball_zero_iff.mpr hx.1
  have he := h.area_on_base_eq hE hmE measurableSet_ball (subset_refl _)
  rw [hs] at he
  have hv : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) = Real.pi / 4 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  rw [hv] at he
  rw [Measure.real, canonicalPerimeterMeasure_apply_eq_reducedBoundary_area E hE hmE
    (isOpen_standardCylinder _).measurableSet, inter_comm]
  exact he

lemma HasGraphCapPhases.cylinder_half_mass_le
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    (canonicalPerimeterMeasure E hE hmE).real (standardCylinder (1 / 2)) ≤
      Real.pi / 4 + (1 / 2 : ℝ) *
        cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  rw [h.cylinder_half_mass_eq hE hmE]
  have hm := normalExcessIntegral_mono E hE hmE (isBounded_standardCylinder 1)
    (U := standardCylinder (1 / 2)) (by
      rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
      exact cylinder_mono (by norm_num)) (EuclideanSpace.single 2 1)
  simp only [standardCylinder_eq_cylinder, cylindricalExcess, one_pow, div_one] at hm ⊢
  linarith

/-- Apply the actual quasiminimal first variation to the constructed compact
vertical field. The right side retains the actual local perimeter mass. -/
theorem IsOmegaMinimal.approxHarmonic_vertical_variation
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    {N : ℝ} (hζN : ∀ p, |ζ p| ≤ N) :
    |∫ z in standardCylinder (1 / 2),
      tangentialDivergence (approxHarmonicField ζ)
        (reducedNormal E hE.locallyFinite hE.nullMeasurable) z
          ∂canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable| ≤
      ω * N * (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).real
        (standardCylinder (1 / 2)) := by
  let μ := canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
  let ν := reducedNormal E hE.locallyFinite hE.nullMeasurable
  let C := standardCylinder (1 / 2)
  obtain ⟨hX, hcX, hsX, hXB⟩ := approxHarmonicField_admissible hζ hcζ hsζ
  have hv := hE.bounded_first_variation hX hcX hXB
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area] at hv
  have htd : (∫ z in C, tangentialDivergence (approxHarmonicField ζ) ν z ∂μ) =
      ∫ z, tangentialDivergence (approxHarmonicField ζ) ν z ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      approxHarmonicField_tangential_zero_off_cylinder hsζ ν hz
  have hf : (∫ z in C, |inner ℝ (approxHarmonicField ζ z) (ν z)| ∂μ) =
      ∫ z, |inner ℝ (approxHarmonicField ζ z) (ν z)| ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hsX ht)), inner_zero_left, abs_zero]
  let : IsFiniteMeasureOnCompacts μ :=
    (canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict C) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isBounded_standardCylinder (1 / 2)).measure_lt_top⟩
  have hb : (∫ z in C, |inner ℝ (approxHarmonicField ζ z) (ν z)| ∂μ) ≤ N * μ.real C := by
    have he := integral_mono_of_nonneg
      (ae_of_all (μ.restrict C) fun z => abs_nonneg (inner ℝ (approxHarmonicField ζ z) (ν z)))
      (integrable_const N) ?_
    · simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
        mul_comm] using he
    · filter_upwards [ae_restrict_of_ae
        (ae_mem_reducedBoundary E hE.locallyFinite hE.nullMeasurable)] with z hz
      exact (approxHarmonicField_normal_flux_le ζ z (ν z)
        (norm_reducedNormal E hE.locallyFinite hE.nullMeasurable hz)).trans (hζN _)
  change |∫ z in C, tangentialDivergence (approxHarmonicField ζ) ν z ∂μ| ≤ _
  rw [htd]
  apply hv.trans
  rw [← hf]
  exact (mul_le_mul_of_nonneg_left hb hE.nonneg).trans_eq (by ring)

end LiquidDrop
