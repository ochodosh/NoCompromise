import NoCompromise.Regularity.DeformationLimitProperties

/-! # Localized perimeter bounds on arbitrary horizontal bands -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The compression parameters and the observed horizontal band are independent.
The source height moment is localized to that same band. -/
theorem IsSlabCapConfiguration.compression_band_perimeter_bound
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {a b : ℝ} (hbr : b ≤ r) :
    perimeterIn (compressionCompetitor E r σ τ ε c) (cylindricalTransition r a b) ≤
      perimeterIn E (cylindricalTransition r a b) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in cylindricalTransition r a b, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  let Ext := verticalPhaseExtension E r
  let G := verticalCompression (compressionBeta σ τ ε) c '' Ext
  have hExt := hasLocallyFinitePerimeter_verticalPhaseExtension hE hmE h.1.1.le
  have hmExt := nullMeasurableSet_verticalPhaseExtension hmE r
  have hG := hasLocallyFinitePerimeter_verticalCompression hσ hst hε hε1 c Ext hExt hmExt
  have hmG := nullMeasurableSet_image_of_differentiable
    ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
      one_ne_zero)
    (verticalCompressionHomeomorph (compressionBeta σ τ ε)
      (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c).injective hmExt
  have hrest := h.extension_perimeter_annulus hExt hmExt (σ := a) hbr
  have hmass : canonicalPerimeterMeasure Ext hExt hmExt (horizontalAnnulus a b) =
      perimeterIn E (cylindricalTransition r a b) := by
    have hh := congrArg (fun μ : Measure AmbientSpace => μ univ) hrest
    simpa only [Measure.restrict_apply_univ,
      canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalTransition r a b)] using hh
  have hbound := perimeter_verticalCompression_le_source_measure hσ hst hε hε1 c
    Ext hExt hmExt hG hmG (isOpen_horizontalAnnulus a b).measurableSet
  rw [verticalCompression_image_horizontalAnnulus _ (contDiff_compressionBeta hσ hst ε)
    (compressionBeta_ne_zero hε hε1), hmass] at hbound
  have hmom : (∫⁻ x in horizontalAnnulus a b, ENNReal.ofReal ((x 2 - c) ^ 2)
        ∂canonicalPerimeterMeasure Ext hExt hmExt) ≤
      ∫⁻ x in cylindricalTransition r a b, ENNReal.ofReal ((x 2 - c) ^ 2)
        ∂canonicalPerimeterMeasure E hE hmE := by
    rw [hrest]
  have hlocal : perimeterIn (compressionCompetitor E r σ τ ε c)
      (cylindricalTransition r a b) = perimeterIn G (cylindricalTransition r a b) := by
    apply variation_congr_ae
    apply (ae_restrict_iff' (isOpen_cylindricalTransition r a b).measurableSet).mpr
    exact Eventually.of_forall fun x hx => compressionCompetitor_indicator_between E r σ τ ε c
      ⟨(abs_lt.mp hx.2.2).1.le, (abs_lt.mp hx.2.2).2⟩
  rw [hlocal, ← canonicalPerimeterMeasure_open G hG hmG (isOpen_cylindricalTransition r a b)]
  exact (measure_mono inter_subset_left).trans (hbound.trans (by gcongr))


/-- The localized bound passes to every genuine compact-local L¹ limit. -/
theorem IsSlabCapConfiguration.compression_limit_band_perimeter_bound
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) (hmF : NullMeasurableSet F volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x -
          F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0))
    {a b : ℝ} (hbr : b ≤ r) :
    perimeterIn F (cylindricalTransition r a b) ≤
      perimeterIn E (cylindricalTransition r a b) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in cylindricalTransition r a b, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  have hls := perimeterIn_le_liminf_of_locally_l1 (isOpen_cylindricalTransition r a b)
    (fun j => (compressionCompetitor_locallyFinitePerimeter hE hmE h.1.1.le
      hσ hst (hε j) (hε1 j) c).2) hmF (fun K hK _ => hconv K hK)
  apply hls.trans
  have hh := liminf_le_liminf (f := atTop) (Eventually.of_forall fun j =>
    h.compression_band_perimeter_bound hσ hst (hε j) (hε1 j) (a := a) hbr)
  simpa only [liminf_const] using hh

/-- A bounded cylinder controls its height moment by its perimeter mass. -/
lemma cylinder_height_moment_le_mass (μ : Measure AmbientSpace) {r c : ℝ}
    {A : Set AmbientSpace} (hA : MeasurableSet A) (hAC : A ⊆ standardCylinder r) :
    (∫⁻ x in A, ENNReal.ofReal ((x 2 - c) ^ 2) ∂μ) ≤
      ENNReal.ofReal ((r + |c|) ^ 2) * μ A := by
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal ((r + |c|) ^ 2) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      apply ENNReal.ofReal_le_ofReal
      have hh := (hAC hx).2
      have hh' : |x 2 - c| ≤ r + |c| :=
        (abs_sub _ _).trans (add_le_add hh.le le_rfl)
      nlinarith [sq_nonneg (r + |c| - |x 2 - c|), sq_abs (x 2 - c), abs_nonneg (x 2 - c)]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- In particular, a finite fixed multiple of the original band mass bounds
all limiting band mass; no inverse-compression constant enters this estimate. -/
theorem IsSlabCapConfiguration.compression_limit_band_mass_bound
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) (hmF : NullMeasurableSet F volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x -
          F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0))
    {a b : ℝ} (hbr : b ≤ r) :
    perimeterIn F (cylindricalTransition r a b) ≤
      (1 + ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
        ENNReal.ofReal ((r + |c|) ^ 2)) *
          perimeterIn E (cylindricalTransition r a b) := by
  apply (h.compression_limit_band_perimeter_bound hmF hσ hst hε hε1 hconv hbr).trans
  have hh := cylinder_height_moment_le_mass (canonicalPerimeterMeasure E hE hmE) (c := c)
    (isOpen_cylindricalTransition r a b).measurableSet inter_subset_right
  rw [canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalTransition r a b)] at hh
  calc
    _ ≤ perimeterIn E (cylindricalTransition r a b) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          (ENNReal.ofReal ((r + |c|) ^ 2) *
            perimeterIn E (cylindricalTransition r a b)) := by gcongr
    _ = _ := by rw [add_mul, one_mul, mul_assoc]

end LiquidDrop
