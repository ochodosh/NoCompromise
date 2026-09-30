module

public import NoCompromise.Regularity.DeformationOuterWallBands
public import NoCompromise.Regularity.DeformationOuterWallMeasure
public import NoCompromise.Regularity.Deformation

@[expose] public section

/-! # Outer-wall regularity for genuine phase-preserving deformations -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Any interior wall carrying no original perimeter also carries no perimeter
of a genuine local-L¹ compression limit. No rate of compression is assumed. -/
theorem IsSlabCapConfiguration.compression_limit_wall_zero
    {E F : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(compressionCompetitor E r σ τ (ε j) c).indicator (fun _ => (1 : ℝ)) x -
          F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0))
    {s : ℝ} (hs : s < r)
    (hzero : canonicalPerimeterMeasure E hE hmE
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0) :
    canonicalPerimeterMeasure F hF hmF
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0 := by
  let : IsFiniteMeasureOnCompacts (canonicalPerimeterMeasure E hE hmE) :=
    (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  apply measure_cylindrical_wall_zero_of_band_bound
    (canonicalPerimeterMeasure F hF hmF) (canonicalPerimeterMeasure E hE hmE) hs
    (C := 1 + ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
      ENNReal.ofReal ((r + |c|) ^ 2))
  · exact (ENNReal.add_lt_top.mpr ⟨by simp,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩).ne
  · intro a b hbr
    rw [canonicalPerimeterMeasure_open F hF hmF (isOpen_cylindricalTransition r a b),
      canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalTransition r a b)]
    exact h.compression_limit_band_mass_bound hmF hσ hst hε hε1 hconv hbr
  · exact hzero

/-- The genuine cylindrical deformation can be chosen with no perimeter on
its outer wall whenever that wall is regular for the original set. The exact
core/exterior representatives and cap phases are preserved. -/
theorem phase_preserving_cylindrical_deformation_with_outer_wall
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ < r)
    (hzero : canonicalPerimeterMeasure E hE hmE
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = τ ∧ |x 2| < r} = 0) :
    ∃ (F : Set AmbientSpace) (hF : HasLocallyFinitePerimeter F)
      (hmF : NullMeasurableSet F volume),
      (∀ x ∉ cylindricalCore r τ, x ∈ F ↔ x ∈ E) ∧
      (∀ x ∈ cylindricalCore r σ, x ∈ F ↔ x 2 < c) ∧
      hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityOne F) = 0 ∧
      hausdorffMeasure2 3 (cylindricalCap r r \ densityZero F) = 0 ∧
      perimeterIn F (cylindricalCore r τ) ≤
        perimeterIn E (cylindricalTransition r σ τ) + ENNReal.ofReal (Real.pi * σ ^ 2) +
          ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
            ∫⁻ x in standardCylinder r ∩ reducedBoundary E hE hmE,
              ENNReal.ofReal ((x 2 - c) ^ 2) ∂hausdorffMeasure2 3 ∧
      canonicalPerimeterMeasure F hF hmF
        {x : AmbientSpace | ‖graphProjectionN 2 x‖ = τ ∧ |x 2| < r} = 0 := by
  let ε : ℕ → ℝ := fun j => (1 / 2) ^ j
  have hε (j : ℕ) : 0 < ε j := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j
  have hε1 (j : ℕ) : ε j ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨F, hmF, hF, k, hk, hl1, hae⟩ :=
    h.exists_compressionCompetitor_subsequence_ae hσ hst hτr.le hε hε1
  have hepos (j : ℕ) := hε (k j)
  have hele (j : ℕ) := hε1 (k j)
  have helim := hεlim.comp hk.tendsto_atTop
  have hcore := h.compression_limit_core hσ hst (hst.le.trans hτr.le) hepos hele helim hae
  have hext := compression_limit_exterior hst hτr.le hae
  have hcaps := h.compression_limit_caps hσ hst hepos hele hae
  have hbound := h.compression_limit_perimeter_bound hF hmF.nullMeasurableSet
    hσ hst hτr.le hepos hele helim hae hl1
  have hwall := h.compression_limit_wall_zero hF hmF.nullMeasurableSet
    hσ hst hepos hele hl1 hτr hzero
  have hAB : cylindricalCore r σ ⊆ cylindricalCore r τ :=
    fun _ hx => ⟨hx.1.trans hst, hx.2⟩
  let H : Set AmbientSpace := {x | x 2 < c}
  let G := nestedPhaseRepresentative E F H (cylindricalCore r σ) (cylindricalCore r τ)
  obtain ⟨heq, hG, hmG, hGc, hGe⟩ := nestedPhaseRepresentative_properties
    (isOpen_cylindricalCore r σ).measurableSet (isOpen_cylindricalCore r τ).measurableSet
    hAB hF hmF.nullMeasurableSet (ae_eq_set_of_indicator_one_ae hcore)
      (ae_eq_set_of_indicator_one_ae hext)
  have hmeasure : canonicalPerimeterMeasure G hG hmG =
      canonicalPerimeterMeasure F hF hmF.nullMeasurableSet := by
    simpa only [Measure.restrict_univ] using
      canonicalPerimeterMeasure_restrict_eq_of_indicator_ae hG hmG hF hmF.nullMeasurableSet
        isOpen_univ (ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set heq))
  refine ⟨G, hG, hmG, hGe, hGc, ?_, ?_, ?_, ?_⟩
  · rw [densityOne_congr_ae heq]
    exact hcaps.1
  · rw [densityZero_congr_ae heq]
    exact hcaps.2
  · rw [perimeterIn_congr_ae _ (ae_restrict_of_ae heq)]
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
      Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet] at hbound
    exact hbound
  · rw [hmeasure]
    exact hwall

end LiquidDrop
