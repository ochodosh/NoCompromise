module

public import NoCompromise.Regularity.DeformationCompactnessPointwise
public import NoCompromise.Regularity.DeformationEstimate
public import NoCompromise.Regularity.DeformationRepresentative

@[expose] public section

/-! # Phase-preserving cylindrical deformation

The full blueprint theorem holds with C = π², at arbitrary scale and for all
0 < σ < τ ≤ r. The limit is chosen with exact core and exterior representatives.
The construction compresses the core along with the annulus, then identifies
its halfspace limit. Its inner wall has zero perimeter by the genuine phase
envelope and the proved zero area of a horizontal circle.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace LiquidDrop

lemma cylindricalCore_eq_base_height {r s : ℝ} (hsr : s ≤ r) :
    cylindricalCore r s = {x : AmbientSpace | ‖graphProjectionN 2 x‖ < s ∧ |x 2| < r} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.2⟩
  · intro hx
    exact ⟨hx.1, hx.1.trans_le hsr, hx.2⟩

lemma cylindricalTransition_eq_base_height {r σ τ : ℝ} (hτr : τ ≤ r) :
    cylindricalTransition r σ τ =
      {x : AmbientSpace | σ < ‖graphProjectionN 2 x‖ ∧
        ‖graphProjectionN 2 x‖ < τ ∧ |x 2| < r} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.1.2, hx.2.2⟩
  · intro hx
    exact ⟨⟨hx.1, hx.2.1⟩, hx.2.1.trans_le hτr, hx.2.2⟩

/-- Full blueprint `thm:deformation`, with the universal constant π². The
conclusion is stronger: no regular-radius premise or special radius interval
is required, and the result holds at every scale. -/
theorem phase_preserving_cylindrical_deformation
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r) :
    ∃ F : Set AmbientSpace, HasLocallyFinitePerimeter F ∧ NullMeasurableSet F volume ∧
      (∀ x ∉ cylindricalCore r τ, x ∈ F ↔ x ∈ E) ∧
      (∀ x ∈ cylindricalCore r σ, x ∈ F ↔ x 2 < c) ∧
      hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityOne F) = 0 ∧
      hausdorffMeasure2 3 (cylindricalCap r r \ densityZero F) = 0 ∧
      perimeterIn F (cylindricalCore r τ) ≤
        perimeterIn E (cylindricalTransition r σ τ) + ENNReal.ofReal (Real.pi * σ ^ 2) +
          ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
            ∫⁻ x in standardCylinder r ∩ reducedBoundary E hE hmE,
              ENNReal.ofReal ((x 2 - c) ^ 2) ∂hausdorffMeasure2 3 := by
  let ε : ℕ → ℝ := fun j => (1 / 2) ^ j
  have hε (j : ℕ) : 0 < ε j := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j
  have hε1 (j : ℕ) : ε j ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨F, hmF, hF, k, hk, hl1, hae⟩ :=
    h.exists_compressionCompetitor_subsequence_ae hσ hst hτr hε hε1
  have hepos (j : ℕ) := hε (k j)
  have hele (j : ℕ) := hε1 (k j)
  have helim := hεlim.comp hk.tendsto_atTop
  have hcore := h.compression_limit_core hσ hst (hst.le.trans hτr) hepos hele helim hae
  have hext := compression_limit_exterior hst hτr hae
  have hcaps := h.compression_limit_caps hσ hst hepos hele hae
  have hbound := h.compression_limit_perimeter_bound hF hmF.nullMeasurableSet
    hσ hst hτr hepos hele helim hae hl1
  have hAB : cylindricalCore r σ ⊆ cylindricalCore r τ :=
    fun _ hx => ⟨hx.1.trans hst, hx.2⟩
  let H : Set AmbientSpace := {x | x 2 < c}
  let G := nestedPhaseRepresentative E F H (cylindricalCore r σ) (cylindricalCore r τ)
  obtain ⟨heq, hG, hmG, hGc, hGe⟩ := nestedPhaseRepresentative_properties
    (isOpen_cylindricalCore r σ).measurableSet (isOpen_cylindricalCore r τ).measurableSet
    hAB hF hmF.nullMeasurableSet (ae_eq_set_of_indicator_one_ae hcore)
      (ae_eq_set_of_indicator_one_ae hext)
  refine ⟨G, hG, hmG, hGe, hGc, ?_, ?_, ?_⟩
  · rw [densityOne_congr_ae heq]
    exact hcaps.1
  · rw [densityZero_congr_ae heq]
    exact hcaps.2
  · rw [perimeterIn_congr_ae _ (ae_restrict_of_ae heq)]
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
      Measure.restrict_restrict (isOpen_standardCylinder r).measurableSet] at hbound
    exact hbound

end LiquidDrop
