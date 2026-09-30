module

public import NoCompromise.Regularity.DeformationCompactnessSource
public import NoCompromise.Regularity.DeformationCutBoundsStrip
public import NoCompromise.BV.Compactness

@[expose] public section

/-! # Genuine local BV compactness of the compression competitors -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual competitors have an epsilon-independent local perimeter bound. -/
theorem IsSlabCapConfiguration.exists_uniform_compressionCompetitor_perimeter_bound
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {U : Set AmbientSpace} (hU : IsOpen U) (hbU : Bornology.IsBounded U) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      perimeterIn (compressionCompetitor E r σ τ ε c) U ≤ C := by
  obtain ⟨D, hD, hDb⟩ := h.exists_uniform_compressed_extension_perimeter_bound
    hσ hst hτr hU hbU
  refine ⟨3 * perimeterIn E U + 2 * D + 2 * flatHyperplaneMeasure 2 (-r) U +
    2 * flatHyperplaneMeasure 2 r U, ?_, ?_⟩
  · have hP := hE U hU hbU.isCompact_closure
    have hm := flatHyperplaneMeasure_lt_top_of_bounded (-r) hbU
    have hp := flatHyperplaneMeasure_lt_top_of_bounded r hbU
    finiteness
  · intro ε hε hε1
    have hExt := hasLocallyFinitePerimeter_verticalPhaseExtension hE hmE h.1.1.le
    have hmExt := nullMeasurableSet_verticalPhaseExtension hmE r
    let Φ := verticalCompressionHomeomorph (compressionBeta σ τ ε)
      (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c
    have hG := hasLocallyFinitePerimeter_verticalCompression hσ hst hε hε1 c
      (verticalPhaseExtension E r) hExt hmExt
    have hmG := nullMeasurableSet_image_of_differentiable
      ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
        one_ne_zero) Φ.injective hmExt
    exact (perimeterIn_replaceVerticalStrip_le hE hmE hG hmG h.1.1.le hU).trans
      (by gcongr; exact hDb ε hε hε1)

/-- Compactness for the genuine compression competitors, with actual local L¹
convergence and a measurable locally finite-perimeter limit. -/
theorem IsSlabCapConfiguration.exists_compressionCompetitor_subsequence
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧
        ∀ K : Set AmbientSpace, IsCompact K →
          Tendsto (fun j => ∫ x in K,
            |(compressionCompetitor E r σ τ (ε (k j)) c).indicator (fun _ => (1 : ℝ)) x -
              F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0) := by
  let C (j : ℕ) := compressionCompetitor E r σ τ (ε j) c
  have hp (j : ℕ) := compressionCompetitor_locallyFinitePerimeter hE hmE h.1.1.le
    hσ hst (hε j) (hε1 j) c
  apply bv_compactness_indicators_univ C (fun j => (hp j).1) (fun j => (hp j).2)
  intro A hA hcA
  obtain ⟨B, hB, hb⟩ := h.exists_uniform_compressionCompetitor_perimeter_bound
    hσ hst hτr hA (hcA.isBounded.subset subset_closure)
  refine ⟨volume.real A + B.toReal, fun j => ?_⟩
  have hfin : volume A ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt hcA.measure_lt_top).ne
  have hi : IntegrableOn ((C j).indicator (fun _ => (1 : ℝ))) A :=
    ((locallyIntegrable_indicator_one (hp j).2).integrableOn_isCompact hcA).mono_set subset_closure
  have hn : (∫ x in A, |(C j).indicator (fun _ => (1 : ℝ)) x|) ≤ volume.real A := by
    have hh := integral_mono hi.norm (integrableOn_const hfin (C := (1 : ℝ)))
      (fun x => by by_cases hx : x ∈ C j <;> simp [hx])
    simpa only [Real.norm_eq_abs, setIntegral_const, smul_eq_mul, mul_one] using hh
  exact add_le_add hn (ENNReal.toReal_mono hB.ne (hb (ε j) (hε j) (hε1 j)))

end LiquidDrop
