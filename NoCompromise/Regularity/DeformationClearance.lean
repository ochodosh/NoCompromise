import NoCompromise.Regularity.DeformationCore

/-! # The compressed competitors preserve fixed neighborhoods of both caps -/

noncomputable section
open Set MeasureTheory Filter Metric
namespace LiquidDrop

lemma compressionCompetitor_indicator_outside_height (E : Set AmbientSpace) (r σ τ ε c : ℝ)
    {x : AmbientSpace} (hx : ¬ (-r ≤ x 2 ∧ x 2 < r)) :
    (compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ)) x =
      E.indicator (fun _ => (1 : ℝ)) x := by
  have he := compressionCompetitor_mem_outside_height (E := E) (σ := σ) (τ := τ)
    (ε := ε) (c := c) hx
  by_cases hxE : x ∈ E
  · rw [indicator_of_mem (he.mpr hxE), indicator_of_mem hxE]
  · rw [indicator_of_notMem (mt he.mp hxE), indicator_of_notMem hxE]

lemma compressionCompetitor_indicator_outside_base (E : Set AmbientSpace) (r σ τ ε c : ℝ)
    (hst : σ < τ) {x : AmbientSpace} (hx : τ ≤ ‖graphProjectionN 2 x‖) :
    (compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ)) x =
      E.indicator (fun _ => (1 : ℝ)) x := by
  have he := compressionCompetitor_mem_outside_base (E := E) (r := r) (ε := ε) (c := c) hst hx
  by_cases hxE : x ∈ E
  · rw [indicator_of_mem (he.mpr hxE), indicator_of_mem hxE]
  · rw [indicator_of_notMem (mt he.mp hxE), indicator_of_notMem hxE]

/-- The cap collars are independent of epsilon, and agreement is with the
original set on both sides of each cap plane. -/
theorem IsSlabCapConfiguration.compression_agrees_on_cap_columns
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ))
      =ᵐ[volume.restrict (lowerPhaseColumn r (c - η * r))]
        E.indicator (fun _ => (1 : ℝ))) ∧
    ((compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ))
      =ᵐ[volume.restrict (upperPhaseColumn r (c + η * r))]
        E.indicator (fun _ => (1 : ℝ))) := by
  obtain ⟨hl, hu⟩ := h.phases_off_slab
  have hl' := (ae_restrict_iff' (isOpen_lowerSlabRegion r c η).measurableSet).mp hl
  have hu' := (ae_restrict_iff' (isOpen_upperSlabRegion r c η).measurableSet).mp hu
  have hcomp := h.compressed_extension_phases hσ hst hε hε1
  have hηr : 0 < η * r := mul_pos h.1.2.1 h.1.1
  have hgapL : -r < c - η * r := by linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by linarith [le_abs_self c, h.1.2.2.2.1]
  have hplane : ∀ᵐ x : AmbientSpace ∂volume, x 2 ≠ -r := by
    have hh := (measure_eq_zero_iff_ae_notMem).mp (volume_flatHyperplane 2 (-r))
    simpa only [mem_ofPred_eq, show (Fin.last 2 : Fin 3) = 2 from rfl] using hh
  constructor
  · apply (ae_restrict_iff' (isOpen_lowerPhaseColumn r (c - η * r)).measurableSet).mpr
    filter_upwards [hl', hcomp, hplane] with x hx hc hxp
    intro hxcol
    by_cases hstrip : -r ≤ x 2 ∧ x 2 < r
    · rw [compressionCompetitor_indicator_between E r σ τ ε c hstrip]
      have hxreg : x ∈ lowerSlabRegion r c η :=
        ⟨by simpa only [mem_preimage, mem_ball, dist_zero_right] using hxcol.1,
          lt_of_le_of_ne hstrip.1 (Ne.symm hxp), hxcol.2⟩
      rw [hx hxreg]
      apply hc.1 hxcol.1
      have hb := (compressionBeta_bounds σ τ hε.le hε1 (graphProjectionN 2 x)).2
      nlinarith [hxcol.2]
    · exact compressionCompetitor_indicator_outside_height E r σ τ ε c hstrip
  · apply (ae_restrict_iff' (isOpen_upperPhaseColumn r (c + η * r)).measurableSet).mpr
    filter_upwards [hu', hcomp] with x hx hc
    intro hxcol
    by_cases hstrip : -r ≤ x 2 ∧ x 2 < r
    · rw [compressionCompetitor_indicator_between E r σ τ ε c hstrip]
      have hxreg : x ∈ upperSlabRegion r c η :=
        ⟨by simpa only [mem_preimage, mem_ball, dist_zero_right] using hxcol.1,
          hxcol.2, hstrip.2⟩
      rw [hx hxreg]
      apply hc.2 hxcol.1
      have hb := (compressionBeta_bounds σ τ hε.le hε1 (graphProjectionN 2 x)).2
      nlinarith [hxcol.2]
    · exact compressionCompetitor_indicator_outside_height E r σ τ ε c hstrip

end LiquidDrop
