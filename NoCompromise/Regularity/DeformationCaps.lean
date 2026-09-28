import NoCompromise.Regularity.DeformationDensity
import NoCompromise.Regularity.DeformationClearance

/-! # The actual density representatives on both caps are preserved -/

noncomputable section
open Set MeasureTheory Filter Metric
namespace LiquidDrop

lemma ae_eq_set_of_indicator_one_ae {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    (h : E.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] F.indicator (fun _ => (1 : ℝ))) :
    E =ᵐ[μ] F := by
  filter_upwards [h] with x hx
  change (x ∈ E) = (x ∈ F)
  by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp_all

theorem IsSlabCapConfiguration.compression_cap_densities
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ x ∈ cylindricalCap r (-r),
      x ∈ densityOne (compressionCompetitor E r σ τ ε c) ↔ x ∈ densityOne E) ∧
    (∀ x ∈ cylindricalCap r r,
      x ∈ densityZero (compressionCompetitor E r σ τ ε c) ↔ x ∈ densityZero E) := by
  obtain ⟨hL, hU⟩ := h.compression_agrees_on_cap_columns hσ hst hε hε1
  have hl := ae_eq_set_of_indicator_one_ae hL
  have hu := ae_eq_set_of_indicator_one_ae hU
  have hgapL : -r < c - η * r := by linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by linarith [le_abs_self c, h.1.2.2.2.1]
  constructor
  · rintro x ⟨p, hp, rfl⟩
    apply densityOne_mem_iff_of_ae_on_open (isOpen_lowerPhaseColumn r (c - η * r)) _ hl
    exact ⟨by simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp,
      by simpa only [graphAppendN_height_three] using hgapL⟩
  · rintro x ⟨p, hp, rfl⟩
    apply densityZero_mem_iff_of_ae_on_open (isOpen_upperPhaseColumn r (c + η * r)) _ hu
    exact ⟨by simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp,
      by simpa only [graphAppendN_height_three] using hgapU⟩

theorem IsSlabCapConfiguration.compression_cap_conditions
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    hausdorffMeasure2 3
      (cylindricalCap r (-r) \ densityOne (compressionCompetitor E r σ τ ε c)) = 0 ∧
    hausdorffMeasure2 3
      (cylindricalCap r r \ densityZero (compressionCompetitor E r σ τ ε c)) = 0 := by
  obtain ⟨hl, hu⟩ := h.compression_cap_densities hσ hst hε hε1
  constructor
  · apply measure_mono_null _ h.2.1
    intro x hx
    exact ⟨hx.1, fun hh => hx.2 ((hl x hx.1).mpr hh)⟩
  · apply measure_mono_null _ h.2.2
    intro x hx
    exact ⟨hx.1, fun hh => hx.2 ((hu x hx.1).mpr hh)⟩

end LiquidDrop
