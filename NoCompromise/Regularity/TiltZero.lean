import NoCompromise.Regularity.Excess
import NoCompromise.Regularity.OmegaMinimal

/-! # The zero-excess case of tilt improvement -/

noncomputable section
open Set MeasureTheory Metric
namespace LiquidDrop

lemma cylindricalExcess_zero_of_unit_zero (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) {r : ℝ} (hr1 : r ≤ 1)
    (hz : cylindricalExcess E hE hmE 0 1 ν = 0) :
    cylindricalExcess E hE hmE 0 r ν = 0 := by
  have hsub : cylinder 0 r ν ⊆ cylinder 0 1 ν := fun _ hx =>
    ⟨hx.1.trans_le hr1, hx.2.trans_le hr1⟩
  have he : normalExcessIntegral E hE hmE (cylinder 0 1 ν) ν = 0 := by
    simpa only [cylindricalExcess, one_pow, div_one] using hz
  have hi := normalExcessIntegral_mono E hE hmE (isBounded_cylinder 0 1 hν) hsub ν
  have hz' : normalExcessIntegral E hE hmE (cylinder 0 r ν) ν = 0 :=
    le_antisymm (he ▸ hi) (normalExcessIntegral_nonneg E hE hmE _ _)
  simp only [cylindricalExcess, hz', zero_div]

lemma IsOmegaMinimal.excess_zero_of_sum_zero
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hz : cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1 ν + ω = 0)
    {r : ℝ} (hr1 : r ≤ 1) :
    ω = 0 ∧ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r ν = 0 := by
  have hn : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1 ν := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable (cylinder 0 1 ν) ν
  have he : cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1 ν = 0 := by
    linarith [hE.nonneg]
  exact ⟨by linarith, cylindricalExcess_zero_of_unit_zero E hE.locallyFinite
    hE.nullMeasurable hν hr1 he⟩

end LiquidDrop
