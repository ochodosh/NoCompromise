module

public import NoCompromise.Regularity.HeightCompactnessPairing
public import NoCompromise.Regularity.ZeroExcessLocalPolar

@[expose] public section

/-! # Small-excess limits have a genuine positive constant polar measure

Positive measure compactness suffices here. The limiting measure need not be
identified with the actual perimeter before the halfspace classification.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop

theorem exists_small_excess_constant_polar_limit
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {U : Set AmbientSpace} (hbU : Bornology.IsBounded U) (ν : AmbientSpace)
    (he : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable U ν) atTop (𝓝 0))
    {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ μ : Measure AmbientSpace, μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧
      HasLocalConstantIndicatorPolar F U μ ν := by
  let M (j : ℕ) := canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable
  let : ∀ j, IsFiniteMeasureOnCompacts (M j) :=
    fun j => (canonicalPerimeterPolar (E j) (hE j).locallyFinite
      (hE j).nullMeasurable).finiteOnCompacts
  obtain ⟨μ, k, hk, hμ, hfin, hw⟩ := exists_subseq_positive_measure M (by
    intro K hK
    obtain ⟨C, hC, hb⟩ := bounded_perimeterMeasure_quasiminimal_sequence hE hω hK
    exact ⟨C.toReal, ENNReal.toReal_nonneg, fun j => ENNReal.toReal_mono hC.ne (hb j)⟩)
  refine ⟨μ, hμ, hfin, ?_⟩
  intro i φ hφ hs
  have hleft := (tendsto_indicator_coordinate_pairing_of_locally_l1 E
    (fun j => (hE j).nullMeasurable) hmF hl1 i φ hφ).comp hk.tendsto_atTop
  have hright := (hw φ).const_mul (-ν i)
  have herr := (tendsto_coordinate_pairing_error_of_excess hE hω hbU ν he i φ hφ hs).comp
    hk.tendsto_atTop
  have heq := tendsto_nhds_unique (hleft.sub hright) herr
  rw [integral_mul_const]
  simpa only [mul_comm] using sub_eq_zero.mp heq

end LiquidDrop
