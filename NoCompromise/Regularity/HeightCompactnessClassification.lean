import NoCompromise.Regularity.HeightCompactnessPhases
import NoCompromise.Regularity.ZeroExcess

/-! # Boundary points identify the cutting plane of a classified limit -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma volume_inter_zero_of_ae_empty
    {F U : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (he : F =ᵐ[volume.restrict U] (∅ : Set AmbientSpace)) : volume (F ∩ U) = 0 := by
  rw [← Measure.restrict_apply₀ (hmF.mono Measure.restrict_le_self)]
  exact (measure_congr he).trans (measure_empty)

lemma volume_compl_inter_zero_of_ae_full
    {F U : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (he : F =ᵐ[volume.restrict U] (univ : Set AmbientSpace)) : volume (Fᶜ ∩ U) = 0 := by
  apply volume_inter_zero_of_ae_empty hmF.compl
  filter_upwards [he] with x hx
  change (¬ x ∈ F) = False
  have hx' : (x ∈ F) = True := hx
  simp only [hx', not_true_eq_false]

theorem IsOmegaMinimal.limit_boundary_height_eq
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {x : ℕ → AmbientSpace} {a : AmbientSpace}
    (hx : ∀ j, x j ∈ frontier (densityOne (E j))) (ht : Tendsto x atTop (𝓝 a))
    {F U : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hU : IsOpen U) (ha : a ∈ U)
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ y in K,
        |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
        atTop (𝓝 0)) {c : ℝ}
    (he : F =ᵐ[volume.restrict U] {y : AmbientSpace | y 2 < c}) : a 2 = c := by
  apply le_antisymm
  · by_contra hle
    have hc : c < a 2 := lt_of_not_ge hle
    let V := U ∩ {y : AmbientSpace | c < y 2}
    have hV : IsOpen V := hU.inter (isOpen_lt continuous_const (by fun_prop))
    have hv := (IsOmegaMinimal.limit_two_phases hE hω hx ht hmF hV
      (show a ∈ V from ⟨ha, hc⟩)
      (fun K hK hKV => hl1 K hK (hKV.trans inter_subset_left))).1
    have hz : volume (F ∩ V) = 0 := by
      apply volume_inter_zero_of_ae_empty hmF
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left : V ⊆ U) he,
        ae_restrict_mem hV.measurableSet] with y hy hyV
      change (y ∈ F) = False
      change (y ∈ F) = (y 2 < c) at hy
      rw [hy]
      exact propext ⟨fun hh => (not_lt_of_ge hyV.2.le) hh, False.elim⟩
    exact (ne_of_gt hv) hz
  · by_contra hle
    have hc : a 2 < c := lt_of_not_ge hle
    let V := U ∩ {y : AmbientSpace | y 2 < c}
    have hV : IsOpen V := hU.inter (isOpen_lt (by fun_prop) continuous_const)
    have hv := (IsOmegaMinimal.limit_two_phases hE hω hx ht hmF hV
      (show a ∈ V from ⟨ha, hc⟩)
      (fun K hK hKV => hl1 K hK (hKV.trans inter_subset_left))).2
    have hz : volume (Fᶜ ∩ V) = 0 := by
      apply volume_compl_inter_zero_of_ae_full hmF
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left : V ⊆ U) he,
        ae_restrict_mem hV.measurableSet] with y hy hyV
      change (y ∈ F) = True
      change (y ∈ F) = (y 2 < c) at hy
      rw [hy]
      exact propext ⟨fun _ => trivial, fun _ => hyV.2⟩
    exact (ne_of_gt hv) hz

end LiquidDrop
