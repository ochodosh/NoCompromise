module

public import NoCompromise.Regularity.HeightCompactnessDensity

@[expose] public section

/-! # Both phases survive at limits of quasiminimal boundary points -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma IsOmegaMinimal.limit_phase_volume_pos_open
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {x : ℕ → AmbientSpace} {a : AmbientSpace}
    (hx : ∀ j, x j ∈ frontier (densityOne (E j))) (ht : Tendsto x atTop (𝓝 a))
    {F U : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hU : IsOpen U) (ha : a ∈ U)
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ y in K,
        |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
        atTop (𝓝 0)) :
    0 < volume (F ∩ U) := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU a ha
  let ρ := min (R / 4) (1 / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hρR : ρ ≤ R / 4 := min_le_left _ _
  have hsub : closedBall a (2 * ρ) ⊆ U := by
    intro y hy
    apply hRU
    rw [mem_ball]
    have hy' := mem_closedBall.mp hy
    linarith
  exact (IsOmegaMinimal.limit_phase_volume_pos hE hω hx ht hmF hρ hρ1
    (hl1 _ (isCompact_closedBall _ _) hsub)).trans_le
      (measure_mono (inter_subset_inter_right _ hsub))

/-- Any open neighborhood of a limit of boundary points contains positive
volume of both actual limiting phases. This excludes either constant phase. -/
theorem IsOmegaMinimal.limit_two_phases
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {x : ℕ → AmbientSpace} {a : AmbientSpace}
    (hx : ∀ j, x j ∈ frontier (densityOne (E j))) (ht : Tendsto x atTop (𝓝 a))
    {F U : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hU : IsOpen U) (ha : a ∈ U)
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ y in K,
        |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
        atTop (𝓝 0)) :
    0 < volume (F ∩ U) ∧ 0 < volume (Fᶜ ∩ U) := by
  refine ⟨IsOmegaMinimal.limit_phase_volume_pos_open hE hω hx ht hmF hU ha hl1, ?_⟩
  refine IsOmegaMinimal.limit_phase_volume_pos_open (fun j => (hE j).compl) hω
    (x := x) (a := a) ?_ ht hmF.compl hU ha ?_
  · intro j
    rw [(hE j).compl.frontier_densityOne, essentialBoundary_compl (hE j).nullMeasurable,
      ← (hE j).frontier_densityOne]
    exact hx j
  · intro K hK hKU
    simpa only [abs_indicator_compl_sub] using hl1 K hK hKU

end LiquidDrop
