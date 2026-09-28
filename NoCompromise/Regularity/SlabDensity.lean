import NoCompromise.Regularity.RepresentativeDensity

/-! # An interior ball condition detects the phase at a boundary point -/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- If a region contains a ball of radius s/4 inside every small ball about x,
it cannot be empty of E almost everywhere when x has density one for E. -/
theorem not_densityOne_of_zero_phase_and_interior_balls
    {E U : Set AmbientSpace} (hmE : NullMeasurableSet E volume) (hU : MeasurableSet U)
    (hzero : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 0)
    {x : AmbientSpace} {δ : ℝ} (hδ : 0 < δ)
    (hballs : ∀ s : ℝ, 0 < s → s < δ →
      ∃ z : AmbientSpace, ball z (s / 4) ⊆ U ∩ ball x s) : x ∉ densityOne E := by
  intro hx
  have hz := (ae_restrict_iff' hU).mp hzero
  have hlower : ∀ s : ℝ, 0 < s → s < δ → (1 / 64 : ℝ) ≤ densityRatio Eᶜ x s := by
    intro s hs hsδ
    obtain ⟨z, hsub⟩ := hballs s hs hsδ
    have ha : ∀ᵐ y ∂volume, y ∈ ball z (s / 4) → y ∈ Eᶜ ∩ ball x s := by
      filter_upwards [hz] with y hy
      intro hyB
      refine ⟨?_, (hsub hyB).2⟩
      intro hyE
      have hh := hy (hsub hyB).1
      norm_num only [indicator_of_mem hyE] at hh
    have hm : volume (ball z (s / 4)) ≤ volume (Eᶜ ∩ ball x s) := measure_mono_ae ha
    have hfin : volume (Eᶜ ∩ ball x s) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
    have hr := ENNReal.toReal_mono hfin hm
    have hvol : 0 < (volume (ball x s)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume x hs).ne' measure_ball_lt_top.ne
    rw [densityRatio, le_div_iff₀ hvol]
    rw [volumeReal_ball_three x hs.le]
    rw [volumeReal_ball_three z (by positivity)] at hr
    calc
      _ = (4 * Real.pi / 3) * (s / 4) ^ 3 := by ring
      _ ≤ _ := hr
  have ht : Tendsto (fun s : ℝ => 1 - densityRatio E x s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  have hc : Tendsto (densityRatio Eᶜ x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (densityRatio_compl hmE x hs).symm
  have hlim : (1 / 64 : ℝ) ≤ 0 := ge_of_tendsto hc (by
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    exact hlower s hs.1 hs.2)
  norm_num at hlim

end LiquidDrop
