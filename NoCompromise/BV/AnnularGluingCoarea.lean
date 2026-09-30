module

public import NoCompromise.BV.GoodTruncation

@[expose] public section

/-!
# Spherical trace mismatch and selection of gluing radii

Slicing the Borel density-one representatives gives exactly the volume of the
original symmetric difference in the annulus. The first-moment argument permits
any prescribed almost-everywhere condition on the selected radius.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma spherical_mismatch_coarea {E F : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (c : AmbientSpace) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (∫⁻ r in Ioo a b,
      hausdorffMeasure2 3 ((densityOne F ∆ densityOne E) ∩ sphere c r)) =
        volume ((F ∆ E) ∩ (ball c b \ closedBall c a)) := by
  rw [spherical_slicing_measurable
    ((measurableSet_densityOne hmF).symmDiff (measurableSet_densityOne hmE)) c ha b]
  have hs : {x : AmbientSpace | a < dist x c ∧ dist x c < b} =
      ball c b \ closedBall c a := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, and_comm]
  rw [hs]
  apply measure_congr
  exact ((densityOne_ae_eq (by norm_num : 0 < 3) hmF).symmDiff
    (densityOne_ae_eq (by norm_num : 0 < 3) hmE)).inter (EventuallyEq.rfl)

/-- One may avoid any null set of radii while obtaining the mean mismatch bound. -/
theorem exists_radius_spherical_mismatch_le {E F : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (c : AmbientSpace) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioo a b), P r) :
    ∃ r, r ∈ Ioo a b ∧ P r ∧
      hausdorffMeasure2 3 ((densityOne F ∆ densityOne E) ∩ sphere c r) ≤
        volume ((F ∆ E) ∩ (ball c b \ closedBall c a)) / ENNReal.ofReal (b - a) := by
  let μ : Measure ℝ := volume.restrict (Ioo a b)
  have hμ : μ ≠ 0 := by
    intro hz
    have : μ univ = 0 := by simp only [hz, Measure.coe_zero, Pi.zero_apply]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' (by
      simpa only [μ, Measure.restrict_apply_univ, Real.volume_Ioo] using this)
  have hg : ∀ᵐ r ∂μ, r ∈ Ioo a b ∧ P r :=
    (ae_restrict_mem measurableSet_Ioo).and hP
  obtain ⟨r, hr, hb⟩ := exists_notMem_null_le_laverage hμ
    ((measurable_sphere_sections
      ((measurableSet_densityOne hmF).symmDiff (measurableSet_densityOne hmE)) c).aemeasurable
        (μ := μ)) (ae_iff.mp hg)
  have hr' : r ∈ Ioo a b ∧ P r := by
    simpa only [mem_ofPred_eq, not_not] using hr
  refine ⟨r, hr'.1, hr'.2, ?_⟩
  simpa only [laverage_eq, μ, Measure.restrict_apply_univ, Real.volume_Ioo,
    spherical_mismatch_coarea hmE hmF c ha b] using hb

/-- In a fixed annulus, vanishing volume mismatch gives vanishing spherical
mismatch along selected radii satisfying any almost-everywhere requirements. -/
theorem exists_radii_spherical_mismatch_tendsto_zero
    {E F : ℕ → Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hmF : ∀ j, NullMeasurableSet (F j) volume)
    (c : AmbientSpace) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {P : ℕ → ℝ → Prop} (hP : ∀ j, ∀ᵐ r ∂volume.restrict (Ioo a b), P j r)
    (ht : Tendsto (fun j => volume ((F j ∆ E j) ∩ (ball c b \ closedBall c a)))
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ, (∀ j, r j ∈ Ioo a b ∧ P j (r j)) ∧
      Tendsto (fun j => hausdorffMeasure2 3
        ((densityOne (F j) ∆ densityOne (E j)) ∩ sphere c (r j))) atTop (𝓝 0) := by
  choose r hr hPr hb using fun j =>
    exists_radius_spherical_mismatch_le (hmE j) (hmF j) c ha hab (hP j)
  refine ⟨r, fun j => ⟨hr j, hPr j⟩, ?_⟩
  have hden : ENNReal.ofReal (b - a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hmean := ENNReal.Tendsto.div_const ht (Or.inr hden)
  simp only [ENNReal.zero_div] at hmean
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmean
    (fun _ => bot_le) hb

/-- The actual L¹ distance of two indicators is the symmetric-difference mass. -/
lemma eLpNorm_indicator_sub_eq_symmDiff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E F : Set α} (hmE : NullMeasurableSet E μ)
    (hmF : NullMeasurableSet F μ) :
    eLpNorm (E.indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ))) 1 μ =
      μ (E ∆ F) := by
  rw [eLpNorm_indicator_sub_indicator _ hmE hmF,
    eLpNorm_indicator_const₀ (hmE.symmDiff hmF) (by norm_num) (by norm_num)]
  simp

/-- A change of the target set on an annular null set does not alter the
indicator L¹ error that controls the chosen gluing sphere. -/
lemma volume_symmDiff_inter_eq_indicator_error {E F G A : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume) (hFG : F =ᵐ[volume.restrict A] G) :
    volume ((F ∆ E) ∩ A) =
      eLpNorm (E.indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ)))
        1 (volume.restrict A) := by
  rw [eLpNorm_indicator_sub_eq_symmDiff (hmE.mono Measure.restrict_le_self)
    (hmG.mono Measure.restrict_le_self)]
  rw [← Measure.restrict_apply₀
    ((hmF.symmDiff hmE).mono Measure.restrict_le_self)]
  apply measure_congr
  filter_upwards [hFG] with z hz
  change (z ∈ F ∆ E) = (z ∈ E ∆ G)
  change (z ∈ F) = (z ∈ G) at hz
  apply propext
  simp only [Set.mem_symmDiff, hz]
  tauto

end LiquidDrop
