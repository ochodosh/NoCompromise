import NoCompromise.Regularity.DeformationCutBounds

/-! # Uniform local perimeter bounds for the actual strip replacement -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Patching two actual indicators across the two fixed cap planes has a
uniform local perimeter bound. The plane terms require no regular-height assumption. -/
theorem perimeterIn_replaceVerticalStrip_le {E G : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hG : HasLocallyFinitePerimeter G) (hmG : NullMeasurableSet G volume)
    {r : ℝ} (hr : 0 ≤ r) {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn (replaceVerticalStrip E G r) U ≤
      3 * perimeterIn E U + 2 * perimeterIn G U +
        2 * flatHyperplaneMeasure 2 (-r) U + 2 * flatHyperplaneMeasure 2 r U := by
  let f := E.indicator (fun _ => (1 : ℝ))
  let g := G.indicator (fun _ => (1 : ℝ))
  let cut := fun (v : AmbientSpace → ℝ) (a : ℝ) => {z : AmbientSpace | z 2 < a}.indicator v
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hg := hG.isLocallyBVOn_indicator hmG univ
  have hif : LocallyIntegrableOn f U := hf.1.mono_set (subset_univ U)
  have hfc (a : ℝ) : LocallyIntegrableOn (cut f a) U :=
    (hf.indicator_lowerHalfspace a).1.mono_set (subset_univ U)
  have hgc (a : ℝ) : LocallyIntegrableOn (cut g a) U :=
    (hg.indicator_lowerHalfspace a).1.mono_set (subset_univ U)
  have hb (A : Set AmbientSpace) (z : AmbientSpace) :
      ‖A.indicator (fun _ => (1 : ℝ)) z‖ ≤ 1 := by
    by_cases hz : z ∈ A <;> simp [hz]
  have hfb (a : ℝ) : variation (cut f a) U ≤
      perimeterIn E U + flatHyperplaneMeasure 2 a U := by
    simpa only [cut, f, show Fin.last 2 = (2 : Fin 3) from rfl,
      ENNReal.ofReal_one, one_mul, perimeterIn] using
      hf.variation_indicator_lowerHalfspace_le (hb E) a hU
  have hgb (a : ℝ) : variation (cut g a) U ≤
      perimeterIn G U + flatHyperplaneMeasure 2 a U := by
    simpa only [cut, g, show Fin.last 2 = (2 : Fin 3) from rfl,
      ENNReal.ofReal_one, one_mul, perimeterIn] using
      hg.variation_indicator_lowerHalfspace_le (hb G) a hU
  have hs : (replaceVerticalStrip E G r).indicator (fun _ => (1 : ℝ)) =
      fun z => f z - (cut f r z - cut f (-r) z) -
        (cut g (-r) z - cut g r z) := funext (indicator_replaceVerticalStrip hr)
  change variation _ U ≤ _
  rw [hs]
  calc
    _ ≤ (variation f U + (variation (cut f r) U + variation (cut f (-r)) U)) +
        (variation (cut g (-r)) U + variation (cut g r) U) :=
      (variation_sub_le_local (hif.sub ((hfc r).sub (hfc (-r))))
        ((hgc (-r)).sub (hgc r))).trans
        (add_le_add ((variation_sub_le_local hif ((hfc r).sub (hfc (-r)))).trans
          (add_le_add le_rfl (variation_sub_le_local (hfc r) (hfc (-r)))))
          (variation_sub_le_local (hgc (-r)) (hgc r)))
    _ ≤ (perimeterIn E U + ((perimeterIn E U + flatHyperplaneMeasure 2 r U) +
        (perimeterIn E U + flatHyperplaneMeasure 2 (-r) U))) +
        ((perimeterIn G U + flatHyperplaneMeasure 2 (-r) U) +
        (perimeterIn G U + flatHyperplaneMeasure 2 r U)) :=
      add_le_add (add_le_add le_rfl (add_le_add (hfb r) (hfb (-r))))
        (add_le_add (hgb (-r)) (hgb r))
    _ = _ := by ring

/-- The actual extension by the prescribed exterior phases has the same
kind of quantitative fixed-plane bound. -/
theorem perimeterIn_verticalPhaseExtension_le {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r : ℝ} (hr : 0 ≤ r) {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn (verticalPhaseExtension E r) U ≤
      2 * perimeterIn E U + 2 * flatHyperplaneMeasure 2 (-r) U +
        flatHyperplaneMeasure 2 r U := by
  let f := E.indicator (fun _ => (1 : ℝ))
  let cut := fun (v : AmbientSpace → ℝ) (a : ℝ) => {z : AmbientSpace | z 2 < a}.indicator v
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hc : IsLocallyBVOn (fun _ : AmbientSpace => (1 : ℝ)) univ := by
    refine ⟨(locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn univ, ?_⟩
    intro A _ _ _
    rw [variation_const_eq_zero]
    exact ENNReal.zero_lt_top
  have hic : LocallyIntegrableOn (cut (fun _ => 1) (-r)) U :=
    (hc.indicator_lowerHalfspace (-r)).1.mono_set (subset_univ U)
  have hfc (a : ℝ) : LocallyIntegrableOn (cut f a) U :=
    (hf.indicator_lowerHalfspace a).1.mono_set (subset_univ U)
  have hb : ∀ z, ‖E.indicator (fun _ => (1 : ℝ)) z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ E <;> simp [hz]
  have hfb (a : ℝ) : variation (cut f a) U ≤
      perimeterIn E U + flatHyperplaneMeasure 2 a U := by
    simpa only [cut, f, show Fin.last 2 = (2 : Fin 3) from rfl,
      ENNReal.ofReal_one, one_mul, perimeterIn] using
      hf.variation_indicator_lowerHalfspace_le hb a hU
  have hcb : variation (cut (fun _ => 1) (-r)) U ≤ flatHyperplaneMeasure 2 (-r) U := by
    simpa only [cut, show Fin.last 2 = (2 : Fin 3) from rfl, variation_const_eq_zero,
      ENNReal.ofReal_one, one_mul, zero_add] using
      hc.variation_indicator_lowerHalfspace_le (B := 1) (by intro z; norm_num) (-r) hU
  have hs : (verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ)) =
      fun z => cut (fun _ => 1) (-r) z - (cut f (-r) z - cut f r z) :=
    funext (indicator_verticalPhaseExtension hr)
  change variation _ U ≤ _
  rw [hs]
  calc
    _ ≤ variation (cut (fun _ => 1) (-r)) U +
        (variation (cut f (-r)) U + variation (cut f r) U) :=
      (variation_sub_le_local hic ((hfc (-r)).sub (hfc r))).trans
        (add_le_add le_rfl (variation_sub_le_local (hfc (-r)) (hfc r)))
    _ ≤ flatHyperplaneMeasure 2 (-r) U +
        ((perimeterIn E U + flatHyperplaneMeasure 2 (-r) U) +
        (perimeterIn E U + flatHyperplaneMeasure 2 r U)) :=
      add_le_add hcb (add_le_add (hfb (-r)) (hfb r))
    _ = _ := by ring

/-- The fixed plane area in any bounded region is finite. -/
lemma flatHyperplaneMeasure_lt_top_of_bounded {n : ℕ} (a : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : Bornology.IsBounded U) :
    flatHyperplaneMeasure n a U < ∞ :=
  (measure_mono subset_closure).trans_lt hU.isCompact_closure.measure_lt_top

/-- Uniform local input perimeter bounds give an explicit uniform bound for
all of the corresponding genuine strip competitors. -/
theorem perimeterIn_replaceVerticalStrip_uniform_bound
    {E G : ℕ → Set AmbientSpace}
    (hE : ∀ j, HasLocallyFinitePerimeter (E j))
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hG : ∀ j, HasLocallyFinitePerimeter (G j))
    (hmG : ∀ j, NullMeasurableSet (G j) volume)
    {r : ℝ} (hr : 0 ≤ r) {U : Set AmbientSpace}
    (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    {C D : ℝ≥0∞} (hC : C < ∞) (hD : D < ∞)
    (hbE : ∀ j, perimeterIn (E j) U ≤ C) (hbG : ∀ j, perimeterIn (G j) U ≤ D) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ j, perimeterIn (replaceVerticalStrip (E j) (G j) r) U ≤ B := by
  refine ⟨3 * C + 2 * D + 2 * flatHyperplaneMeasure 2 (-r) U +
    2 * flatHyperplaneMeasure 2 r U, ?_, ?_⟩
  · have hm := flatHyperplaneMeasure_lt_top_of_bounded (-r) hbU
    have hp := flatHyperplaneMeasure_lt_top_of_bounded r hbU
    finiteness
  · intro j
    exact (perimeterIn_replaceVerticalStrip_le (hE j) (hmE j) (hG j) (hmG j) hr hU).trans
      (by gcongr <;> first | exact hbE j | exact hbG j)

end LiquidDrop
