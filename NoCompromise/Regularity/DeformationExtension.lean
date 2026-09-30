module

public import NoCompromise.Regularity.SlabPhaseIdentification
public import NoCompromise.BV.FlatCutMeasure

@[expose] public section

/-! # Extending the vertical slices by the prescribed exterior phases -/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal
namespace LiquidDrop

/-- The vertical extension equals E between the caps, one below, and zero above. -/
def verticalPhaseExtension (E : Set AmbientSpace) (r : ℝ) : Set AmbientSpace :=
  {x | x 2 < -r} ∪ (E ∩ {x | -r ≤ x 2 ∧ x 2 < r})

lemma verticalPhaseExtension_mem_between {E : Set AmbientSpace} {r : ℝ} {x : AmbientSpace}
    (hx : -r ≤ x 2 ∧ x 2 < r) : x ∈ verticalPhaseExtension E r ↔ x ∈ E := by
  simp only [verticalPhaseExtension, mem_union, mem_inter_iff, mem_ofPred_eq,
    hx.1.not_gt, hx, and_true, false_or]

lemma verticalPhaseExtension_mem_lower {E : Set AmbientSpace} {r : ℝ} {x : AmbientSpace}
    (hx : x 2 < -r) : x ∈ verticalPhaseExtension E r := Or.inl hx

lemma verticalPhaseExtension_notMem_upper {E : Set AmbientSpace} {r : ℝ} (hr : 0 ≤ r)
    {x : AmbientSpace} (hx : r ≤ x 2) : x ∉ verticalPhaseExtension E r := by
  intro hh
  rcases hh with hh | ⟨_, hh⟩
  · change x 2 < -r at hh
    linarith
  · exact hh.2.not_ge hx

lemma nullMeasurableSet_verticalPhaseExtension {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (r : ℝ) :
    NullMeasurableSet (verticalPhaseExtension E r) volume := by
  have hz : Measurable (fun x : AmbientSpace => x 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).measurable
  exact (measurableSet_lt hz measurable_const).nullMeasurableSet.union
    (hmE.inter ((measurableSet_le measurable_const hz).inter
      (measurableSet_lt hz measurable_const)).nullMeasurableSet)

lemma indicator_verticalPhaseExtension {E : Set AmbientSpace} {r : ℝ} (hr : 0 ≤ r)
    (x : AmbientSpace) :
    (verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ)) x =
      ({z : AmbientSpace | z 2 < -r}.indicator (fun _ => (1 : ℝ))) x -
        (({z : AmbientSpace | z 2 < -r}.indicator (E.indicator (fun _ => (1 : ℝ)))) x -
          ({z : AmbientSpace | z 2 < r}.indicator (E.indicator (fun _ => (1 : ℝ)))) x) := by
  by_cases hlow : x 2 < -r
  · have hup : x 2 < r := by linarith
    simp [verticalPhaseExtension, hlow, hup]
  · by_cases hup : x 2 < r
    · have hbot : -r ≤ x 2 := le_of_not_gt hlow
      by_cases hxE : x ∈ E <;> simp [verticalPhaseExtension, hlow, hup, hbot, hxE]
    · simp [verticalPhaseExtension, hlow, hup]

/-- The extension has genuine globally local finite perimeter, obtained from
the proved flat BV cuts and their distributional trace formulas. -/
theorem hasLocallyFinitePerimeter_verticalPhaseExtension {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r : ℝ} (hr : 0 ≤ r) : HasLocallyFinitePerimeter (verticalPhaseExtension E r) := by
  have hc : IsLocallyBVOn (fun _ : AmbientSpace => (1 : ℝ)) univ := by
    refine ⟨(locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn univ, ?_⟩
    intro A _ _ _
    rw [variation_const_eq_zero]
    exact ENNReal.zero_lt_top
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hs := (hc.indicator_lowerHalfspace (-r)).sub_univ
    ((hf.indicator_lowerHalfspace (-r)).sub_univ (hf.indicator_lowerHalfspace r))
  have hlocal : IsLocallyBVOn ((verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ)))
      univ := by
    convert hs using 1
    ext x
    exact indicator_verticalPhaseExtension hr x
  intro A hA hcA
  exact hlocal.2 A hA hcA (subset_univ _)

end LiquidDrop
