module

public import NoCompromise.Regularity.DeformationExtension

@[expose] public section

/-! # Replacing a vertical strip by a locally finite-perimeter set -/

noncomputable section
open Set MeasureTheory
namespace LiquidDrop

def replaceVerticalStrip (E G : Set AmbientSpace) (r : ℝ) : Set AmbientSpace :=
  (E \ {x | -r ≤ x 2 ∧ x 2 < r}) ∪ (G ∩ {x | -r ≤ x 2 ∧ x 2 < r})

lemma replaceVerticalStrip_mem_between {E G : Set AmbientSpace} {r : ℝ} {x : AmbientSpace}
    (hx : -r ≤ x 2 ∧ x 2 < r) : x ∈ replaceVerticalStrip E G r ↔ x ∈ G := by
  simp [replaceVerticalStrip, hx]

lemma replaceVerticalStrip_mem_outside {E G : Set AmbientSpace} {r : ℝ} {x : AmbientSpace}
    (hx : ¬ (-r ≤ x 2 ∧ x 2 < r)) : x ∈ replaceVerticalStrip E G r ↔ x ∈ E := by
  simp [replaceVerticalStrip, hx]

lemma nullMeasurableSet_replaceVerticalStrip {E G : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hmG : NullMeasurableSet G volume) (r : ℝ) :
    NullMeasurableSet (replaceVerticalStrip E G r) volume := by
  have hz : Measurable (fun x : AmbientSpace => x 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).measurable
  have hS : NullMeasurableSet {x : AmbientSpace | -r ≤ x 2 ∧ x 2 < r} volume :=
    ((measurableSet_le measurable_const hz).inter
    (measurableSet_lt hz measurable_const)).nullMeasurableSet
  exact (hmE.diff hS).union (hmG.inter hS)

lemma indicator_replaceVerticalStrip {E G : Set AmbientSpace} {r : ℝ} (hr : 0 ≤ r)
    (x : AmbientSpace) :
    (replaceVerticalStrip E G r).indicator (fun _ => (1 : ℝ)) x =
      E.indicator (fun _ => (1 : ℝ)) x -
        ({z : AmbientSpace | z 2 < r}.indicator (E.indicator (fun _ => (1 : ℝ))) x -
          {z : AmbientSpace | z 2 < -r}.indicator (E.indicator (fun _ => (1 : ℝ))) x) -
        ({z : AmbientSpace | z 2 < -r}.indicator (G.indicator (fun _ => (1 : ℝ))) x -
          {z : AmbientSpace | z 2 < r}.indicator (G.indicator (fun _ => (1 : ℝ))) x) := by
  by_cases hlow : x 2 < -r
  · have hup : x 2 < r := by linarith
    by_cases hxE : x ∈ E <;> by_cases hxG : x ∈ G <;>
      simp [replaceVerticalStrip, hlow, hup, hlow.not_ge, hxE, hxG]
  · by_cases hup : x 2 < r
    · have hbot : -r ≤ x 2 := le_of_not_gt hlow
      by_cases hxE : x ∈ E <;> by_cases hxG : x ∈ G <;>
        simp [replaceVerticalStrip, hlow, hup, hbot, hxE, hxG]
    · by_cases hxE : x ∈ E <;> by_cases hxG : x ∈ G <;>
        simp [replaceVerticalStrip, hlow, hup, hxE, hxG]

/-- Cutting at the two fixed planes and subtracting the actual BV cuts yields
local finite perimeter; no regular-radius assumption is used here. -/
theorem hasLocallyFinitePerimeter_replaceVerticalStrip {E G : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hG : HasLocallyFinitePerimeter G) (hmG : NullMeasurableSet G volume)
    {r : ℝ} (hr : 0 ≤ r) : HasLocallyFinitePerimeter (replaceVerticalStrip E G r) := by
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hg := hG.isLocallyBVOn_indicator hmG univ
  have hs := (hf.sub_univ
    ((hf.indicator_lowerHalfspace r).sub_univ (hf.indicator_lowerHalfspace (-r)))).sub_univ
    ((hg.indicator_lowerHalfspace (-r)).sub_univ (hg.indicator_lowerHalfspace r))
  have hlocal : IsLocallyBVOn ((replaceVerticalStrip E G r).indicator (fun _ => (1 : ℝ)))
      univ := by
    convert hs using 1
    ext x
    exact indicator_replaceVerticalStrip hr x
  intro A hA hcA
  exact hlocal.2 A hA hcA (subset_univ _)

end LiquidDrop
