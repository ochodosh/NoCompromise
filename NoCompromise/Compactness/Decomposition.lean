module

public import NoCompromise.Compactness.PerimeterSplitting
public import NoCompromise.Compactness.Radii
public import NoCompromise.Compactness.CoulombSplitting

@[expose] public section

/-!
# Concentration-compactness decomposition (blueprint chapter 19)

Blueprint `thm:decomposition`, assembled from `lem:radii-construction`
(`Compactness/Radii.lean`), `lem:perimeter-splitting` (`Compactness/PerimeterSplitting.lean`)
and `lem:coulomb-splitting` (`Compactness/CoulombSplitting.lean`).

"The situation of `thm:compactness`" is abstracted to its output: a sequence `E n` of
null-measurable sets of locally finite perimeter with `|E n| ≤ C`, `Per(E n) ≤ C`, converging
in `L¹_loc` to a null-measurable set `F` with `|F| ≤ C` (the limit is called `F` in Lean,
`E` in the blueprint). With `F_n := E n ∩ ball 0 (R n)` and `G_n := E n \ ball 0 (R n)`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LiquidDrop

/-- Blueprint `thm:decomposition`, the one-profile decomposition. -/
theorem decomposition {C : ℝ}
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hE : ∀ n, HasLocallyFinitePerimeter (E n)) (hmE : ∀ n, NullMeasurableSet (E n) volume)
    (hmF : NullMeasurableSet F volume)
    (hvol : ∀ n, volume (E n) ≤ ENNReal.ofReal C) (hFvol : volume F ≤ ENNReal.ofReal C)
    (hper : ∀ n, perimeter (E n) ≤ ENNReal.ofReal C)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun n => ∫ x in K,
        |(E n).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
      (∀ n, IsGoodRadius (E n) (hE n) (hmE n) 0 (R n)) ∧
      -- eq:decomp-conv
      Tendsto (fun n => (volume (symmDiff (E n ∩ ball 0 (R n)) F)).toReal) atTop (𝓝 0) ∧
      (∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun n => ∫ x in K,
          (E n \ ball 0 (R n)).indicator (fun _ => (1 : ℝ)) x) atTop (𝓝 0)) ∧
      -- eq:decomp-volumes
      Tendsto (fun n => (volume (E n ∩ ball 0 (R n))).toReal) atTop (𝓝 (volume F).toReal) ∧
      (∀ n, volume (E n \ ball 0 (R n)) + volume (E n ∩ ball 0 (R n)) = volume (E n)) ∧
      -- eq:decomp-perimeter
      (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n,
        (perimeter F).toReal + (perimeter (E n \ ball 0 (R n))).toReal + ε n
          ≤ (perimeter (E n)).toReal) ∧
      -- eq:decomp-coulomb
      (∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ n,
        (coulombEnergy (E n)).toReal
          = (coulombEnergy F).toReal + (coulombEnergy (E n \ ball 0 (R n))).toReal + δ n) := by
  have hFfin : volume F ≠ ∞ := (hFvol.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨N, k, R, -, -, hgood, -, -, hRtop, ha, hsymm, hvolF, hG⟩ :=
    radii_construction E F hE hmE hmF hFfin hconv
  -- the Coulomb lemma is stated for a nonnegative bound
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hle : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hvol' : ∀ n, volume (E n) ≤ ENNReal.ofReal C' := fun n => (hvol n).trans hle
  have hFvol' : volume F ≤ ENNReal.ofReal C' := hFvol.trans hle
  refine ⟨R, hRtop, hgood, ?_, hG, ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
  · exact (ENNReal.tendsto_toReal hFfin).comp hvolF
  · intro n
    exact measure_sdiff_add_inter (E n) measurableSet_ball
  · exact (perimeter_splitting E F hE hmE hmF hper R hgood ha hsymm).2
  · exact coulomb_splitting hC'0 E F hmE hmF hvol' hFvol' R hRtop hsymm

end LiquidDrop
