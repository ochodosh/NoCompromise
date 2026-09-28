import NoCompromise.BV.CoareaLayerCake
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Measurability of superlevel perimeter

Strict-superlevel indicators are right-continuous in the level. Dominated convergence
makes every compact divergence pairing right-continuous, so their supremum is right
lower semicontinuous. Its strict superlevels are right-neighborhoods of all their
points and hence Borel sets. Almost-everywhere changes of the original function
preserve the perimeter at every level.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma continuousWithinAt_superlevelIndicator_right {α : Type*} (f : α → ℝ)
    (t : ℝ) (x : α) :
    ContinuousWithinAt (fun s => superlevelIndicator f s x) (Ioi t) t := by
  by_cases h : t < f x
  · apply tendsto_const_nhds.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with s hs
    have hs' : s < f x := hs
    simp [superlevelIndicator_apply, h, hs']
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have h' : ¬ s < f x := not_lt.mpr ((not_lt.mp h).trans (le_of_lt hs))
    simp [superlevelIndicator_apply, h, h']

lemma continuousWithinAt_integral_superlevel_mul_right {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Measurable f) (hg : Integrable g μ) (t : ℝ) :
    ContinuousWithinAt (fun s => ∫ x, superlevelIndicator f s x * g x ∂μ) (Ioi t) t := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖)
  · exact Eventually.of_forall fun s =>
      ((measurable_const.indicator (measurableSet_lt measurable_const hf)).aestronglyMeasurable.mul
        hg.aestronglyMeasurable)
  · exact Eventually.of_forall fun s => Eventually.of_forall fun x => by
      by_cases hs : s < f x <;> simp [superlevelIndicator_apply, hs]
  · exact hg.norm
  · exact Eventually.of_forall fun x =>
      (continuousWithinAt_superlevelIndicator_right f t x).mul_const (g x)

lemma lowerSemicontinuousWithinAt_perimeter_superlevel_right_of_measurable {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (t : ℝ) :
    LowerSemicontinuousWithinAt (fun s => perimeterIn {x | s < f x} U) (Ioi t) t := by
  unfold perimeterIn variation
  apply lowerSemicontinuousWithinAt_biSup
  intro X hX
  have hi := (integrable_divergenceN hX.1 hX.2.1).integrableOn (s := U)
  have hc := continuousWithinAt_integral_superlevel_mul_right hf hi t
  have hd := ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt hc
  exact hd.lowerSemicontinuousWithinAt

lemma measurable_perimeter_superlevel_of_measurable {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) : Measurable (fun s => perimeterIn {x | s < f x} U) := by
  apply measurable_of_Ioi
  intro a
  apply MeasurableSet.of_mem_nhdsGT
  intro t ht
  exact lowerSemicontinuousWithinAt_perimeter_superlevel_right_of_measurable U hf t a ht

/-- Almost-everywhere equal functions have identical perimeter at every level. -/
lemma perimeter_superlevel_congr_ae {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g) (t : ℝ) :
    perimeterIn {x | t < f x} U = perimeterIn {x | t < g x} U := by
  apply variation_congr_ae
  filter_upwards [hfg] with x hx
  simp only [indicator_apply, mem_ofPred_eq, hx]

lemma lowerSemicontinuousWithinAt_perimeter_superlevel_right {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f (volume.restrict U)) (t : ℝ) :
    LowerSemicontinuousWithinAt (fun s => perimeterIn {x | s < f x} U) (Ioi t) t := by
  have heq : (fun s => perimeterIn {x | s < f x} U) =
      (fun s => perimeterIn {x | s < hf.mk f x} U) := by
    funext s
    exact perimeter_superlevel_congr_ae U hf.ae_eq_mk s
  rw [heq]
  exact lowerSemicontinuousWithinAt_perimeter_superlevel_right_of_measurable U hf.measurable_mk t

/-- Perimeter of strict superlevels is Borel measurable in the level. -/
theorem measurable_perimeter_superlevel_of_aemeasurable {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f (volume.restrict U)) :
    Measurable (fun t => perimeterIn {x | t < f x} U) := by
  apply measurable_of_Ioi
  intro a
  apply MeasurableSet.of_mem_nhdsGT
  intro t ht
  exact lowerSemicontinuousWithinAt_perimeter_superlevel_right U hf t a ht

/-- The measurability needed by the BV coarea formula follows from local integrability. -/
theorem measurable_perimeter_superlevel {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) : Measurable (fun t => perimeterIn {x | t < f x} U) :=
  measurable_perimeter_superlevel_of_aemeasurable U hf.aestronglyMeasurable.aemeasurable

end LiquidDrop
