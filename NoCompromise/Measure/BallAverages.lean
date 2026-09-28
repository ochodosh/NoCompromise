import NoCompromise.Sobolev.MaximalMeasurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.IsLUB

/-!
# Measurability and radial left continuity of ball averages

The measure need not be doubling. Open balls are used throughout, including
at radii where the boundary sphere has positive mass.
-/

noncomputable section
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The integral of a Borel vector field on a fixed-radius open ball is Borel
as a function of the center. No integrability assumption is needed. -/
theorem measurable_integral_ball {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Measurable f) (r : ℝ) :
    Measurable (fun x => ∫ y in ball x r, f y ∂μ) := by
  let T : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | dist p.2 p.1 < r}
  have hT : MeasurableSet T := measurableSet_lt (measurable_snd.dist measurable_fst)
    measurable_const
  have hF : StronglyMeasurable (T.indicator (fun p => f p.2)) :=
    ((hf.comp measurable_snd).indicator hT).stronglyMeasurable
  have h := (hF.integral_prod_right' (ν := μ)).measurable
  convert h using 1
  funext x
  rw [← integral_indicator measurableSet_ball]
  rfl

theorem measurable_average_ball {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Measurable f) (r : ℝ) :
    Measurable (fun x => ⨍ y in ball x r, f y ∂μ) := by
  simp only [setAverage_eq, measureReal_def]
  exact (lowerSemicontinuous_measure_ball μ r).measurable.ennreal_toReal.inv.smul
    (measurable_integral_ball μ hf r)

/-- At a fixed positive radius, integrals over open balls are continuous
from the left. Boundary atoms are included in the proof, not discarded. -/
theorem continuousWithinAt_integral_ball_radius {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (hf : Measurable f)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hi : IntegrableOn f (ball x r) μ) :
    ContinuousWithinAt (fun s => ∫ y in ball x s, f y ∂μ) (Iic r) r := by
  simp only [ContinuousWithinAt, ← integral_indicator measurableSet_ball]
  apply tendsto_integral_filter_of_dominated_convergence ((ball x r).indicator (fun y => ‖f y‖))
  · exact Eventually.of_forall fun s => (hf.indicator measurableSet_ball).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ ball x s
      · have hyr : y ∈ ball x r := ball_subset_ball hs hy
        simp only [indicator_of_mem hy, indicator_of_mem hyr, le_refl]
      · simp only [indicator_of_notMem hy, norm_zero]
        exact indicator_nonneg (fun _ _ => norm_nonneg _) _
  · exact (integrable_indicator_iff measurableSet_ball).mpr hi.norm
  · exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ ball x r
      · have hev : ∀ᶠ s in 𝓝[Iic r] r, dist y x < s :=
          (eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds
        apply tendsto_const_nhds.congr'
        filter_upwards [hev] with s hs
        simp only [indicator_of_mem hy, indicator_of_mem (show y ∈ ball x s from hs)]
      · apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hys : y ∉ ball x s := fun h => hy (ball_subset_ball hs h)
        simp only [indicator_of_notMem hy, indicator_of_notMem hys]

/-- A unit-length scalar test identifies radial continuity of ball mass. -/
theorem continuousWithinAt_measureReal_ball_radius {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hfin : μ (ball x r) ≠ ∞) :
    ContinuousWithinAt (fun s => μ.real (ball x s)) (Iic r) r := by
  let e := EuclideanSpace.single (ι := Fin 1) (𝕜 := ℝ) 0 1
  have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => e) (ball x r) μ :=
    integrableOn_const hfin
  have h := continuousWithinAt_integral_ball_radius μ measurable_const x r hi
  have hcoord := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).continuous.continuousAt
    |>.comp_continuousWithinAt h
  simpa [e, Function.comp_def] using hcoord

/-- Ball averages are left-continuous wherever the denominator is positive
and finite and the field is integrable on that ball. -/
theorem continuousWithinAt_average_ball_radius {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (hf : Measurable f)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hi : IntegrableOn f (ball x r) μ)
    (hpos : μ (ball x r) ≠ 0) (hfin : μ (ball x r) ≠ ∞) :
    ContinuousWithinAt (fun s => ⨍ y in ball x s, f y ∂μ) (Iic r) r := by
  simp only [setAverage_eq]
  exact ((continuousWithinAt_measureReal_ball_radius μ x r hfin).inv₀
    (ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩)).smul
    (continuousWithinAt_integral_ball_radius μ hf x r hi)

/-- For functions left-continuous at positive radii, testing all positive
rational radii is equivalent to the full right-hand limit at zero. -/
theorem tendsto_nhdsGT_zero_iff_rat_of_leftContinuous {E : Type*} [MetricSpace E]
    {F : ℝ → E} (hF : ∀ r > 0, ContinuousWithinAt F (Iic r) r) (z : E) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 z) ↔
      Tendsto (fun q : ℚ => F q)
        (comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 z) := by
  constructor
  · intro h
    exact h.comp tendsto_comap
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := h.eventually (ball_mem_nhds z (half_pos hε))
    rw [eventually_comap] at hsmall
    obtain ⟨δ, hδ, hd⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hsmall
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨q, _, hq, hqtop⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      Rat.cast_mono hr.1
    have hqin : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[Iic r] r) :=
      tendsto_nhdsWithin_iff.mpr ⟨hqtop, Eventually.of_forall fun n => (hq n).2.le⟩
    have hlim := ((hF r hr.1).tendsto.comp hqin).dist
      (tendsto_const_nhds (x := z))
    have hbound : dist (F r) z ≤ ε / 2 := le_of_tendsto hlim
      (Eventually.of_forall fun n =>
        (hd ⟨(hq n).1, ((hq n).2.trans hr.2).le⟩ (q n) rfl).le)
    exact hbound.trans_lt (half_lt_self hε)

lemma neBot_comap_rat_nhdsGT_zero :
    NeBot (comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) := by
  obtain ⟨q, _, hq, ht⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_mono (show (0 : ℝ) < 1 by norm_num)
  have ht' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun n => (hq n).1⟩
  exact (tendsto_comap_iff.mpr ht' : Tendsto q atTop _).neBot

/-- Existence of a unit radial limit is a Borel condition whenever each
fixed-radius evaluation is Borel and each radial function is left-continuous. -/
theorem measurableSet_exists_unit_radial_limit {α : Type*} [MeasurableSpace α] {m : ℕ}
    {F : α → ℝ → EuclideanSpace ℝ (Fin m)} (hm : ∀ r, Measurable (fun x => F x r))
    (hc : ∀ x r, 0 < r → ContinuousWithinAt (F x) (Iic r) r) :
    MeasurableSet {x | ∃ z, ‖z‖ = 1 ∧ Tendsto (F x) (𝓝[>] (0 : ℝ)) (𝓝 z)} := by
  let l := comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))
  have : NeBot l := neBot_comap_rat_nhdsGT_zero
  have hconv : MeasurableSet {x | ∃ z, Tendsto (fun q : ℚ => F x q) l (𝓝 z)} :=
    measurableSet_exists_tendsto (fun q => hm q)
  have hnorm : MeasurableSet {x | Tendsto (fun q : ℚ => ‖F x q‖) l (𝓝 (1 : ℝ))} :=
    measurableSet_tendsto (𝓝 1) (fun q => (hm q).norm)
  have heq : {x | ∃ z, ‖z‖ = 1 ∧ Tendsto (F x) (𝓝[>] (0 : ℝ)) (𝓝 z)} =
      {x | ∃ z, Tendsto (fun q : ℚ => F x q) l (𝓝 z)} ∩
        {x | Tendsto (fun q : ℚ => ‖F x q‖) l (𝓝 (1 : ℝ))} := by
    ext x
    constructor
    · rintro ⟨z, hz, ht⟩
      have hq := (tendsto_nhdsGT_zero_iff_rat_of_leftContinuous (hc x) z).mp ht
      exact ⟨⟨z, hq⟩, hz ▸ hq.norm⟩
    · rintro ⟨⟨z, ht⟩, hn⟩
      exact ⟨z, tendsto_nhds_unique ht.norm hn,
        (tendsto_nhdsGT_zero_iff_rat_of_leftContinuous (hc x) z).mpr ht⟩
  rw [heq]
  exact hconv.inter hnorm

/-- Local integrability gives radial left continuity, including balls of
zero mass, on which the average is defined to be zero. -/
theorem continuousWithinAt_average_ball_radius_of_locallyIntegrable {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Measurable f) (hi : LocallyIntegrable f μ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContinuousWithinAt (fun s => ⨍ y in ball x s, f y ∂μ) (Iic r) r := by
  by_cases hz : μ (ball x r) = 0
  · have havg (s : ℝ) (hs : s ≤ r) : (⨍ y in ball x s, f y ∂μ) = 0 := by
      have hzs := measure_mono_null (ball_subset_ball hs) hz
      simp only [setAverage_eq, measureReal_def, hzs, ENNReal.toReal_zero, inv_zero, zero_smul]
    change Tendsto _ _ _
    dsimp only
    rw [havg r le_rfl]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (havg s hs).symm
  · exact continuousWithinAt_average_ball_radius μ hf x r
      ((hi.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall) hz
      ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall x r).measure_lt_top).ne

/-- The unit-limit condition defining a reduced boundary is Borel. -/
theorem measurableSet_exists_unit_ball_average_limit {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Measurable f) (hi : LocallyIntegrable f μ) :
    MeasurableSet {x | ∃ z, ‖z‖ = 1 ∧
      Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 z)} :=
  measurableSet_exists_unit_radial_limit (measurable_average_ball μ hf)
    (fun x r _ => continuousWithinAt_average_ball_radius_of_locallyIntegrable μ hf hi x r)

end LiquidDrop
