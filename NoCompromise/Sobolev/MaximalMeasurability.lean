import NoCompromise.Conventions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

/-!
# Lower semicontinuity of centered maximal densities

For fixed radius, ball mass is lower semicontinuous in the center. Rational inner
radii and continuity from below prove this for every measure, without finiteness
or regularity assumptions. Dividing by the positive, center-independent ball volume
and taking arbitrary suprema gives the corresponding maximal-density statements.
No maximal function definition or weak maximal inequality is assumed here.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace LiquidDrop

/-- Ball mass is the supremum of masses of concentric balls with smaller rational radii. -/
lemma measure_ball_eq_iSup_rat_lt {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (r : ℝ) :
    μ (ball x r) = ⨆ s : {s : ℚ // (s : ℝ) < r}, μ (ball x (s : ℝ)) := by
  have hmono : Monotone (fun s : {s : ℚ // (s : ℝ) < r} => ball x (s : ℝ)) := by
    intro a b hab
    exact ball_subset_ball (by exact_mod_cast hab)
  have hball : (⋃ s : {s : ℚ // (s : ℝ) < r}, ball x (s : ℝ)) = ball x r := by
    ext y
    simp only [mem_iUnion, mem_ball]
    constructor
    · rintro ⟨s, hs⟩
      exact hs.trans s.property
    · intro hy
      obtain ⟨s, hs, hsr⟩ := exists_rat_btwn hy
      exact ⟨⟨s, hsr⟩, hs⟩
  rw [← hball]
  exact hmono.measure_iUnion

/-- For any measure, the mass of a fixed-radius open ball is lower semicontinuous in its center. -/
theorem lowerSemicontinuous_measure_ball {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) : LowerSemicontinuous (fun x => μ (ball x r)) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  apply Metric.isOpen_iff.mpr
  intro x hx
  change t < μ (ball x r) at hx
  rw [measure_ball_eq_iSup_rat_lt] at hx
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hx
  refine ⟨r - (s : ℝ), sub_pos.mpr s.property, fun y hy => ?_⟩
  change t < μ (ball y r)
  apply hs.trans_le (measure_mono ?_)
  intro z hz
  have hxy : dist x y < r - (s : ℝ) := by simpa only [mem_ball, dist_comm] using hy
  have hzx : dist z x < (s : ℝ) := hz
  exact (dist_triangle z x y).trans_lt (by linarith)

/-- The fixed-radius ball density is lower semicontinuous in Euclidean space.
The denominator is volume of that same ball, and the radius is strictly positive. -/
theorem lowerSemicontinuous_ballRatio {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 < r) :
    LowerSemicontinuous (fun x => μ (ball x r) / volume (ball x r)) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  have hzero : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≠ 0 :=
    (measure_ball_pos volume 0 hr).ne'
  have htop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≠ ∞ :=
    measure_ball_lt_top.ne
  have heq : {x : EuclideanSpace ℝ (Fin n) | t < μ (ball x r) / volume (ball x r)} =
      {x | t * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) < μ (ball x r)} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, Measure.addHaar_ball_center volume x r,
      ENNReal.lt_div_iff_mul_lt (Or.inl hzero) (Or.inl htop)]
  change IsOpen {x : EuclideanSpace ℝ (Fin n) | t < μ (ball x r) / volume (ball x r)}
  rw [heq]
  exact (lowerSemicontinuous_measure_ball μ r).isOpen_preimage _

/-- The raw centered maximal-density supremum is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_ballRatio {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    LowerSemicontinuous (fun x => ⨆ r : ℝ, ⨆ (_ : 0 < r),
      μ (ball x r) / volume (ball x r)) :=
  lowerSemicontinuous_iSup fun _ => lowerSemicontinuous_iSup fun hr =>
    lowerSemicontinuous_ballRatio μ hr

/-- Truncating the allowable radii preserves lower semicontinuity, even for a nonpositive cutoff. -/
theorem lowerSemicontinuous_iSup_ballRatio_lt {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (R : ℝ) :
    LowerSemicontinuous (fun x => ⨆ r : ℝ, ⨆ (_ : 0 < r), ⨆ (_ : r < R),
      μ (ball x r) / volume (ball x r)) :=
  lowerSemicontinuous_iSup fun _ => lowerSemicontinuous_iSup fun hr =>
    lowerSemicontinuous_iSup fun _ => lowerSemicontinuous_ballRatio μ hr

/-- Strict ball-ratio superlevels are open for every extended-real threshold. -/
theorem isOpen_ballRatio_superlevel {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ≥0∞) :
    IsOpen {x | ∃ r : ℝ, 0 < r ∧ t < μ (ball x r) / volume (ball x r)} := by
  have h := (lowerSemicontinuous_iSup_ballRatio μ).isOpen_preimage t
  simpa only [preimage, mem_Ioi, lt_iSup_iff, exists_prop] using h

/-- The same openness holds with a strict upper bound on the witnessing radius. -/
theorem isOpen_ballRatio_superlevel_lt {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (R : ℝ) (t : ℝ≥0∞) :
    IsOpen {x | ∃ r : ℝ, 0 < r ∧ r < R ∧ t < μ (ball x r) / volume (ball x r)} := by
  have h := (lowerSemicontinuous_iSup_ballRatio_lt μ R).isOpen_preimage t
  simpa only [preimage, mem_Ioi, lt_iSup_iff, exists_prop] using h

/-- The raw full maximal-density expression is Borel measurable. -/
theorem measurable_iSup_ballRatio {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun x => ⨆ r : ℝ, ⨆ (_ : 0 < r), μ (ball x r) / volume (ball x r)) :=
  (lowerSemicontinuous_iSup_ballRatio μ).measurable

/-- The raw truncated maximal-density expression is Borel measurable. -/
theorem measurable_iSup_ballRatio_lt {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (R : ℝ) :
    Measurable (fun x => ⨆ r : ℝ, ⨆ (_ : 0 < r), ⨆ (_ : r < R),
      μ (ball x r) / volume (ball x r)) :=
  (lowerSemicontinuous_iSup_ballRatio_lt μ R).measurable

end LiquidDrop
