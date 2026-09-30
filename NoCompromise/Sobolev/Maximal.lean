module

public import NoCompromise.Conventions
public import NoCompromise.Sobolev.MaximalMeasurability
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Planar maximal measure functions and the weak maximal estimate

The centered and radius-truncated maximal functions use Euclidean ball volume,
identified explicitly with πr². Vitali's five-covering lemma gives the exact
blueprint weak bound 25 μ(univ)/t. The proof applies to every finite measure and
uses outer volume throughout, so it needs no unproved superlevel measurability.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- The centered maximal function of a measure on the plane. The extended-real
value includes atoms and agrees with the blueprint's denominator πr². -/
noncomputable def maximalMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), μ (ball x r) / volume (ball x r)

/-- The same centered maximal function, restricted to radii strictly below R. -/
noncomputable def truncatedMaximalMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), ⨆ (_ : r < R), μ (ball x r) / volume (ball x r)

lemma maximalMeasure_eq_pi (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    maximalMeasure μ x = ⨆ r : ℝ, ⨆ (_ : 0 < r),
      μ (ball x r) / ENNReal.ofReal (Real.pi * r ^ 2) := by
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_pos.le,
    ENNReal.ofReal_pow hr.le, mul_comm (ENNReal.ofReal Real.pi)]

lemma truncatedMaximalMeasure_le (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    truncatedMaximalMeasure μ R x ≤ maximalMeasure μ x := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply iSup_le
  intro _
  exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)

lemma volume_ball_fivefold (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (ball x (5 * r)) = 25 * volume (ball x r) := by
  simp only [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
    ENNReal.ofReal_ofNat, mul_pow]
  ring

/-- The five-covering argument for an arbitrary set with uniformly bounded witnessing
radii. No measurability of the covered set is required, since volume is an outer measure. -/
theorem volume_le_of_bounded_ball_witnesses
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {S : Set (EuclideanSpace ℝ (Fin 2))}
    {R : ℝ} {c : ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      volume (ball x r) ≤ c * μ (ball x r)) :
    volume S ≤ (25 * c) * μ univ := by
  classical
  choose r hr hR hball using fun x : S => hS x x.property
  obtain ⟨u, _, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set S) (fun x => (x : EuclideanSpace ℝ (Fin 2))) r R
    (fun x _ => hR x) 5 (by norm_num)
  have hu : u.Countable := hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (hr x)⟩)
  have : Countable u := hu.to_subtype
  have hcover : S ⊆ ⋃ x : u, ball (x.val : EuclideanSpace ℝ (Fin 2)) (5 * r x.val) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hc ⟨x, hx⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (mem_ball_self (hr ⟨x, hx⟩))⟩
  calc
    volume S ≤ volume (⋃ x : u, ball (x.val : EuclideanSpace ℝ (Fin 2)) (5 * r x.val)) :=
      measure_mono hcover
    _ ≤ ∑' x : u, volume (ball (x.val : EuclideanSpace ℝ (Fin 2)) (5 * r x.val)) :=
      measure_iUnion_le _
    _ = 25 * ∑' x : u, volume (ball (x.val : EuclideanSpace ℝ (Fin 2)) (r x.val)) := by
      simp only [volume_ball_fivefold, ENNReal.tsum_mul_left]
    _ ≤ 25 * ∑' x : u, c * μ (ball (x.val : EuclideanSpace ℝ (Fin 2)) (r x.val)) := by
      gcongr with x
      exact hball x.val
    _ = (25 * c) * μ (⋃ x ∈ u, ball (x : EuclideanSpace ℝ (Fin 2)) (r x)) := by
      rw [ENNReal.tsum_mul_left, measure_biUnion hu hd (fun _ _ => measurableSet_ball), mul_assoc]
    _ ≤ (25 * c) * μ univ := by
      gcongr
      exact subset_univ _


/-- A ball witnessing a positive maximal threshold has uniformly bounded radius
when the measure has finite total mass. -/
lemma maximal_witness_radius_le (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin 2)}
    {r : ℝ} (hr : 0 < r)
    (hb : ENNReal.ofReal t < μ (ball x r) / volume (ball x r)) :
    r ≤ 1 + (μ univ).toReal / (t * Real.pi) := by
  have hvol0 : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hvoltop : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hvol0) (Or.inl hvoltop)).mp hb
  have hh : ENNReal.ofReal (t * Real.pi * r ^ 2) ≤ μ univ := by
    have he : ENNReal.ofReal (t * Real.pi * r ^ 2) =
        ENNReal.ofReal t * volume (ball x r) := by
      rw [EuclideanSpace.volume_ball_fin_two,
        ENNReal.ofReal_mul (mul_nonneg ht.le Real.pi_pos.le),
        ENNReal.ofReal_mul ht.le, ENNReal.ofReal_pow hr.le]
      ring
    rw [he]
    exact hm.le.trans (measure_mono (subset_univ _))
  have hreal := ENNReal.toReal_mono (measure_ne_top μ univ) hh
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hs : r ^ 2 ≤ (μ univ).toReal / (t * Real.pi) := by
    apply (le_div_iff₀ (mul_pos ht Real.pi_pos)).mpr
    nlinarith
  have hp : 0 ≤ (μ univ).toReal / (t * Real.pi) := by positivity
  nlinarith [sq_nonneg (r - 1)]

/-- Blueprint `lem:maximal`: the planar centered maximal measure function has
weak (1,1) bound with the five-covering constant 25. Finiteness of the measure
suffices; no extra regularity or measurability of the superlevel set is assumed. -/
theorem maximalMeasure_weak_bound (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < maximalMeasure μ x} ≤
      ENNReal.ofReal (25 / t) * μ univ := by
  have h := volume_le_of_bounded_ball_witnesses μ
    (S := {x | ENNReal.ofReal t < maximalMeasure μ x})
    (R := 1 + (μ univ).toReal / (t * Real.pi))
    (c := (ENNReal.ofReal t)⁻¹) ?_
  · convert h using 1
    rw [ENNReal.ofReal_div_of_pos ht]
    norm_num [div_eq_mul_inv]
  · intro x hx
    simp only [mem_ofPred_eq, maximalMeasure, lt_iSup_iff] at hx
    obtain ⟨r, hr, hb⟩ := hx
    refine ⟨r, hr, maximal_witness_radius_le μ ht hr hb, ?_⟩
    have hvol0 : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
    have hvoltop : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
    have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hvol0) (Or.inl hvoltop)).mp hb
    rw [mul_comm (ENNReal.ofReal t)⁻¹, ← div_eq_mul_inv]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr ht))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    exact (mul_comm _ _).trans_le hm.le

/-- The same weak bound holds after restricting the radii, for every real cutoff R. -/
theorem truncatedMaximalMeasure_weak_bound (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] (R : ℝ) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < truncatedMaximalMeasure μ R x} ≤
      ENNReal.ofReal (25 / t) * μ univ := by
  apply (measure_mono (show {x | ENNReal.ofReal t < truncatedMaximalMeasure μ R x} ⊆
    {x | ENNReal.ofReal t < maximalMeasure μ x} from
      fun x hx => hx.trans_le (truncatedMaximalMeasure_le μ R x))).trans
  exact maximalMeasure_weak_bound μ ht

/-- The centered maximal measure function is lower semicontinuous. -/
theorem lowerSemicontinuous_maximalMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2))) :
    LowerSemicontinuous (maximalMeasure μ) := lowerSemicontinuous_iSup_ballRatio μ

/-- Restricting the radii preserves lower semicontinuity. -/
theorem lowerSemicontinuous_truncatedMaximalMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (R : ℝ) :
    LowerSemicontinuous (truncatedMaximalMeasure μ R) :=
  lowerSemicontinuous_iSup_ballRatio_lt μ R

/-- The centered maximal measure function is Borel measurable. -/
theorem measurable_maximalMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2))) :
    Measurable (maximalMeasure μ) := measurable_iSup_ballRatio μ

/-- The radius-truncated maximal measure function is Borel measurable. -/
theorem measurable_truncatedMaximalMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2))) (R : ℝ) :
    Measurable (truncatedMaximalMeasure μ R) := measurable_iSup_ballRatio_lt μ R

end LiquidDrop
