module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# Ball masses under local weak-star convergence

Compact bump functions sandwich ball indicators. For a fixed locally finite
measure, dominated convergence identifies the bump integrals when the limiting
sphere is null. Convergence on compactly supported continuous tests then gives
convergence of the actual ball masses.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma integral_bump_between_ball_measures {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {c : EuclideanSpace ℝ (Fin n)} (φ : ContDiffBump c) :
    μ.real (closedBall c φ.rIn) ≤ (∫ y, φ y ∂μ) ∧
      (∫ y, φ y ∂μ) ≤ μ.real (ball c φ.rOut) := by
  have hi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  constructor
  · calc
      _ = ∫ y in closedBall c φ.rIn, φ y ∂μ := by
        rw [show (∫ y in closedBall c φ.rIn, φ y ∂μ) = ∫ _y in closedBall c φ.rIn,
          (1 : ℝ) ∂μ from setIntegral_congr_fun measurableSet_closedBall
            (fun y hy => φ.one_of_mem_closedBall hy)]
        simp
      _ ≤ ∫ y, φ y ∂μ := setIntegral_le_integral hi (Eventually.of_forall φ.nonneg')
  · have heq : (∫ y in ball c φ.rOut, φ y ∂μ) = ∫ y, φ y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
        φ.zero_of_le_dist (le_of_not_gt hy)
    rw [← heq]
    have hm : μ (ball c φ.rOut) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall c φ.rOut).measure_lt_top).ne
    calc
      _ ≤ ∫ _y in ball c φ.rOut, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hi.integrableOn (integrableOn_const hm)
        exact Eventually.of_forall fun _ => φ.le_one
      _ = μ.real (ball c φ.rOut) := by simp

/-- Bumps with both radii approaching a null sphere converge in integral to its ball mass. -/
theorem tendsto_integral_bump_of_radii_tendsto {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {c : EuclideanSpace ℝ (Fin n)} (φ : ℕ → ContDiffBump c) {R M : ℝ}
    (hIn : Tendsto (fun j => (φ j).rIn) atTop (𝓝 R))
    (hOut : Tendsto (fun j => (φ j).rOut) atTop (𝓝 R))
    (hM : ∀ j, (φ j).rOut ≤ M) (hnull : μ (sphere c R) = 0) :
    Tendsto (fun j => ∫ y, φ j y ∂μ) atTop (𝓝 (μ.real (ball c R))) := by
  have hb : Integrable ((closedBall c M).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (isCompact_closedBall c M).measure_lt_top.ne)
  have ht : Tendsto (fun j => ∫ y, φ j y ∂μ) atTop
      (𝓝 (∫ y, (ball c R).indicator (fun _ => (1 : ℝ)) y ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall c M).indicator (fun _ => (1 : ℝ)))
      (fun j => (φ j).continuous.aestronglyMeasurable) hb ?_ ?_
    · intro j
      apply Eventually.of_forall
      intro y
      by_cases hy : y ∈ closedBall c M
      · rw [indicator_of_mem hy, Real.norm_of_nonneg (φ j).nonneg]
        exact (φ j).le_one
      · have hz : φ j y = 0 := (φ j).zero_of_le_dist
          ((hM j).trans (le_of_lt (lt_of_not_ge hy)))
        rw [hz, norm_zero, indicator_of_notMem hy]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
      have hne : dist y c ≠ R := hy
      by_cases hlt : dist y c < R
      · rw [indicator_of_mem (show y ∈ ball c R from hlt)]
        apply tendsto_const_nhds.congr'
        filter_upwards [hIn.eventually (Ioi_mem_nhds hlt)] with j hj
        exact ((φ j).one_of_mem_closedBall hj.le).symm
      · rw [indicator_of_notMem (show y ∉ ball c R from hlt)]
        have hgt : R < dist y c := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        apply tendsto_const_nhds.congr'
        filter_upwards [hOut.eventually (Iio_mem_nhds hgt)] with j hj
        exact ((φ j).zero_of_le_dist hj.le).symm
  simpa [integral_indicator measurableSet_ball] using ht

/-- Local weak-star convergence gives convergence of every ball whose boundary is null. -/
theorem tendsto_real_ball_of_compact_test_convergence {n : ℕ}
    (μs : ℕ → Measure (EuclideanSpace ℝ (Fin n))) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [∀ j, IsFiniteMeasureOnCompacts (μs j)] [IsFiniteMeasureOnCompacts μ]
    (ht : ∀ f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      Tendsto (fun j => ∫ y, f y ∂μs j) atTop (𝓝 (∫ y, f y ∂μ)))
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) (hnull : μ (sphere c R) = 0) :
    Tendsto (fun j => (μs j).real (ball c R)) atTop (𝓝 (μ.real (ball c R))) := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hεpos (j) : 0 < ε j := by dsimp [ε]; positivity
  have hεle (j) : ε j ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let lo (j : ℕ) : ContDiffBump c :=
    ⟨R / (1 + ε j), R, by positivity, by
      apply (div_lt_iff₀ (by positivity : 0 < 1 + ε j)).mpr
      nlinarith [hεpos j]⟩
  let up (j : ℕ) : ContDiffBump c :=
    ⟨R, R + ε j, hR, by have := hεpos j; linarith⟩
  have hloIn : Tendsto (fun j => (lo j).rIn) atTop (𝓝 R) := by
    have h := (tendsto_const_nhds (x := R)).div (tendsto_const_nhds.add hε)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
    change Tendsto (fun j => R / (1 + ε j)) atTop (𝓝 (R / (1 + 0))) at h
    simpa only [lo, add_zero, div_one] using h
  have hlo := tendsto_integral_bump_of_radii_tendsto μ lo hloIn tendsto_const_nhds
    (M := R + 1) (fun _ => by dsimp [lo]; linarith) hnull
  have hupOut : Tendsto (fun j => (up j).rOut) atTop (𝓝 R) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hup := tendsto_integral_bump_of_radii_tendsto μ up tendsto_const_nhds hupOut
    (M := R + 1) (fun j => by dsimp [up]; linarith [hεle j]) hnull
  have htest (φ : ContDiffBump c) :
      Tendsto (fun j => ∫ y, φ y ∂μs j) atTop (𝓝 (∫ y, φ y ∂μ)) :=
    ht ⟨⟨φ, φ.continuous⟩, φ.hasCompactSupport⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hlo.eventually (Ioi_mem_nhds ha)).exists
    filter_upwards [(htest (lo k)).eventually (Ioi_mem_nhds hk)] with j hj
    exact hj.trans_le (integral_bump_between_ball_measures (μs j) (lo k)).2
  · intro b hb
    obtain ⟨k, hk⟩ := (hup.eventually (Iio_mem_nhds hb)).exists
    filter_upwards [(htest (up k)).eventually (Iio_mem_nhds hk)] with j hj
    have hm : (μs j) (closedBall c R) ≠ ∞ := (isCompact_closedBall c R).measure_lt_top.ne
    have hball : (μs j).real (ball c R) ≤ (μs j).real (closedBall c R) :=
      ENNReal.toReal_mono hm (measure_mono ball_subset_closedBall)
    exact (hball.trans (integral_bump_between_ball_measures (μs j) (up k)).1).trans_lt hj

end LiquidDrop
