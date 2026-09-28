import NoCompromise.Regularity.FluxDefectTests
import NoCompromise.BV.CoareaSmooth

/-! # Smooth one-sided approximations to horizontal disks -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def fluxDiskCutoff (s : ℝ) (j : ℕ) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.smoothTransition (((j : ℝ) + 1) * (s ^ 2 - ‖p‖ ^ 2))

lemma contDiff_fluxDiskCutoff (s : ℝ) (j : ℕ) : ContDiff ℝ 1 (fluxDiskCutoff s j) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))

lemma fluxDiskCutoff_mem_Icc (s : ℝ) (j : ℕ) (p : EuclideanSpace ℝ (Fin 2)) :
    fluxDiskCutoff s j p ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma tsupport_fluxDiskCutoff {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    tsupport (fluxDiskCutoff s j) ⊆ closedBall 0 s := by
  apply closure_minimal ?_ isClosed_closedBall
  intro p hp
  by_contra hball
  have hn : s < ‖p‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hball
  apply hp
  apply Real.smoothTransition.zero_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  nlinarith [norm_nonneg p]

lemma hasCompactSupport_fluxDiskCutoff {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    HasCompactSupport (fluxDiskCutoff s j) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) s).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_fluxDiskCutoff hs j)

lemma tendsto_fluxDiskCutoff {s : ℝ} (hs : 0 < s) (p : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun j => fluxDiskCutoff s j p) atTop
      (𝓝 ((ball (0 : EuclideanSpace ℝ (Fin 2)) s).indicator (fun _ => (1 : ℝ)) p)) := by
  have he : (0 : ℝ) < s ^ 2 - ‖p‖ ^ 2 ↔ p ∈ ball 0 s := by
    rw [mem_ball, dist_zero_right]
    constructor <;> intro hh <;> nlinarith [norm_nonneg p]
  have hv : (ball (0 : EuclideanSpace ℝ (Fin 2)) s).indicator (fun _ => (1 : ℝ)) p =
      if 0 < s ^ 2 - ‖p‖ ^ 2 then 1 else 0 := by
    by_cases hh : 0 < s ^ 2 - ‖p‖ ^ 2
    · simp [he.mp hh, hh]
    · simp [mt he.mpr hh, hh]
  rw [hv]
  simpa only [fluxDiskCutoff, sub_zero] using
    tendsto_smoothTransition_nat_mul_sub (s ^ 2 - ‖p‖ ^ 2) 0

lemma tendsto_integral_fluxDiskCutoff {s : ℝ} (hs : 0 < s) :
    Tendsto (fun j => ∫ p, fluxDiskCutoff s j p) atTop (𝓝 (Real.pi * s ^ 2)) := by
  let b : EuclideanSpace ℝ (Fin 2) → ℝ := (closedBall 0 s).indicator (fun _ => (1 : ℝ))
  have hc : Continuous (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) := continuous_const
  have hi : Integrable b := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 s))
  have ht := tendsto_integral_of_dominated_convergence b
    (fun j => (contDiff_fluxDiskCutoff s j).continuous.aestronglyMeasurable)
    hi (fun j => Eventually.of_forall fun p => by
      have hh := fluxDiskCutoff_mem_Icc s j p
      rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
      by_cases hp : p ∈ closedBall 0 s
      · rw [show b p = 1 from indicator_of_mem hp _]
        exact hh.2
      · rw [show b p = 0 from indicator_of_notMem hp _]
        exact le_of_eq (image_eq_zero_of_notMem_tsupport
          (fun ht => hp (tsupport_fluxDiskCutoff hs.le j ht))))
    (Eventually.of_forall (tendsto_fluxDiskCutoff hs))
  have he : (∫ p : EuclideanSpace ℝ (Fin 2),
      (ball 0 s).indicator (fun _ => (1 : ℝ)) p) = Real.pi * s ^ 2 := by
    rw [integral_indicator measurableSet_ball, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply_univ]
    rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hs.le, ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  simpa only [he] using ht

end LiquidDrop
