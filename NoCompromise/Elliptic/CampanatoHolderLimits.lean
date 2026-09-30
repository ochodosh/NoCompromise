module

public import NoCompromise.Elliptic.CampanatoHolderAverages

@[expose] public section

/-! Squared mean-oscillation decay constructs a genuine limit of the ball
averages at every center, with a uniform error at every positive small radius. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The constant is chosen before the function, center, and starting radius.
No Lebesgue-point or continuity premise is imposed at the center. -/
theorem campanato_average_limit_constant {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {B γ : ℝ} (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → F)
      (x : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      MemLp f 2 (volume.restrict (ball x R)) →
      (∀ r ∈ Ioc 0 R, (∫ y in ball x r, ‖f y - ⨍ z in ball x r, f z‖ ^ 2) ≤
        (B * r ^ γ) ^ 2 * volume.real (ball x r)) →
      ∃ v : F,
        Tendsto (fun j : ℕ => ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y) atTop (𝓝 v) ∧
        ∀ r ∈ Ioc 0 R, ‖(⨍ y in ball x r, f y) - v‖ ≤ C * r ^ γ := by
  let q := (1 / 2 : ℝ) ^ γ
  let A := Real.sqrt ((2 : ℝ) ^ n) * B
  let L := A / (1 - q)
  let C := (A + L) * (2 : ℝ) ^ γ
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 ≤ L := div_nonneg hA (sub_pos.mpr hq).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f x R hR hf hosc
  let ρ (j : ℕ) := (1 / 2 : ℝ) ^ j * R
  let m (j : ℕ) := ⨍ y in ball x (ρ j), f y
  have hρ (j : ℕ) : ρ j ∈ Ioc 0 R := by
    refine ⟨mul_pos (pow_pos (by norm_num) j) hR, ?_⟩
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) hR.le
  have hρsucc (j : ℕ) : ρ (j + 1) = ρ j / 2 := by dsimp [ρ]; rw [pow_succ]; ring
  have hρpow (j : ℕ) : ρ j ^ γ = q ^ j * R ^ γ := by
    dsimp [ρ, q]
    rw [Real.mul_rpow (pow_nonneg (by norm_num) j) hR.le,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) γ j]
  have hstep (j : ℕ) : dist (m j) (m (j + 1)) ≤ (A * R ^ γ) * q ^ j := by
    have hs : ball x (ρ j / 2) ⊆ ball x (ρ j) :=
      ball_subset_ball (by linarith [(hρ j).1])
    have hm := campanato_average_half_radius_bound hn (hρ j).1 hB hs
      (hf.mono_measure (Measure.restrict_mono (ball_subset_ball (hρ j).2) le_rfl))
      (hosc _ (hρ j))
    rw [dist_eq_norm, norm_sub_rev]
    change ‖(⨍ y in ball x (ρ (j + 1)), f y) - ⨍ y in ball x (ρ j), f y‖ ≤ _
    rw [hρsucc]
    calc
      _ ≤ A * ρ j ^ γ := hm
      _ = _ := by rw [hρpow]; ring
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric q (A * R ^ γ) hq hstep)
  have htail (j : ℕ) : ‖m j - v‖ ≤ L * ρ j ^ γ := by
    have ht := dist_le_of_le_geometric_of_tendsto q (A * R ^ γ) hq hstep hv j
    rw [dist_eq_norm] at ht
    convert ht using 1
    rw [hρpow]
    dsimp [L]
    ring
  refine ⟨v, hv, ?_⟩
  intro r hr
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr.1 hR) ((div_le_one hR).mpr hr.2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hrj : r ≤ ρ j := (div_le_iff₀ hR).mp hjhi
  have hjr : ρ j / 2 ≤ r := by
    have ht := (lt_div_iff₀ hR).mp hjlo
    rw [pow_succ] at ht
    dsimp [ρ]
    nlinarith only [ht]
  have hcompare := campanato_average_comparable_radius_bound hn (hρ j).1 hB hjr
    (ball_subset_ball hrj)
    (hf.mono_measure (Measure.restrict_mono (ball_subset_ball (hρ j).2) le_rfl))
    (hosc _ (hρ j))
  have hpower : ρ j ^ γ ≤ (2 * r) ^ γ :=
    Real.rpow_le_rpow (hρ j).1.le (by linarith only [hjr]) hγ.le
  calc
    _ ≤ ‖(⨍ y in ball x r, f y) - m j‖ + ‖m j - v‖ := by
      simpa only [dist_eq_norm] using dist_triangle (⨍ y in ball x r, f y) (m j) v
    _ ≤ A * ρ j ^ γ + L * ρ j ^ γ := add_le_add hcompare (htail j)
    _ = (A + L) * ρ j ^ γ := by ring
    _ ≤ (A + L) * (2 * r) ^ γ :=
      mul_le_mul_of_nonneg_left hpower (add_nonneg hA hL)
    _ = C * r ^ γ := by rw [Real.mul_rpow (by norm_num) hr.1.le]; dsimp [C]; ring

end LiquidDrop
