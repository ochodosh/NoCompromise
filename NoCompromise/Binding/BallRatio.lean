module

public import NoCompromise.Ball.Potential
public import NoCompromise.Threshold.Ledger

@[expose] public section

/-!
# The uniquely optimal volume among balls

The original ball energy divided by its prescribed volume has its unique
minimum at volume 5/2. The algebraic ledger supplies the exact factorization.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LiquidDrop

lemma real_cuberoot_cube {V : ℝ} (hV : 0 ≤ V) :
    (V ^ (1 / (3 : ℝ))) ^ 3 = V := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
  norm_num

lemma real_cuberoot_sq {V : ℝ} (hV : 0 ≤ V) :
    (V ^ (1 / (3 : ℝ))) ^ 2 = V ^ (2 / (3 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
  norm_num

theorem ball_energy_ratio_cuberoot {V : ℝ} (hV : 0 < V) :
    (energy (ballByVolume V)).toReal / V =
      (36 * Real.pi) ^ (1 / (3 : ℝ)) *
        (1 / V ^ (1 / (3 : ℝ)) + (V ^ (1 / (3 : ℝ))) ^ 2 / 5) := by
  rw [energy_ballByVolume_toReal hV, ballPerimeter_toReal_eq_rpow hV,
    ← real_cuberoot_sq hV.le]
  set x := V ^ (1 / (3 : ℝ))
  have hx : x ≠ 0 := (Real.rpow_pos_of_pos hV _).ne'
  have hcube : x ^ 3 = V := real_cuberoot_cube hV.le
  rw [← hcube]
  field_simp
  ring

/-- The volume-only formula for the actual energy-to-volume ratio. -/
theorem ball_energy_ratio {V : ℝ} (hV : 0 < V) :
    (energy (ballByVolume V)).toReal / V =
      (36 * Real.pi) ^ (1 / (3 : ℝ)) *
        (V ^ (-1 / (3 : ℝ)) + (1 / 5 : ℝ) * V ^ (2 / (3 : ℝ))) := by
  rw [ball_energy_ratio_cuberoot hV, real_cuberoot_sq hV.le]
  have hi : 1 / V ^ (1 / (3 : ℝ)) = V ^ (-1 / (3 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg hV.le]
    congr 1
    norm_num
  rw [hi]
  ring

/-- The first exact expression for the optimal ball ratio. -/
theorem ball_energy_ratio_at_five_halves :
    (energy (ballByVolume (5 / 2))).toReal / (5 / 2) =
      (36 * Real.pi) ^ (1 / (3 : ℝ)) * (3 / (2 * (5 / 2 : ℝ) ^ (1 / (3 : ℝ)))) := by
  rw [ball_energy_ratio_cuberoot (by norm_num : (0 : ℝ) < 5 / 2)]
  congr 1
  exact sub_eq_zero.mp ((ledger_binding _
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 2) _)).2.2.mpr rfl)

/-- The two stated expressions for the optimal value coincide. -/
theorem ball_optimal_ratio_value :
    (36 * Real.pi) ^ (1 / (3 : ℝ)) * (3 / (2 * (5 / 2 : ℝ) ^ (1 / (3 : ℝ)))) =
      3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ)) := by
  apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, div_pow, mul_pow, real_cuberoot_cube (by positivity),
    real_cuberoot_cube (by norm_num), mul_pow, real_cuberoot_cube (by positivity)]
  ring

/-- Every positive-volume ball has at least the ratio of the volume-5/2 ball. -/
theorem ball_energy_ratio_min {V : ℝ} (hV : 0 < V) :
    (energy (ballByVolume (5 / 2))).toReal / (5 / 2) ≤
      (energy (ballByVolume V)).toReal / V := by
  rw [ball_energy_ratio_at_five_halves, ball_energy_ratio_cuberoot hV]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  exact sub_nonneg.mp (ledger_binding _ (Real.rpow_pos_of_pos hV _)).2.1

/-- Equality in the actual ball-ratio bound determines the volume exactly. -/
theorem ball_energy_ratio_eq_min_iff {V : ℝ} (hV : 0 < V) :
    (energy (ballByVolume V)).toReal / V =
        (energy (ballByVolume (5 / 2))).toReal / (5 / 2) ↔ V = 5 / 2 := by
  rw [ball_energy_ratio_at_five_halves, ball_energy_ratio_cuberoot hV,
    mul_right_inj' (Real.rpow_pos_of_pos (by positivity : 0 < 36 * Real.pi) _).ne',
    ← sub_eq_zero, (ledger_binding _ (Real.rpow_pos_of_pos hV _)).2.2,
    Real.rpow_left_inj hV.le (by norm_num) (by norm_num : (1 / (3 : ℝ)) ≠ 0)]

/-- The complete optimal-ball-volume lemma with its exact value and uniqueness. -/
theorem optimal_ball_volume :
    (energy (ballByVolume (5 / 2))).toReal / (5 / 2) =
        3 * (9 * Real.pi / 5) ^ (1 / (3 : ℝ)) ∧
      ∀ V : ℝ, 0 < V →
        (energy (ballByVolume (5 / 2))).toReal / (5 / 2) ≤
            (energy (ballByVolume V)).toReal / V ∧
          ((energy (ballByVolume V)).toReal / V =
            (energy (ballByVolume (5 / 2))).toReal / (5 / 2) ↔ V = 5 / 2) :=
  ⟨ball_energy_ratio_at_five_halves.trans ball_optimal_ratio_value,
    fun _ hV => ⟨ball_energy_ratio_min hV, ball_energy_ratio_eq_min_iff hV⟩⟩

end LiquidDrop
