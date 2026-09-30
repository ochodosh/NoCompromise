module

public import NoCompromise.Elliptic.NewtonianSchauderKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

/-!
# Radial integrals for Newtonian Hölder estimates

The near-field exponent `α - 3` is integrable precisely in the range used here,
`α > 0`. The far-field exponent `α - 4` is integrable for `α < 1`. Their exact
integrals exhibit the constants `4π/α` and `4π/(1-α)` in the elementary Schauder
argument. These are genuine Lebesgue integrals, with integrability proved first.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma schauder_integral_radial (g : ℝ → ℝ) :
    (∫ x : E₃, g ‖x‖) = 4 * Real.pi * ∫ r in Ioi (0 : ℝ), r ^ 2 * g r := by
  have h := integral_fun_norm_addHaar (volume : Measure E₃) g
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, Measure.real, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi * 4 / 3 by positivity),
    nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [h]
  ring

lemma schauder_radial_rpow_mul {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r ^ 2 * r ^ q = r ^ (q + 2) := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
  congr 1
  ring

lemma integrableOn_schauder_near_power {α R : ℝ} (hα : 0 < α) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ (α - 3)) (ball 0 R) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun r : ℝ => r ^ (α - 3))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  have hi : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioo 0 R) := by
    by_cases hR : 0 < R
    · exact (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr (by linarith)
    · simp [Ioo_eq_empty_of_le (not_lt.mp hR)]
  apply hi.congr_fun _ measurableSet_Ioo
  intro r hr
  dsimp only
  rw [schauder_radial_rpow_mul hr.1]
  congr 1
  ring

lemma integral_schauder_near_power {α R : ℝ} (hα : 0 < α) (hR : 0 ≤ R) :
    (∫ x : E₃ in ball 0 R, ‖x‖ ^ (α - 3)) = 4 * Real.pi * R ^ α / α := by
  have h := schauder_integral_radial ((Iio R).indicator (fun r : ℝ => r ^ (α - 3)))
  have he : (fun x : E₃ => (Iio R).indicator (fun r : ℝ => r ^ (α - 3)) ‖x‖) =
      (ball (0 : E₃) R).indicator (fun x => ‖x‖ ^ (α - 3)) := by
    funext x
    simp [indicator]
  rw [he, integral_indicator measurableSet_ball] at h
  have hr : (∫ r in Ioi (0 : ℝ), r ^ 2 *
      (Iio R).indicator (fun s : ℝ => s ^ (α - 3)) r) = R ^ α / α := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun s : ℝ => s ^ (α - 1)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases hrR : r < R
        · simp only [indicator_of_mem (show r ∈ Iio R from hrR)]
          rw [schauder_radial_rpow_mul hr]
          congr 1
          ring
        · simp [hrR]
      _ = ∫ r in Ioo (0 : ℝ) R, r ^ (α - 1) := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          inter_comm, Ioi_inter_Iio]
      _ = R ^ α / α := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
          integral_rpow (Or.inl (by linarith : -1 < α - 1))]
        simp [Real.zero_rpow hα.ne']
  rw [hr] at h
  rw [h]
  ring

lemma integrableOn_schauder_far_power {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ (α - 4)) {x | R < ‖x‖} := by
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const continuous_norm.measurable)]
  have he : ({x : E₃ | R < ‖x‖}.indicator (fun x => ‖x‖ ^ (α - 4))) =
      (fun x : E₃ => (Ioi R).indicator (fun r : ℝ => r ^ (α - 4)) ‖x‖) := by
    funext x
    rfl
  rw [he, integrable_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : α - 2 < -1) hR
  have hi' : IntegrableOn ((Ioi R).indicator (fun r : ℝ => r ^ (α - 2))) (Ioi 0) :=
    (hi.integrable_indicator measurableSet_Ioi).integrableOn
  apply hi'.congr_fun _ measurableSet_Ioi
  intro r hr
  by_cases hRr : R < r
  · simp only [indicator_of_mem (show r ∈ Ioi R from hRr)]
    rw [schauder_radial_rpow_mul hr]
    congr 1
    ring
  · simp [hRr]

lemma integral_schauder_far_power {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    (∫ x : E₃ in {x | R < ‖x‖}, ‖x‖ ^ (α - 4)) =
      4 * Real.pi * R ^ (α - 1) / (1 - α) := by
  have h := schauder_integral_radial ((Ioi R).indicator (fun r : ℝ => r ^ (α - 4)))
  have he : (fun x : E₃ => (Ioi R).indicator (fun r : ℝ => r ^ (α - 4)) ‖x‖) =
      ({x : E₃ | R < ‖x‖}).indicator (fun x => ‖x‖ ^ (α - 4)) := by
    funext x
    rfl
  rw [he, integral_indicator
    (measurableSet_lt measurable_const continuous_norm.measurable)] at h
  have hr : (∫ r in Ioi (0 : ℝ), r ^ 2 *
      (Ioi R).indicator (fun s : ℝ => s ^ (α - 4)) r) = R ^ (α - 1) / (1 - α) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Ioi R).indicator (fun s : ℝ => s ^ (α - 2)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases hRr : R < r
        · simp only [indicator_of_mem (show r ∈ Ioi R from hRr)]
          rw [schauder_radial_rpow_mul hr]
          congr 1
          ring
        · simp [hRr]
      _ = ∫ r in Ioi R, r ^ (α - 2) := by
        rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          inter_eq_left.mpr (Ioi_subset_Ioi hR.le)]
      _ = R ^ (α - 1) / (1 - α) := by
        rw [integral_Ioi_rpow_of_lt (by linarith : α - 2 < -1) hR]
        rw [show α - 2 + 1 = α - 1 by ring, show 1 - α = -(α - 1) by ring]
        simp only [div_neg, neg_div]
  rw [hr] at h
  rw [h]
  ring

end LiquidDrop
