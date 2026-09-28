import NoCompromise.Elliptic.FrozenDecayVariance
import NoCompromise.Elliptic.FrozenDecayEstimates

/-! Pointwise interior bounds imply the two integral decay rates. The
large-radius case uses monotonicity and the minimizing property of the mean. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_real_volume_ball {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  simp only [Measure.real, Measure.addHaar_ball volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _), finrank_euclideanSpace, Fintype.card_fin]

lemma frozen_half_radius_power (p : ℕ) {θ : ℝ} (hθ : (1 / 2 : ℝ) ≤ θ) :
    1 ≤ (2 : ℝ) ^ p * θ ^ p := by
  rw [← mul_pow]
  exact one_le_pow₀ (by linarith)

lemma frozen_integral_sq_le_of_ae_norm_bound {n : ℕ}
    {r B : ℝ} {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict (ball 0 r))) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict (ball 0 r), ‖G x‖ ≤ B) :
    (∫ x in ball 0 r, ‖G x‖ ^ 2) ≤
      B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hi := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  calc
    _ ≤ ∫ _x in ball (0 : EuclideanSpace ℝ (Fin n)) r, B ^ 2 := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hb] with x hx
      exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hx
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, Measure.real,
      smul_eq_mul]; ring

/-- An interior supremum estimate supplies the noncentered unit-ball decay. -/
theorem frozen_energy_decay_of_unit_bound {n : ℕ} (hn : 0 < n)
    {G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict (ball 0 1)))
    (he : G =ᵐ[volume.restrict (ball 0 1)] F)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball 0 (1 / 2 : ℝ),
      ‖F x‖ ≤ B * lpNorm G 2 (volume.restrict (ball 0 1)))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ x in ball 0 θ, ‖G x‖ ^ 2) ≤
      max (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ((2 : ℝ) ^ n) *
        θ ^ n * ∫ x in ball 0 1, ‖G x‖ ^ 2 := by
  have hs : ball (0 : EuclideanSpace ℝ (Fin n)) θ ⊆ ball 0 1 := ball_subset_ball hθ1.le
  have hi := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hE : 0 ≤ ∫ x in ball 0 1, ‖G x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases ht : θ ≤ 1 / 2
  · have hGb := hG.mono_measure (Measure.restrict_mono hs le_rfl)
    have hbound : ∀ᵐ x ∂volume.restrict (ball 0 θ),
        ‖G x‖ ≤ B * lpNorm G 2 (volume.restrict (ball 0 1)) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he,
        ae_restrict_mem measurableSet_ball] with x hx hxB
      rw [hx]
      exact hb x ((ball_subset_ball ht) hxB)
    calc
      _ ≤ (B * lpNorm G 2 (volume.restrict (ball 0 1))) ^ 2 *
          volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) θ) :=
        frozen_integral_sq_le_of_ae_norm_bound hGb (mul_nonneg hB lpNorm_nonneg) hbound
      _ = (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
          θ ^ n * ∫ x in ball 0 1, ‖G x‖ ^ 2 := by
        rw [frozen_real_volume_ball hn _ hθ.le, mul_pow, lpNorm_two_sq_eq_integral_norm_sq hG]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le _)) hE
  · have hpow := frozen_half_radius_power n (le_of_lt (lt_of_not_ge ht))
    calc
      _ ≤ ∫ x in ball 0 1, ‖G x‖ ^ 2 :=
        setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
          (Eventually.of_forall hs)
      _ ≤ (2 : ℝ) ^ n * θ ^ n * ∫ x in ball 0 1, ‖G x‖ ^ 2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hθ.le _)) hE

/-- A derivative supremum estimate supplies the centered oscillation decay. -/
theorem frozen_oscillation_decay_of_unit_derivative_bound {n : ℕ} (hn : 0 < n)
    {G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict (ball 0 1)))
    (he : G =ᵐ[volume.restrict (ball 0 1)] F)
    (hF : ∀ x ∈ ball 0 (1 / 2 : ℝ), DifferentiableAt ℝ F x)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball 0 (1 / 2 : ℝ), ‖fderiv ℝ F x‖ ≤
      B * lpNorm (fun y => G y - ⨍ z in ball 0 1, G z) 2 (volume.restrict (ball 0 1)))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ x in ball 0 θ, ‖G x - ⨍ y in ball 0 θ, G y‖ ^ 2) ≤
      max (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        ((2 : ℝ) ^ (n + 2)) * θ ^ (n + 2) *
          ∫ x in ball 0 1, ‖G x - ⨍ y in ball 0 1, G y‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) θ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  let c := ⨍ y in ball 0 1, G y
  let H := fun y => G y - c
  have hH : MemLp H 2 (volume.restrict (ball 0 1)) := hG.sub (memLp_const c)
  have hs : ball (0 : EuclideanSpace ℝ (Fin n)) θ ⊆ ball 0 1 := ball_subset_ball hθ1.le
  have hGb := hG.mono_measure (Measure.restrict_mono hs le_rfl)
  have hE : 0 ≤ ∫ x in ball 0 1, ‖H x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  change _ ≤ _ * θ ^ (n + 2) * ∫ x in ball 0 1, ‖H x‖ ^ 2
  by_cases ht : θ ≤ 1 / 2
  · have hbound : ∀ᵐ x ∂volume.restrict (ball 0 θ),
        ‖G x - F 0‖ ≤ (B * lpNorm H 2 (volume.restrict (ball 0 1))) * θ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he,
        ae_restrict_mem measurableSet_ball] with x hx hxB
      rw [hx]
      have hm := Convex.norm_image_sub_le_of_norm_fderiv_le hF hb
        (convex_ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
        (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) ((ball_subset_ball ht) hxB)
      simp only [sub_zero] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hxB).le
        (mul_nonneg hB lpNorm_nonneg))
    calc
      _ ≤ ∫ x in ball 0 θ, ‖G x - F 0‖ ^ 2 := frozen_integral_norm_sub_average_le hGb (F 0)
      _ ≤ ((B * lpNorm H 2 (volume.restrict (ball 0 1))) * θ) ^ 2 *
          volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) θ) :=
        frozen_integral_sq_le_of_ae_norm_bound (hGb.sub (memLp_const (F 0)))
          (mul_nonneg (mul_nonneg hB lpNorm_nonneg) hθ.le) hbound
      _ = (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
          θ ^ (n + 2) * ∫ x in ball 0 1, ‖H x‖ ^ 2 := by
        rw [frozen_real_volume_ball hn _ hθ.le, mul_pow, mul_pow,
          lpNorm_two_sq_eq_integral_norm_sq hH, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le _)) hE
  · have hpow := frozen_half_radius_power (n + 2) (le_of_lt (lt_of_not_ge ht))
    calc
      _ ≤ ∫ x in ball 0 θ, ‖H x‖ ^ 2 := frozen_integral_norm_sub_average_le hGb c
      _ ≤ ∫ x in ball 0 1, ‖H x‖ ^ 2 :=
        setIntegral_mono_set ((memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH)
          (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hs)
      _ ≤ (2 : ℝ) ^ (n + 2) * θ ^ (n + 2) * ∫ x in ball 0 1, ‖H x‖ ^ 2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hθ.le _)) hE

end LiquidDrop
