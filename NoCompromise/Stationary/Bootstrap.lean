module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

namespace LiquidDrop

/-- The matrix entries of the planar minimal-surface coefficient. -/
noncomputable def mcCoefficient (p : EuclideanSpace ℝ (Fin 2)) : Fin 2 → Fin 2 → ℝ :=
  fun i j => (if i = j then 1 else 0) / Real.sqrt (1 + ‖p‖ ^ 2) -
    p i * p j / (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 3

/-- The quadratic form associated with the minimal-surface coefficient. -/
noncomputable def mcQuadratic (p ξ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖ξ‖ ^ 2 / Real.sqrt (1 + ‖p‖ ^ 2) -
    (inner ℝ p ξ) ^ 2 / (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 3

private theorem mc_inner_sq_le (p ξ : EuclideanSpace ℝ (Fin 2)) :
    (inner ℝ p ξ) ^ 2 ≤ ‖p‖ ^ 2 * ‖ξ‖ ^ 2 := by
  simpa only [sq_abs, mul_pow] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      (abs_real_inner_le_norm p ξ)

private theorem mc_lower (p ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖ξ‖ ^ 2 / (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 3 ≤ mcQuadratic p ξ := by
  have hbase : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.2 hbase
  have hsq := Real.sq_sqrt hbase.le
  have hi := mc_inner_sq_le p ξ
  unfold mcQuadratic
  apply (div_le_iff₀ (pow_pos hs 3)).2
  field_simp
  nlinarith

/-- The quadratic form is the one built from the matrix entries `mcCoefficient`. -/
theorem mcQuadratic_eq_sum (p ξ : EuclideanSpace ℝ (Fin 2)) :
    mcQuadratic p ξ = ∑ i, ∑ j, mcCoefficient p i j * ξ i * ξ j := by
  have hnorm : ‖ξ‖ ^ 2 = ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, abs_mul_abs_self, pow_two]
  have hinner : (inner ℝ p ξ : ℝ) = p 0 * ξ 0 + p 1 * ξ 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  have hs : (0 : ℝ) < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  unfold mcQuadratic mcCoefficient
  rw [hnorm, hinner]
  norm_num [Fin.sum_univ_two]
  field_simp
  ring

/-- Uniform ellipticity with the explicit constant `(1 + M²)^(-3/2)`. -/
theorem mcCoefficient_elliptic {M : ℝ} (hM : 0 ≤ M) :
    ∃ lam > 0, ∀ p : EuclideanSpace ℝ (Fin 2), ‖p‖ ≤ M →
      ∀ ξ : EuclideanSpace ℝ (Fin 2), lam * ‖ξ‖ ^ 2 ≤ mcQuadratic p ξ := by
  refine ⟨(1 + M ^ 2) ^ (-(3 / 2 : ℝ)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro p hp ξ
  have hbase : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hMbase : 0 < 1 + M ^ 2 := by positivity
  have hle : 1 + ‖p‖ ^ 2 ≤ 1 + M ^ 2 := by
    have := (sq_le_sq₀ (norm_nonneg p) hM).2 hp
    linarith
  have hpow : (1 + M ^ 2) ^ (-(3 / 2 : ℝ)) ≤
      (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_nonpos hbase hle (by norm_num)
  have heq : (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) =
      1 / (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hbase.le,
      show (1 / (2 : ℝ)) * (3 : ℕ) = (3 / 2 : ℝ) by norm_num,
      Real.rpow_neg hbase.le]
    simp [one_div]
  calc
    _ ≤ (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ = ‖ξ‖ ^ 2 / (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 3 := by rw [heq]; ring
    _ ≤ mcQuadratic p ξ := mc_lower p ξ

/-- The minimal-surface quadratic form has upper bound one. -/
theorem mcCoefficient_bound : ∀ p ξ : EuclideanSpace ℝ (Fin 2),
    |mcQuadratic p ξ| ≤ ‖ξ‖ ^ 2 := by
  intro p ξ
  have hbase : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.2 hbase
  have hsone : 1 ≤ Real.sqrt (1 + ‖p‖ ^ 2) := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖p‖])
  have hnonneg : 0 ≤ mcQuadratic p ξ :=
    le_trans (by positivity) (mc_lower p ξ)
  rw [abs_of_nonneg hnonneg]
  unfold mcQuadratic
  have hfirst : ‖ξ‖ ^ 2 / Real.sqrt (1 + ‖p‖ ^ 2) ≤ ‖ξ‖ ^ 2 :=
    div_le_self (sq_nonneg _) hsone
  nlinarith [div_nonneg (sq_nonneg (inner ℝ p ξ)) (pow_pos hs 3).le]

/-- Smooth dependence of every matrix entry on the planar gradient. -/
theorem contDiff_mcCoefficient :
    ContDiff ℝ ⊤ (fun p : EuclideanSpace ℝ (Fin 2) => mcCoefficient p) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  have hs : ContDiff ℝ ⊤ (fun p : EuclideanSpace ℝ (Fin 2) =>
      Real.sqrt (1 + ‖p‖ ^ 2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun p =>
      (by positivity : (1 + ‖p‖ ^ 2 : ℝ) ≠ 0)
  have hcoord (k : Fin 2) : ContDiff ℝ ⊤ (fun p : EuclideanSpace ℝ (Fin 2) => p k) :=
    contDiff_piLp_apply (p := 2)
  unfold mcCoefficient
  apply ContDiff.sub
  · apply ContDiff.div
    · exact contDiff_const
    · exact hs
    · intro p
      positivity
  · apply ContDiff.div
    · exact (hcoord i).mul (hcoord j)
    · exact hs.pow 3
    · intro p
      positivity

end LiquidDrop
