import NoCompromise.Sobolev.Extension

/-! # The value bound for a compact test on the half disk -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped NNReal Topology Gradient
namespace LiquidDrop

/-- A test supported inside the half disk has sup norm at most a global bound
for its gradient, by comparison with a point on the boundary of the disk. -/
lemma approxHarmonic_test_value_le_gradient_bound
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hsζ : tsupport ζ ⊆ ball 0 (1 / 2))
    {M : ℝ} (hM : 0 ≤ M) (hgrad : ∀ p, ‖gradient ζ p‖ ≤ M) :
    ∀ p, |ζ p| ≤ M := by
  have hd (p) : ‖fderiv ℝ ζ p‖ ≤ M := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hgrad p
  have hl : LipschitzWith ⟨M, hM⟩ ζ :=
    lipschitzWith_of_nnnorm_fderiv_le (hζ.differentiable one_ne_zero)
      (fun p => NNReal.coe_le_coe.mp (hd p))
  let q : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1 / 2)
  have hq : ‖q‖ = 1 / 2 := by simp [q]
  have hqzero : ζ q = 0 := image_eq_zero_of_notMem_tsupport (by
    intro ht
    have hh := mem_ball_zero_iff.mp (hsζ ht)
    rw [hq] at hh
    exact (lt_irrefl _ hh))
  intro p
  by_cases hp : p ∈ tsupport ζ
  · have hpn := mem_ball_zero_iff.mp (hsζ hp)
    have hdist : dist p q ≤ 1 := by
      have hh := dist_le_norm_add_norm p q
      rw [hq] at hh
      linarith
    calc
      |ζ p| = dist (ζ p) (ζ q) := by simp [hqzero]
      _ ≤ M * dist p q := hl.dist_le_mul p q
      _ ≤ M := mul_le_of_le_one_right hM hdist
  · rw [image_eq_zero_of_notMem_tsupport hp, abs_zero]
    exact hM

end LiquidDrop
