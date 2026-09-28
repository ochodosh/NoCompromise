import NoCompromise.Elliptic.QuasilinearEquation

/-! Quantitative control of the actual linearized coefficient DA(∇f). The
averaged secant coefficients converge uniformly to it without requiring any
second derivatives of f. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma quasilinear_linearized_coefficient_holder {n : ℕ}
    {A F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B H a : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hF : ∀ x ∈ U, F x ∈ closedBall 0 M)
    (hhold : ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ H * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (hy : y ∈ U) :
    ‖fderiv ℝ A (F x) - fderiv ℝ A (F y)‖ ≤ (B * H) * dist x y ^ a := by
  apply (quasilinear_fderiv_lipschitz_bound hA hb (hF x hx) (hF y hy)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hhold x hx y hy) hB

/-- A uniform error estimate for the actual averaged coefficient, valid for
both signs of the step. -/
lemma quasilinearCoefficientField_error_le {n : ℕ}
    {A F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B H a : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hF : ∀ x ∈ U, F x ∈ closedBall 0 M)
    (hhold : ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ H * dist x y ^ a)
    (i : Fin n) (h : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (hxshift : x + h • EuclideanSpace.single i 1 ∈ U) :
    ‖quasilinearCoefficientField A F i h x - fderiv ℝ A (F x)‖ ≤ (B * H) * ‖h‖ ^ a := by
  apply (quasilinearSecantCoefficient_sub_fderiv_le hA hB hb
    (hF x hx) (hF _ hxshift)).trans
  have ht := mul_le_mul_of_nonneg_left (hhold _ hxshift x hx) hB
  simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single,
    norm_one, mul_one, mul_assoc] using ht

end LiquidDrop
