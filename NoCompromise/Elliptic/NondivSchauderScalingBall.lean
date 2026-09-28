import NoCompromise.Elliptic.NondivSchauderBootstrap
import NoCompromise.Elliptic.NondivSchauderScalingEquation
import NoCompromise.Elliptic.NondivSchauderScalingInverse

/-!
# The bootstrap on every contracting interior ball

The constant remains fixed before the center, radius, coefficients, solution,
and source. Only the explicit radius factor r⁻³ is introduced by scaling.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_holder_comp_ballScaling {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {α : ℝ} (hα : 0 ≤ α) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : HasFiniteHolderNormOn α f (ball c r)) :
    HasFiniteHolderNormOn α (f ∘ frozenBallScaling c hr) (ball 0 1) ∧
      holderNorm α (f ∘ frozenBallScaling c hr) (ball 0 1) ≤ holderNorm α f (ball c r) := by
  apply nondiv_holder_comp_contraction hα hf (quasilinear_ballScaling_maps_unit c hr)
  intro x hx y hy
  rw [← dist_eq_norm, quasilinear_ballScaling_dist c x y hr, dist_eq_norm]
  exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)

/-- Uniform translated/scaled nondivergence bootstrap, with an explicit inverse
cube radius factor and no dependence on the solution in the constant. -/
theorem nondiv_schauder_c1_ball {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {α lam cap M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball c r) → HasFiniteHolderNormOn α b (ball c r) →
      HasC1HolderOn α z (ball c r) → HasFiniteHolderNormOn α f (ball c r) →
      nondivC1HolderNorm α A (ball c r) ≤ M → holderNorm α b (ball c r) ≤ M →
      (∀ x ∈ ball c r, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball c r, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball c r) →
      HasC2HolderOn α z (ball c (r / 2)) ∧
        schauderC2HolderNorm α z (ball c (r / 2)) ≤ C * (r⁻¹) ^ 3 *
          (nondivC1HolderNorm α z (ball c r) + holderNorm α f (ball c r)) := by
  obtain ⟨C, hC, hbstr⟩ := nondiv_schauder_c1_data hn0 hn hα hα1 hlam hlamcap hM
  refine ⟨C, hC, ?_⟩
  intro c r hr hr1 A b z f hA hb hz hf hbA hbb hcap hell he
  let e := frozenBallScaling c hr
  have hm := quasilinear_ballScaling_maps_unit c hr
  obtain ⟨hAc, hAcb⟩ := nondiv_c1Holder_comp_ballScaling hα.le c hr hr1 hA
  obtain ⟨hzc, hzcb⟩ := nondiv_c1Holder_comp_ballScaling hα.le c hr hr1 hz
  obtain ⟨hbc, hbcb⟩ := nondiv_holder_comp_ballScaling hα.le c hr hr1 hb
  obtain ⟨hfc, hfcb⟩ := nondiv_holder_comp_ballScaling hα.le c hr hr1 hf
  obtain ⟨hbs, hbsb⟩ := nondiv_holder_const_smul hbc r
  obtain ⟨hfs, hfsb⟩ := nondiv_holder_const_smul hfc (r ^ 2)
  have hbBound : holderNorm α (fun x => r • b (e x)) (ball 0 1) ≤ holderNorm α b (ball c r) := by
    apply hbsb.trans
    rw [Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left hbcb hr.le).trans
      ((mul_le_mul_of_nonneg_right hr1 hb.norm_nonneg).trans_eq (one_mul _))
  have hfBound : holderNorm α (fun x => r ^ 2 * f (e x)) (ball 0 1) ≤
      holderNorm α f (ball c r) := by
    apply hfsb.trans
    rw [Real.norm_of_nonneg (sq_nonneg r)]
    apply (mul_le_mul_of_nonneg_left hfcb (sq_nonneg r)).trans
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hr2 hf.norm_nonneg).trans_eq (one_mul _)
  have hEq := he.comp_nondivBallScaling c hr hA.contDiff (hb.nondiv_continuousOn hα)
    hz.contDiff (hf.nondiv_continuousOn hα)
  obtain ⟨hscaled, hbscaled⟩ := hbstr (A ∘ e) (fun x => r • b (e x))
    (z ∘ e) (fun x => r ^ 2 * f (e x)) hAc hbs hzc hfs
    (hAcb.trans hbA) (hbBound.trans hbb)
    (fun x hx => hcap _ (hm hx)) (fun x hx v => hell _ (hm hx) v) hEq
  obtain ⟨hback, hbback⟩ := nondiv_c2Holder_comp_ballScaling_symm hα.le hα1.le c hr hr1 hscaled
  have heq : (z ∘ e) ∘ e.symm = z := by
    funext x
    simp only [Function.comp_apply, e.apply_symm_apply]
  rw [heq] at hback hbback
  refine ⟨hback, hbback.trans ?_⟩
  have hbtotal := hbscaled.trans
    (mul_le_mul_of_nonneg_left (add_le_add hzcb hfBound) hC.le)
  convert mul_le_mul_of_nonneg_left hbtotal (by positivity : 0 ≤ (r⁻¹) ^ 3) using 1
  ring

end LiquidDrop
