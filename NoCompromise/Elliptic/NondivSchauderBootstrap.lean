module

public import NoCompromise.Elliptic.NondivSchauderDerivativeEquation
public import NoCompromise.Elliptic.NondivSchauderClassical
public import NoCompromise.Elliptic.NondivSchauderNormalize

@[expose] public section

/-!
# Actual C²,α regularity for the nondivergence equation

This completes the difference-quotient bootstrap from the blueprint's actual
C¹,α distributional solution. The constant is fixed before the solution and
right-hand side. The sharper bound using only L∞ is a separate freezing step.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondivDerivativeDatum_norm_le {n : ℕ} {α M : ℝ} (hM : 0 ≤ M)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U)
    (hbA : nondivC1HolderNorm α A U ≤ M) (hbb : holderNorm α b U ≤ M) (i : Fin n) :
    holderNorm α (nondivDerivativeDatum A b z f i) U ≤
      (1 + 3 * ((n : ℝ) + 2) * M) *
        (nondivC1HolderNorm α z U + holderNorm α f U) := by
  apply (nondivDerivativeDatum_holder hA hb hz hf i).2.trans
  apply (add_le_add (nondivDivergenceSource_holder hA hb hz hf).2 le_rfl).trans
  have hD := hA.derivative_norm_le.trans hbA
  have hDz := hz.gradient_holder.2.trans hz.derivative_norm_le
  have hterm : 3 * holderNorm α (fderiv ℝ A) U * holderNorm α (gradient z) U ≤
      3 * M * nondivC1HolderNorm α z U :=
    mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hDz
      hz.gradient_holder.1.norm_nonneg (by positivity)
  have hcoef : (n : ℝ) * nondivC1HolderNorm α A U + holderNorm α b U ≤
      ((n : ℝ) + 1) * M := by nlinarith
  have hterm' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (by norm_num : (0 : ℝ) ≤ 3)) hz.norm_nonneg
  nlinarith [hz.norm_nonneg, hf.norm_nonneg,
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * ((n : ℝ) + 2)) hM) hf.norm_nonneg]

/-- The first blueprint nondivergence Schauder estimate, including actual C²,α
regularity. The constant depends only on the displayed fixed coefficient bounds,
ellipticity, exponent, and dimension, and is chosen before A,b,z,f. -/
theorem nondiv_schauder_c1_data {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {α lam cap M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasFiniteHolderNormOn α b (ball 0 1) →
      HasC1HolderOn α z (ball 0 1) → HasFiniteHolderNormOn α f (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → holderNorm α b (ball 0 1) ≤ M →
      (∀ x ∈ ball 0 (1 : ℝ), ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 (1 : ℝ), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball 0 1) →
      HasC2HolderOn α z (ball 0 (1 / 2)) ∧
        schauderC2HolderNorm α z (ball 0 (1 / 2)) ≤
          C * (nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)) := by
  obtain ⟨Ch, hCh, hder⟩ := nondiv_exists_derivative_equation (n := n) hα hlam hlamcap hM
  let K := 1 + 3 * ((n : ℝ) + 2) * M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Cc, hCc, hcamp⟩ := nondiv_campanato_interior_homogeneous hn0 hn hα hα1
    hlam (hlam.le.trans hlamcap) hM hK (sq_nonneg Ch)
  refine ⟨1 + 2 * (n : ℝ) * Cc, by positivity, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he
  let T := nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)
  have hT : 0 ≤ T := add_nonneg hz.norm_nonneg hf.norm_nonneg
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  let W : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (1 / 2)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hWU : W ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hAhold (x) (hx : x ∈ V) (y) (hy : y ∈ V) :
      ‖A x - A y‖ ≤ M * dist x y ^ α := by
    apply (hA.function_holder.nondiv_norm_sub_le (hVU hx) (hVU hy)).trans
    rw [dist_eq_norm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    exact (le_add_of_nonneg_left
      (holderUniformNorm_nonneg hA.function_holder.uniform_bounded)).trans
        (hA.function_norm_le.trans hbA)
  have hcoord (i : Fin n) :
      ContDiffOn ℝ 1 (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) W ∧
        (∀ x ∈ W, ‖gradient (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) x‖ ≤ Cc * T) ∧
        ∀ x ∈ W, ∀ y ∈ W,
          ‖gradient (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) x -
            gradient (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) y‖ ≤
              Cc * T * dist x y ^ α := by
    obtain ⟨F, hF, hEq, hFb⟩ := hder A b z f hA hb hz hf hbA hbb hcap hell he i
    have hG := (nondivDerivativeDatum_holder hA hb hz hf i).1
    have hGb := nondivDerivativeDatum_norm_le hM hA hb hz hf hbA hbb i
    have hGhold (x) (hx : x ∈ V) (y) (hy : y ∈ V) :
        ‖nondivDerivativeDatum A b z f i x - nondivDerivativeDatum A b z f i y‖ ≤
          K * T * dist x y ^ α := by
      apply (hG.nondiv_norm_sub_le (hVU hx) (hVU hy)).trans
      rw [dist_eq_norm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
      exact (le_add_of_nonneg_left (holderUniformNorm_nonneg hG.uniform_bounded)).trans hGb
    have henergy : (∫ x in V, ‖F x‖ ^ 2) ≤ Ch ^ 2 * T ^ 2 := by
      rw [← lpNorm_two_sq_eq_integral_norm_sq hF.memLp_gradient, ← mul_pow]
      exact pow_le_pow_left₀ lpNorm_nonneg hFb 2
    exact hcamp A (nondivDerivativeDatum A b z f i) F
      (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) T hT
      (hA.contDiff.continuousOn.mono hVU) ((hG.nondiv_continuousOn hα).mono hVU)
      (((hz.derivative_holder.nondiv_continuousOn hα).clm_apply continuousOn_const).mono hVU)
      (fun x hx => hcap x (hVU hx))
      (fun x hx v => by simpa only [real_inner_comm] using hell x (hVU hx) v)
      hAhold hGhold hF hEq henergy
  obtain ⟨hz₂, _, hH, hHb, _, _⟩ := nondiv_hessian_holder_of_coordinate_derivatives
    (mul_nonneg hCc.le hT) isOpen_ball (hz.contDiff.mono hWU) (fun i => (hcoord i).1)
    (fun i => (hcoord i).2.1)
    (fun i x hx y hy => by simpa only [dist_eq_norm] using (hcoord i).2.2 x hx y hy)
  obtain ⟨hzW, hzWb⟩ := hz.mono hWU
  refine ⟨⟨hz₂, hzW.function_holder, hzW.derivative_holder, hH⟩, ?_⟩
  change nondivC1HolderNorm α z W + holderNorm α (fderiv ℝ (fderiv ℝ z)) W ≤
    (1 + 2 * (n : ℝ) * Cc) * T
  have ht : nondivC1HolderNorm α z W ≤ T :=
    hzWb.trans (le_add_of_nonneg_right hf.norm_nonneg)
  nlinarith only [ht, hHb]

end LiquidDrop
