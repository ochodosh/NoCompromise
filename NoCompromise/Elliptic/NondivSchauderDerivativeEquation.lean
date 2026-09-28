import NoCompromise.Elliptic.NondivSchauderHessian
import NoCompromise.Elliptic.NondivSchauderDatumLimit
import NoCompromise.Elliptic.NondivSchauderEquationLimit

/-!
# The genuine differentiated nondivergence equation

The constructed weak second derivative solves the expected divergence equation
with datum g eᵢ−(∂ᵢA)Dz. Its equation follows by the checked weak limit of the
actual difference quotients, not by assuming a derivative of the source.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Actual coordinate derivatives are H¹ solutions of the differentiated
uniformly elliptic equation, with constants fixed before all equation data. -/
theorem nondiv_exists_derivative_equation {n : ℕ} {α lam cap M : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
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
      ∀ i : Fin n, ∃ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) F
          (ball 0 (3 / 4)) ∧
        IsWeakDivergenceEquationOn A F (nondivDerivativeDatum A b z f i) (ball 0 (3 / 4)) ∧
        lpNorm F 2 (volume.restrict (ball 0 (3 / 4))) ≤
          C * (nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)) := by
  obtain ⟨C, hC, hconstruct⟩ := nondiv_exists_coordinate_h1_gradient (n := n)
    hα hlam hlamcap hM
  obtain ⟨Cq, _, hbound⟩ := nondiv_quotient_h1_bound (n := n) hα hlam hlamcap hM
  refine ⟨C, hC, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he i
  obtain ⟨F, hF, hFb, σ, hσ, hw⟩ := hconstruct A b z f hA hb hz hf hbA hbb hcap hell he i
  refine ⟨F, hF, ?_, hFb⟩
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hVW : V ⊆ ball 0 (7 / 8 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  let s (j : ℕ) := nondivQuotientStep (σ j)
  have hs (j : ℕ) : s j ≠ 0 := (nondivQuotientStep_pos (σ j)).ne'
  have hst : Tendsto s atTop (𝓝 0) := tendsto_nondivQuotientStep.comp hσ.tendsto_atTop
  have hseg (j : ℕ) : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (s j • EuclideanSpace.single i 1) ∈ ball 0 (1 : ℝ) :=
    fun _ hx _ ht => nondiv_segment_mem_unitBall i (nondivQuotientStep_small (σ j)) (hVW hx) ht
  have hmap (j : ℕ) : ∀ x ∈ V, x + s j • EuclideanSpace.single i 1 ∈ ball 0 (1 : ℝ) := by
    intro x hx
    simpa only [one_smul] using hseg j x hx 1 (by simp)
  let As (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := A (x + s j • EuclideanSpace.single i 1)
  let Ds (j : ℕ) := coordinateDifferenceQuotient i (s j) (gradient z)
  let Gs (j : ℕ) := nondivQuotientDatum A b z f i (s j)
  let G₀ := nondivDerivativeDatum A b z f i
  have hq (j : ℕ) := hbound A b z f hA hb hz hf hbA hbb hcap hell he i
    (s j) (hs j) (nondivQuotientStep_small (σ j))
  have hEq (j : ℕ) : IsWeakDivergenceEquationOn (As j) (Ds j) (Gs j) V :=
    (nondiv_quotient_equation hα isOpen_ball isOpen_ball isBounded_ball isBounded_ball
      hA hb hz hf he i (hs j) (hseg j)).2
  have hAs (j : ℕ) : ContinuousOn (As j) V :=
    hA.contDiff.continuousOn.comp (continuous_id.add continuous_const).continuousOn (hmap j)
  have hA₀ : ContinuousOn A V := hA.contDiff.continuousOn.mono hVU
  have hbs (j : ℕ) : ∀ᵐ x ∂volume.restrict V, ‖As j x‖ ≤ cap := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hcap _ (hmap j x hx)
  have hb₀ : ∀ᵐ x ∂volume.restrict V, ‖A x‖ ≤ cap := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hcap x (hVU hx)
  have hbDs (j : ℕ) : lpNorm (Ds j) 2 (volume.restrict V) ≤
      Cq * (nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)) :=
    (le_add_of_nonneg_left (lpNorm_nonneg (f := coordinateDifferenceQuotient i (s j) z)
      (p := 2) (μ := volume.restrict V))).trans (hq j).2
  let ε (j : ℕ) := holderNorm α (fderiv ℝ A) (ball 0 1) * ‖s j‖
  have hε (j : ℕ) : 0 ≤ ε j := mul_nonneg hA.derivative_holder.norm_nonneg (norm_nonneg _)
  have htε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, norm_zero, mul_zero] using hst.norm.const_mul
      (holderNorm α (fderiv ℝ A) (ball 0 1))
  have hcoeff (j : ℕ) : ∀ᵐ x ∂volume.restrict V, ‖As j x - A x‖ ≤ ε j := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simpa only [As, ε, norm_smul, PiLp.norm_single, norm_one, mul_one] using
      nondiv_norm_segment_increment_le isOpen_ball hA.contDiff
        (fun y hy => hA.derivative_holder.nondiv_norm_le hy) x
        (s j • EuclideanSpace.single i 1) (hseg j x hx)
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hHGs (j : ℕ) : HasFiniteHolderNormOn α (Gs j) V :=
    (nondivQuotientDatum_holder hα isOpen_ball hA hb hz hf i (hs j) (hseg j)).1
  have hHG₀ : HasFiniteHolderNormOn α G₀ V :=
    (schauder_holder_mono (nondivDerivativeDatum_holder hA hb hz hf i).1 hVU).1
  have hmGs (j : ℕ) : MemLp (Gs j) 2 (volume.restrict V) := by
    apply MemLp.of_bound
      (((hHGs j).nondiv_continuousOn hα).aestronglyMeasurable measurableSet_ball)
      (holderNorm α (Gs j) V)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hHGs j).nondiv_norm_le hx
  have hmG₀ : MemLp G₀ 2 (volume.restrict V) := by
    apply MemLp.of_bound
      ((hHG₀.nondiv_continuousOn hα).aestronglyMeasurable measurableSet_ball)
      (holderNorm α G₀ V)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hHG₀.nondiv_norm_le hx
  have hpow : Tendsto (fun j => ‖s j‖ ^ α) atTop (𝓝 0) := by
    simpa only [norm_zero, Real.zero_rpow hα.ne', Function.comp_def] using!
      (Real.continuous_rpow_const hα.le).continuousAt.tendsto.comp hst.norm
  have hstrong : Tendsto (fun j => eLpNorm (fun x => Gs j x - G₀ x) 2
      (volume.restrict V)) atTop (𝓝 0) := by
    apply nondiv_tendsto_eLpNorm_of_uniform_error
      (hm := fun j => (hmGs j).aestronglyMeasurable.sub hmG₀.aestronglyMeasurable)
      (show Tendsto (fun j =>
        (holderSeminorm α (nondivDivergenceSource A b z f) (ball 0 1) +
          holderSeminorm α (fderiv ℝ A) (ball 0 1) * holderNorm α (gradient z) (ball 0 1)) *
            ‖s j‖ ^ α) atTop (𝓝 0) from by
        simpa only [mul_zero] using hpow.const_mul _)
    intro j
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact nondivQuotientDatum_sub_le hα isOpen_ball hA hb hz hf i (hs j) (hseg j x hx)
  exact nondiv_weakDivergenceEquation_limit
    (fun j => (hAs j).aestronglyMeasurable measurableSet_ball)
    (hA₀.aestronglyMeasurable measurableSet_ball) (fun j => (hq j).1.memLp_gradient)
    hF.memLp_gradient hmGs hmG₀ hbs hb₀ hbDs hε htε hcoeff hw hstrong hEq

end LiquidDrop
