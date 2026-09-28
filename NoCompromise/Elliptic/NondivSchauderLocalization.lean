import NoCompromise.Elliptic.NondivSchauderScalingNorm

/-!
# Uniform local norms control the whole interior set

Close pairs lie in one supplied local ball. Distant pairs are controlled by the
uniform norm. This elementary split keeps the localization loss polynomial and
will turn local Schauder bounds into a nested-radius estimate.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasC2HolderOn.nondiv_mono {n : ℕ} {α : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hf : HasC2HolderOn α f U) (hVU : V ⊆ U) :
    HasC2HolderOn α f V ∧ schauderC2HolderNorm α f V ≤ schauderC2HolderNorm α f U := by
  obtain ⟨h₀, hb₀⟩ := schauder_holder_mono hf.function_holder hVU
  obtain ⟨h₁, hb₁⟩ := schauder_holder_mono hf.derivative_holder hVU
  obtain ⟨h₂, hb₂⟩ := schauder_holder_mono hf.hessian_holder hVU
  exact ⟨⟨hf.contDiff.mono hVU, h₀, h₁, h₂⟩, add_le_add (add_le_add hb₀ hb₁) hb₂⟩

/-- Uniform local Hölder norms give a full norm on the carrier, costing only δ⁻¹
for 0<α≤1 and δ≤1. The carrier need not be open or compact. -/
theorem nondiv_holder_local_ball_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α δ B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : 0 ≤ B) {f : E → F} {S : Set E}
    (hf : ∀ x ∈ S, HasFiniteHolderNormOn α f (ball x δ) ∧ holderNorm α f (ball x δ) ≤ B) :
    HasFiniteHolderNormOn α f S ∧ holderNorm α f S ≤ 3 * δ⁻¹ * B := by
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hv (x) (hx : x ∈ S) : ‖f x‖ ≤ B :=
    ((hf x hx).1.nondiv_norm_le (mem_ball_self hδ)).trans (hf x hx).2
  have hq (x) (hx : x ∈ S) (y) (hy : y ∈ S) :
      ‖f x - f y‖ / ‖x - y‖ ^ α ≤ 2 * δ⁻¹ * B := by
    by_cases hnear : ‖x - y‖ < δ
    · have hyx : y ∈ ball x δ := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hnear
      have hb := ((schauder_holder_quotient_le (hf x hx).1 (mem_ball_self hδ) hyx).trans
        (show holderSeminorm α f (ball x δ) ≤ holderNorm α f (ball x δ) from
          le_add_of_nonneg_left (holderUniformNorm_nonneg (hf x hx).1.uniform_bounded))).trans
        (hf x hx).2
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hinv hB])
    · have hdist : δ ≤ ‖x - y‖ := le_of_not_gt hnear
      have hδpow : δ ≤ δ ^ α := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hα1
      have hp : δ ≤ ‖x - y‖ ^ α := hδpow.trans
        (Real.rpow_le_rpow hδ.le hdist hα.le)
      have hnum : ‖f x - f y‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hv x hx, hv y hy])
      calc
        _ ≤ 2 * B / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (norm_nonneg _) α)
        _ ≤ 2 * B / δ := div_le_div_of_nonneg_left (by positivity) hδ hp
        _ = _ := by ring
  have hsem : 0 ≤ 2 * δ⁻¹ * B := by positivity
  refine ⟨HasFiniteHolderNormOn.of_bounds hB hsem hv hq,
    (holderNorm_le hB hsem hv hq).trans ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_right hinv hB]

/-- Uniform local C²,α norms assemble actual C²,α on the entire carrier. -/
theorem nondiv_c2Holder_local_ball_bound {n : ℕ} {α δ B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ x ∈ S, HasC2HolderOn α f (ball x δ) ∧ schauderC2HolderNorm α f (ball x δ) ≤ B) :
    HasC2HolderOn α f S ∧ schauderC2HolderNorm α f S ≤ 9 * δ⁻¹ * B := by
  have h₀ (x) (hx : x ∈ S) : HasFiniteHolderNormOn α f (ball x δ) ∧
      holderNorm α f (ball x δ) ≤ B := by
    refine ⟨(hf x hx).1.function_holder, ?_⟩
    have hb := (hf x hx).2
    have h₁ := (hf x hx).1.derivative_holder.norm_nonneg
    have h₂ := (hf x hx).1.hessian_holder.norm_nonneg
    dsimp [schauderC2HolderNorm] at hb
    linarith only [hb, h₁, h₂]
  have h₁ (x) (hx : x ∈ S) : HasFiniteHolderNormOn α (fderiv ℝ f) (ball x δ) ∧
      holderNorm α (fderiv ℝ f) (ball x δ) ≤ B := by
    refine ⟨(hf x hx).1.derivative_holder, ?_⟩
    have hb := (hf x hx).2
    have h₀ := (hf x hx).1.function_holder.norm_nonneg
    have h₂ := (hf x hx).1.hessian_holder.norm_nonneg
    dsimp [schauderC2HolderNorm] at hb
    linarith only [hb, h₀, h₂]
  have h₂ (x) (hx : x ∈ S) : HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ f)) (ball x δ) ∧
      holderNorm α (fderiv ℝ (fderiv ℝ f)) (ball x δ) ≤ B := by
    refine ⟨(hf x hx).1.hessian_holder, ?_⟩
    have hb := (hf x hx).2
    have h₀ := (hf x hx).1.function_holder.norm_nonneg
    have h₁ := (hf x hx).1.derivative_holder.norm_nonneg
    dsimp [schauderC2HolderNorm] at hb
    linarith only [hb, h₀, h₁]
  obtain ⟨hF₀, hb₀⟩ := nondiv_holder_local_ball_bound hα hα1 hδ hδ1 hB h₀
  obtain ⟨hF₁, hb₁⟩ := nondiv_holder_local_ball_bound hα hα1 hδ hδ1 hB h₁
  obtain ⟨hF₂, hb₂⟩ := nondiv_holder_local_ball_bound hα hα1 hδ hδ1 hB h₂
  refine ⟨⟨?_, hF₀, hF₁, hF₂⟩, ?_⟩
  · intro x hx
    exact ((hf x hx).1.contDiff.contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_self hδ))).contDiffWithinAt
  · dsimp [schauderC2HolderNorm]
    linarith only [hb₀, hb₁, hb₂]

end LiquidDrop
