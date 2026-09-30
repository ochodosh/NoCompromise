module

public import NoCompromise.Elliptic.NondivSchauderNorm

@[expose] public section

/-!
# Coefficient divergence and the scalar datum

For the operator convention `(A v)ᵢ = Σⱼ aᵢⱼ vⱼ`, coefficient divergence has
j-th component `Σᵢ ∂ᵢaᵢⱼ`. Thus the nondivergence equation becomes
`div(A ∇z) = f + ⟪div A - b, ∇z⟫`. This file proves the actual Hölder bounds
for that datum, without assuming second derivatives of z.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasFiniteHolderNormOn.nondiv_continuousOn {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} (hα : 0 < α) {f : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) : ContinuousOn f U := by
  intro x hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun y : E => holderSeminorm α f U * ‖y - x‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.sub continuous_const).norm)
  have ht : Tendsto (fun y : E => holderSeminorm α f U * ‖y - x‖ ^ α)
      (𝓝[U] x) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  apply squeeze_zero' (Eventually.of_forall (fun y => _root_.norm_nonneg (f y - f x))) _ ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hf.nondiv_norm_sub_le hy hx

lemma nondiv_holder_sub {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f g : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U) :
    HasFiniteHolderNormOn α (fun x => f x - g x) U ∧
      holderNorm α (fun x => f x - g x) U ≤ holderNorm α f U + holderNorm α g U := by
  obtain ⟨hn, hnb⟩ := nondiv_holder_comp_clm hg (-(ContinuousLinearMap.id ℝ F))
  have hL : ‖-(ContinuousLinearMap.id ℝ F)‖ ≤ 1 := by
    simpa only [norm_neg] using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)
  have hn' : HasFiniteHolderNormOn α (fun x => -g x) U := by simpa using! hn
  obtain ⟨ha, hab⟩ := schauder_holder_add hf hn'
  have hb : holderNorm α (fun x => -g x) U ≤ holderNorm α g U := by
    apply le_trans (by simpa using! hnb)
    simpa only [norm_neg] using
      (mul_le_mul_of_nonneg_right hL hg.norm_nonneg).trans_eq (one_mul _)
  exact ⟨by simpa only [sub_eq_add_neg] using ha,
    (by simpa only [sub_eq_add_neg] using hab.trans (add_le_add le_rfl hb))⟩

lemma nondiv_holder_inner {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {α : ℝ} {f g : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U) :
    HasFiniteHolderNormOn α (fun x => inner ℝ (f x) (g x)) U ∧
      holderNorm α (fun x => inner ℝ (f x) (g x)) U ≤
        3 * holderNorm α f U * holderNorm α g U := by
  obtain ⟨hh, hb⟩ := nondiv_holder_bilinear hf hg (innerSL ℝ)
  have hL : ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 1 :=
    (toDualMap ℝ F).norm_toContinuousLinearMap_le
  refine ⟨hh, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 3)) hf.norm_nonneg) hg.norm_nonneg
  simpa only [mul_one] using h

/-- The fixed contraction of a derivative of an operator field: transpose each
coordinate derivative before evaluating it on the same coordinate vector. -/
def nondivCoefficientContraction (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n,
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1)) ∘L
      ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.apply ℝ
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (EuclideanSpace.single i 1))

lemma nondivCoefficientContraction_apply {n : ℕ}
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    nondivCoefficientContraction n D =
      ∑ i : Fin n, (D (EuclideanSpace.single i 1)).adjoint (EuclideanSpace.single i 1) := by
  simp only [nondivCoefficientContraction, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

lemma norm_nondivCoefficientContraction_le (n : ℕ) :
    ‖nondivCoefficientContraction n‖ ≤ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg n)
  intro D
  rw [nondivCoefficientContraction_apply]
  calc
    _ ≤ ∑ i : Fin n,
        ‖(D (EuclideanSpace.single i 1)).adjoint (EuclideanSpace.single i 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖D‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := ((D (EuclideanSpace.single i 1)).adjoint.le_opNorm
        (EuclideanSpace.single i 1)).trans (mul_le_mul_of_nonneg_right
          (show ‖(D (EuclideanSpace.single i 1)).adjoint‖ ≤ ‖D‖ *
            ‖EuclideanSpace.single i (1 : ℝ)‖ by
              rw [LinearIsometryEquiv.norm_map]
              exact D.le_opNorm _) (norm_nonneg _))
      simpa only [PiLp.norm_single, norm_one, mul_one] using h
    _ = n * ‖D‖ := by simp

/-- The j-th component is the sum of ∂ᵢaᵢⱼ, for the usual row-column convention. -/
def nondivCoefficientDivergence {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  nondivCoefficientContraction n (fderiv ℝ A x)

lemma nondivCoefficientDivergence_holder {n : ℕ} {α : ℝ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hA : HasC1HolderOn α A U) :
    HasFiniteHolderNormOn α (nondivCoefficientDivergence A) U ∧
      holderNorm α (nondivCoefficientDivergence A) U ≤ n * nondivC1HolderNorm α A U := by
  obtain ⟨hh, hb⟩ := nondiv_holder_comp_clm hA.derivative_holder (nondivCoefficientContraction n)
  exact ⟨hh, hb.trans (mul_le_mul (norm_nondivCoefficientContraction_le n)
    hA.derivative_norm_le hA.derivative_holder.norm_nonneg (Nat.cast_nonneg n))⟩

/-- The scalar source obtained after rewriting a nondivergence equation in divergence form. -/
def nondivDivergenceSource {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + inner ℝ (nondivCoefficientDivergence A x - b x) (gradient z x)

/-- The divergence-form source is genuinely Hölder, with a bound depending only
on the stated C¹,α coefficients, C⁰,α drift and source, and C¹,α solution norm. -/
theorem nondivDivergenceSource_holder {n : ℕ} {α : ℝ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U) :
    HasFiniteHolderNormOn α (nondivDivergenceSource A b z f) U ∧
      holderNorm α (nondivDivergenceSource A b z f) U ≤ holderNorm α f U +
        3 * (n * nondivC1HolderNorm α A U + holderNorm α b U) * nondivC1HolderNorm α z U := by
  obtain ⟨hD, hDb⟩ := nondivCoefficientDivergence_holder hA
  obtain ⟨hB, hBb⟩ := nondiv_holder_sub hD hb
  obtain ⟨hZ, hZb⟩ := hz.gradient_holder
  obtain ⟨hP, hPb⟩ := nondiv_holder_inner hB hZ
  obtain ⟨hS, hSb⟩ := schauder_holder_add hf hP
  refine ⟨hS, hSb.trans (add_le_add le_rfl (hPb.trans ?_))⟩
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hBb.trans (add_le_add hDb le_rfl)) (by norm_num)
  · exact hZb.trans hz.derivative_norm_le
  · exact hZ.norm_nonneg
  · have hAN := hA.norm_nonneg
    have hbN := hb.norm_nonneg
    positivity


lemma nondivCoefficientContraction_component {n : ℕ}
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    nondivCoefficientContraction n D j =
      ∑ i : Fin n, (D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) i := by
  rw [nondivCoefficientContraction_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := (D (EuclideanSpace.single i 1)).adjoint_inner_left
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  simpa only [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
    conj_trivial, one_mul] using h

lemma nondivCoefficientContraction_smulRight {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    nondivCoefficientContraction n (p.smulRight A) =
      A.adjoint ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm p) := by
  apply PiLp.ext
  intro j
  rw [nondivCoefficientContraction_component]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, PiLp.smul_apply, smul_eq_mul]
  calc
    _ = inner ℝ ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm p)
        (A (EuclideanSpace.single j 1)) := by
      simp only [PiLp.inner_apply, Real.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hp := (toDual ℝ (EuclideanSpace ℝ (Fin n))).apply_symm_apply p
      have hp' := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i 1)) hp
      simp only [toDual_apply_apply, EuclideanSpace.inner_single_right,
        conj_trivial, one_mul] at hp'
      rw [hp']
    _ = _ := by
      rw [← A.adjoint_inner_left]
      simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-- The exact coefficient product rule behind the distributional rewriting. -/
lemma nondivCoefficientDivergence_smul {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hA : DifferentiableAt ℝ A x) (hφ : DifferentiableAt ℝ φ x) :
    nondivCoefficientDivergence (fun y => φ y • A y) x =
      φ x • nondivCoefficientDivergence A x + (A x).adjoint (gradient φ x) := by
  simp only [nondivCoefficientDivergence, fderiv_fun_smul hφ hA, map_add, map_smul,
    nondivCoefficientContraction_smulRight, gradient]

end LiquidDrop
