import NoCompromise.Elliptic.BoundaryNondivC2Equation

/-!
# Subtracting a C² extension of the boundary trace

The first step of the proof of `thm:boundary-nondiv` for a nonzero trace subtracts
a C² extension `φ` of the boundary value. This file proves the two facts used:
a C² function satisfies the weak nondivergence equation with its classical
right side, and the weak equation is linear, so `z - φ` solves it with the
difference of the right sides.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The classical nondivergence operator, with `Aᵢⱼ = (A eⱼ)ᵢ` and `∂ᵢ(∂ⱼφ)`. -/
def nondivClassicalOperator
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i *
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)) + inner ℝ (b x) (gradient φ x)

lemma continuousOn_nondivClassicalOperator
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hA : ContinuousOn A U) (hb : ContinuousOn b U)
    (hφ : ContDiffOn ℝ 2 φ U) : ContinuousOn (nondivClassicalOperator A b φ) U := by
  have hDφ : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hG := continuousOn_gradient_of_contDiffOn hU (hφ.of_le (by norm_num))
  apply ContinuousOn.add _ (hb.inner hG)
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  have hj : ContDiffOn ℝ 1 (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) U :=
    hDφ.clm_apply contDiffOn_const
  exact ((EuclideanSpace.proj i).continuous.comp_continuousOn
    (hA.clm_apply continuousOn_const)).mul
      ((hj.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)

/-- A C² function satisfies the weak nondivergence equation whose right side is its
classical nondivergence operator. -/
theorem isWeakNondivergenceEquationOn_of_contDiffOn
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hb : ContinuousOn b U)
    (hφ : ContDiffOn ℝ 2 φ U) :
    IsWeakNondivergenceEquationOn A b φ (nondivClassicalOperator A b φ) U := by
  have hφ1 : ContDiffOn ℝ 1 φ U := hφ.of_le (by norm_num)
  have hDφ : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hGφ : ContDiffOn ℝ 1 (gradient φ) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDφ
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient φ y)) U := hA.clm_apply hGφ
  have hpt : ∀ x ∈ U, divergenceN (fun y => A y (gradient φ y)) x =
      nondivDivergenceSource A b φ (nondivClassicalOperator A b φ) x := by
    intro x hx
    have hdG := (hGφ.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
    have hpartial (i j : Fin 3) :
        fderiv ℝ (gradient φ) x (EuclideanSpace.single i 1) j =
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) := by
      have he' : (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) =
          fun y => gradient φ y j :=
        funext fun y => (gradient_apply_eq_fderiv_single φ y j).symm
      rw [he']
      change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient φ) x _
      rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
      rfl
    have hdA := (hA.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
    have hp := boundary_neumann_c2_divergence_product hdA hdG
      (differentiableAt_const (0 : EuclideanSpace ℝ (Fin 3)))
    have hzero : divergenceN (fun _ : EuclideanSpace ℝ (Fin 3) =>
        (0 : EuclideanSpace ℝ (Fin 3))) x = 0 := by
      simp [divergenceN]
    simp only [sub_zero] at hp
    rw [hzero, sub_zero] at hp
    have hexp := boundary_neumann_c2_source_expansion A (fun _ => 0) φ x
    simp only [boundaryNeumannC2Source] at hexp
    rw [hzero, zero_sub] at hexp
    simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
    simp only [nondivDivergenceSource, nondivClassicalOperator, inner_sub_left]
    rw [hp]
    linarith
  apply (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hφ1
    (continuousOn_nondivClassicalOperator hU hA.continuousOn hb hφ)).mpr
  intro ψ hψ hcψ hsψ
  rw [boundary_neumann_c2_integral_divergence hU hF (hψ.of_le (by simp)) hcψ hsψ]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ U
  · rw [hpt x hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht)), zero_mul, zero_mul]

/-- Linearity of the weak nondivergence equation: subtracting a second solution
subtracts the right sides. -/
theorem IsWeakNondivergenceEquationOn.sub
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z φ f g : EuclideanSpace ℝ (Fin 3) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hb : ContinuousOn b U)
    (hz : ContDiffOn ℝ 1 z U) (hφ : ContDiffOn ℝ 1 φ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hez : IsWeakNondivergenceEquationOn A b z f U)
    (heφ : IsWeakNondivergenceEquationOn A b φ g U) :
    IsWeakNondivergenceEquationOn A b (fun x => z x - φ x) (fun x => f x - g x) U := by
  have hzφ : ContDiffOn ℝ 1 (fun x => z x - φ x) U := hz.sub hφ
  have hgrad : ∀ x ∈ U, gradient (fun y => z y - φ y) x = gradient z x - gradient φ x := by
    intro x hx
    have hdz := (hz.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
    have hdφ := (hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
    change (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ (fun y => z y - φ y) x) =
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ z x) -
        (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ φ x)
    rw [show (fun y => z y - φ y) = z - φ from rfl,
      (hdz.hasFDerivAt.sub hdφ.hasFDerivAt).fderiv, map_sub]
  have hsz := (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hz hf).mp hez
  have hsφ := (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hφ hg).mp heφ
  apply (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hzφ (hf.sub hg)).mpr
  intro ψ hψ hcψ hsψ
  change (∫ x, inner ℝ (A x (gradient (fun y => z y - φ y) x)) (gradient ψ x)) =
    -(∫ x, ψ x * nondivDivergenceSource A b (fun y => z y - φ y) (fun y => f y - g y) x)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hcgrad : HasCompactSupport (gradient ψ) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ψ)
  have hGz := continuousOn_gradient_of_contDiffOn hU hz
  have hGφ := continuousOn_gradient_of_contDiffOn hU hφ
  have hiz : Integrable (fun x => inner ℝ (A x (gradient z x)) (gradient ψ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      ((hA.continuousOn.clm_apply hGz).locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hψ1) hcgrad ((tsupport_gradient_subset ψ).trans hsψ)
  have hiφ : Integrable (fun x => inner ℝ (A x (gradient φ x)) (gradient ψ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      ((hA.continuousOn.clm_apply hGφ).locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hψ1) hcgrad ((tsupport_gradient_subset ψ).trans hsψ)
  have hDz : ContinuousOn (nondivDivergenceSource A b z f) U :=
    hf.add (((continuousOn_nondivCoefficientDivergence hU hA).sub hb).inner hGz)
  have hDφ : ContinuousOn (nondivDivergenceSource A b φ g) U :=
    hg.add (((continuousOn_nondivCoefficientDivergence hU hA).sub hb).inner hGφ)
  have hjz := integrable_mul_compact_factor_on (hDz.locallyIntegrableOn hU.measurableSet)
    hψ.continuous hcψ hsψ
  have hjφ := integrable_mul_compact_factor_on (hDφ.locallyIntegrableOn hU.measurableSet)
    hψ.continuous hcψ hsψ
  have hl : (∫ x, inner ℝ (A x (gradient (fun y => z y - φ y) x)) (gradient ψ x)) =
      (∫ x, inner ℝ (A x (gradient z x)) (gradient ψ x)) -
        ∫ x, inner ℝ (A x (gradient φ x)) (gradient ψ x) := by
    rw [← integral_sub hiz hiφ]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ U
    · rw [hgrad x hx, map_sub, inner_sub_left]
    · rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht)),
        inner_zero_right, inner_zero_right, inner_zero_right, sub_zero]
  have hr : (∫ x, ψ x * nondivDivergenceSource A b (fun y => z y - φ y)
      (fun y => f y - g y) x) =
      (∫ x, ψ x * nondivDivergenceSource A b z f x) -
        ∫ x, ψ x * nondivDivergenceSource A b φ g x := by
    rw [← integral_sub hjz hjφ]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ U
    · simp only [nondivDivergenceSource, hgrad x hx, inner_sub_right]
      ring
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht))]
      ring
  rw [hl, hr, hsz ψ hψ hcψ hsψ, hsφ ψ hψ hcψ hsψ]
  ring

end LiquidDrop
