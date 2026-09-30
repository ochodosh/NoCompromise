module

public import NoCompromise.Sobolev.W11FoldApprox
public import NoCompromise.Sobolev.H1Reflection

@[expose] public section

/-!
# Interior mollification followed by W¹,¹ reflection

The zero extension need not have a weak gradient across the boundary. Its
convolution has the original convolved gradient wherever the translated kernel
stays inside the domain. This gives an explicit weak gradient after shifting
and folding, suitable for the strong L¹ closure argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem HasW11GradientOn.gradient_convolution_indicator {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) (hs : tsupport (fun y => k (x - y)) ⊆ U) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator G) x := by
  have hmf := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_function
  have hmG := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_gradient
  have hif := hmf.locallyIntegrable (by norm_num)
  have hiG := hmG.locallyIntegrable (by norm_num)
  let φ := fun y => k (x - y)
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hck.comp_homeomorph (Homeomorph.subLeft x)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiL := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hif (continuous_gradient_of_contDiff hk) x
  have hiR := hck.convolutionExists_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hiG hk.continuous x
  change Integrable (fun y => U.indicator f y • gradient k (x - y)) at hiL
  change Integrable (fun y => k (x - y) • U.indicator G y) at hiR
  rw [gradient_convolution_left hif hk hck x, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiL.eval_piLp, eval_integral_piLp hiR.eval_piLp]
  have h := hf.test_eq i φ hφ hcφ hs
  have hderiv (y) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hderiv, mul_neg, integral_neg, neg_neg] at h
  simp only [PiLp.smul_apply, smul_eq_mul]
  calc
    _ = ∫ y in U, f y * gradient k (x - y) i := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy]
    _ = ∫ y in U, k (x - y) * G y i := h
    _ = _ := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy]

theorem HasW11GradientOn.bump_convolution_shiftedCoordinateFold {n : ℕ}
    (i : Fin n) {r R δ : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G (coordinateHalfCube i R))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hδ : φ.rOut < δ) (hR : r + δ + φ.rOut ≤ R) :
    HasW11GradientOn
      ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (coordinateHalfCube i R).indicator f) ∘ shiftedCoordinateFold i δ)
      (fun x => (fderiv ℝ (coordinateFold i) x).adjoint
        ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
          (coordinateHalfCube i R).indicator G) (shiftedCoordinateFold i δ x)))
      (coordinateCube n r) := by
  let f0 := (coordinateHalfCube i R).indicator f
  let G0 := (coordinateHalfCube i R).indicator G
  let g := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f0
  let H := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G0
  have hif0 : Integrable f0 :=
    hf.integrable_function.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  have hiG0 : Integrable G0 :=
    hf.integrable_gradient.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  have hif : Integrable g := φ.integrable_normed.integrable_convolution _ hif0
  have hiG : Integrable H := φ.integrable_normed.integrable_convolution _ hiG0
  have hgs : ContDiff ℝ 1 g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hif0.locallyIntegrable
  have hgrad (x) (hx : x ∈ coordinateCube n r) :
      gradient g (shiftedCoordinateFold i δ x) = H (shiftedCoordinateFold i δ x) := by
    apply hf.gradient_convolution_indicator (isOpen_coordinateHalfCube i R)
      φ.contDiff_normed φ.hasCompactSupport_normed _
    apply tsupport_bump_translate_subset_halfCube i φ
    · exact (mapsTo_shiftedCoordinateFold_halfCube i
        (φ.rOut_pos.trans hδ) (by linarith) hx).1
    · simp only [shiftedCoordinateFold_apply, ite_true]
      linarith [abs_nonneg (x i)]
  have hw := hasWeakGradientOn_comp_of_contDiffOn (isOpen_coordinateCube n r) isOpen_univ
    hgs.contDiffOn (lipschitzWith_shiftedCoordinateFold i δ).lipschitzOnWith
    (mapsTo_univ _ _)
  have hae := ae_gradient_comp_eq_adjoint hgs (lipschitzWith_shiftedCoordinateFold i δ)
  have hEq : gradient (g ∘ shiftedCoordinateFold i δ) =ᵐ[
      volume.restrict (coordinateCube n r)]
        (fun x => (fderiv ℝ (coordinateFold i) x).adjoint (H (shiftedCoordinateFold i δ x))) := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_mem (isOpen_coordinateCube n r).measurableSet] with x hx hxU
    rw [hx, hgrad x hxU, fderiv_shiftedCoordinateFold]
  refine ⟨hw.congr_ae EventuallyEq.rfl hEq,
    (integrable_comp_shiftedCoordinateFold i δ hif).integrableOn, ?_⟩
  exact (integrable_fderiv_adjoint_apply (lipschitzWith_coordinateFold i)
    (integrable_comp_shiftedCoordinateFold i δ hiG)).1.integrableOn

end LiquidDrop
