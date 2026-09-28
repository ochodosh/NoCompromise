import NoCompromise.Sobolev.W11Reflection
import NoCompromise.Sobolev.W11FoldDomain
import NoCompromise.Sobolev.W11Closed

/-!
# Even reflection of W¹,¹ functions

Interior convolutions followed by vanishing inward shifts approximate the
actual reflected function and explicit reflected gradient strongly in L¹.
Closing the weak-gradient graph proves reflection on a smaller cube, with the
two-sheet bound separately for the function and gradient.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_integral_norm_sub_restrict_of_ae_eq {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → F} {g h : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ j, Integrable (f j)) (hg : Integrable g) (hgh : g =ᵐ[volume.restrict U] h)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in U, ‖f j x - h x‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_) ht
  calc
    _ = ∫ x in U, ‖f j x - g x‖ := integral_congr_ae
      (hgh.symm.mono fun x hx => by rw [hx])
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => norm_nonneg _) ((hf j).sub hg).norm

theorem HasW11GradientOn.coordinateFold_halfCube {n : ℕ} (i : Fin n)
    {r R : ℝ} (hrR : r < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G (coordinateHalfCube i R)) :
    HasW11GradientOn (f ∘ coordinateFold i)
      (fun x => (fderiv ℝ (coordinateFold i) x).adjoint (G (coordinateFold i x)))
      (coordinateCube n r) ∧
      (∫ x in coordinateCube n r, ‖f (coordinateFold i x)‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖f x‖ ∧
      (∫ x in coordinateCube n r,
        ‖(fderiv ℝ (coordinateFold i) x).adjoint (G (coordinateFold i x))‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖G x‖ := by
  let a (j : ℕ) : ℝ := ((R - r) / 4) / ((j : ℝ) + 1)
  have ha (j) : 0 < a j := div_pos (div_pos (sub_pos.mpr hrR) (by norm_num)) (by positivity)
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨a j / 2, a j, half_pos (ha j), half_lt_self (ha j)⟩
  let δ (j : ℕ) := 2 * a j
  have hδ (j) : (φ j).rOut < δ j := by
    change a j < 2 * a j
    linarith [ha j]
  have hR (j) : r + δ j + (φ j).rOut ≤ R := by
    have hsmall : a j ≤ (R - r) / 4 := div_le_self
      (by linarith : 0 ≤ (R - r) / 4) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    change r + 2 * a j + a j ≤ R
    linarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((R - r) / 4)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using ha0.const_mul 2
  let f0 := (coordinateHalfCube i R).indicator f
  let G0 := (coordinateHalfCube i R).indicator G
  have hif0 : Integrable f0 :=
    hf.integrable_function.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  have hiG0 : Integrable G0 :=
    hf.integrable_gradient.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  let u (j : ℕ) := ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f0) ∘
    shiftedCoordinateFold i (δ j)
  let H (j : ℕ) := ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G0) ∘
    shiftedCoordinateFold i (δ j)
  have hiu (j) : Integrable (u j) := integrable_comp_shiftedCoordinateFold i (δ j)
    ((φ j).integrable_normed.integrable_convolution _ hif0)
  have hiH (j) : Integrable (H j) := integrable_comp_shiftedCoordinateFold i (δ j)
    ((φ j).integrable_normed.integrable_convolution _ hiG0)
  have hconvF := tendsto_integral_norm_bump_convolution_shiftedCoordinateFold_sub
    i hif0 (φ := φ) hδ0 ha0
  have hconvG := tendsto_integral_norm_bump_convolution_shiftedCoordinateFold_sub
    i hiG0 (φ := φ) hδ0 ha0
  have hconvH := tendsto_integral_norm_fold_adjoint i
    (integrable_comp_coordinateFold i hiG0) hiH hconvG
  obtain ⟨hif, hbf⟩ := integrableOn_coordinateFold_halfCube_vector i hrR.le hf.integrable_function
  obtain ⟨hiG, hbG⟩ := integrableOn_adjoint_coordinateFold_halfCube i hrR.le hf.integrable_gradient
  refine ⟨?_, hbf, hbG⟩
  apply hasW11GradientOn_of_tendsto_L1 (isOpen_coordinateCube n r)
    (fun j => hf.bump_convolution_shiftedCoordinateFold i (φ j) (hδ j) (hR j)) hif hiG
  · exact tendsto_integral_norm_sub_restrict_of_ae_eq hiu
      (integrable_comp_coordinateFold i hif0)
      (indicator_halfCube_comp_coordinateFold_ae i hrR.le f) hconvF
  · apply tendsto_integral_norm_sub_restrict_of_ae_eq
      (fun j => (integrable_fderiv_adjoint_apply (lipschitzWith_coordinateFold i) (hiH j)).1)
      (integrable_fderiv_adjoint_apply (lipschitzWith_coordinateFold i)
        (integrable_comp_coordinateFold i hiG0)).1 ?_ hconvH
    exact (indicator_halfCube_comp_coordinateFold_ae_vector i hrR.le G).mono
      fun x hx => congrArg ((fderiv ℝ (coordinateFold i) x).adjoint) hx

end LiquidDrop
