module

public import NoCompromise.Sobolev.W11Pullback
public import NoCompromise.Sobolev.W11Approximation

@[expose] public section

/-!
# Strong L¹ approximation after shifted reflection

Both scalar and vector-valued convolutions converge after shifting into the
upper half-space and folding. The derivative of folding does not depend on the
shift, so the same convergence holds after applying its adjoint.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient Convolution
namespace LiquidDrop

lemma integrable_comp_shiftedCoordinateFold {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (i : Fin n) (δ : ℝ) {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Integrable (f ∘ shiftedCoordinateFold i δ) := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    integrableOn_comp_shiftedCoordinateFold i δ MeasurableSet.univ
      (mapsTo_univ _ _) hf.integrableOn

theorem tendsto_integral_norm_bump_convolution_shiftedCoordinateFold_sub
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (i : Fin n) {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f)
    {δ : ℕ → ℝ} {φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hδ : Tendsto δ atTop (𝓝 0)) (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)
        (shiftedCoordinateFold i (δ j) x) - f (coordinateFold i x)‖) atTop (𝓝 0) := by
  let g (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hg (j) : Integrable (g j) := (φ j).integrable_normed.integrable_convolution _ hf
  have hconv := tendsto_integral_norm_bump_convolution_sub hf hφ
  have hshift := tendsto_integral_norm_shiftedCoordinateFold_sub i hf hδ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hshift
  have hsum := (hconv.const_mul 2).add hshift
  simp only [mul_zero, zero_add] at hsum
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_) hsum
  have hi1 := integrable_comp_shiftedCoordinateFold i (δ j) ((hg j).sub hf)
  have hi2 := (integrable_comp_shiftedCoordinateFold i (δ j) hf).sub
    (integrable_comp_coordinateFold i hf)
  have hb := integral_norm_comp_shiftedCoordinateFold_le i (δ j) MeasurableSet.univ
    (mapsTo_univ _ _) ((hg j).sub hf).integrableOn
  simp only [Measure.restrict_univ] at hb
  calc
    _ ≤ ∫ x, ‖g j (shiftedCoordinateFold i (δ j) x) - f (shiftedCoordinateFold i (δ j) x)‖ +
        ‖f (shiftedCoordinateFold i (δ j) x) - f (coordinateFold i x)‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hi1.norm.add hi2.norm)
      exact Eventually.of_forall fun _ => norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = (∫ x, ‖g j (shiftedCoordinateFold i (δ j) x) -
          f (shiftedCoordinateFold i (δ j) x)‖) +
        ∫ x, ‖f (shiftedCoordinateFold i (δ j) x) - f (coordinateFold i x)‖ :=
      integral_add hi1.norm hi2.norm
    _ ≤ _ := by
      simpa only [Pi.sub_apply, g] using add_le_add_left hb _

lemma fderiv_shiftedCoordinateFold {n : ℕ} (i : Fin n) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (shiftedCoordinateFold i δ) x = fderiv ℝ (coordinateFold i) x := by
  exact fderiv_add_const _

theorem tendsto_integral_norm_fold_adjoint {n : ℕ} (i : Fin n)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {G' : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : Integrable G) (hG' : ∀ j, Integrable (G' j))
    (ht : Tendsto (fun j => ∫ x, ‖G' j x - G x‖) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖(fderiv ℝ (coordinateFold i) x).adjoint (G' j x) -
        (fderiv ℝ (coordinateFold i) x).adjoint (G x)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_) ht
  have hb := (integrable_fderiv_adjoint_apply (lipschitzWith_coordinateFold i)
    ((hG' j).sub hG)).2
  simpa only [Pi.sub_apply, map_sub, NNReal.coe_one, one_mul] using hb

end LiquidDrop
