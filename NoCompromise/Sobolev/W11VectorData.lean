module

public import NoCompromise.Sobolev.W11Space

@[expose] public section

/-!
# Vector-valued W¹,¹ data and its coordinate bounds

The specified derivative is an actual continuous linear map at almost every
point, and each coordinate has the adjoint row as its weak gradient. The norm
on derivative matrices is the Euclidean operator norm.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

structure HasW11VectorGradientOn {n : ℕ}
    (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  integrable_function : IntegrableOn Z U
  integrable_gradient : IntegrableOn J U
  weak_component : ∀ i : Fin n, HasWeakGradientOn (fun x => Z x i)
    (fun x => (J x).adjoint (EuclideanSpace.single i 1)) U

lemma norm_adjoint_single_le {n : ℕ}
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖J.adjoint (EuclideanSpace.single i 1)‖ ≤ ‖J‖ := by
  simpa only [LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one, mul_one] using
    J.adjoint.le_opNorm (EuclideanSpace.single i 1)

lemma integrable_adjoint_single {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hJ : Integrable J μ) (i : Fin n) :
    Integrable (fun x => (J x).adjoint (EuclideanSpace.single i 1)) μ := by
  apply hJ.norm.mono' ?_ (Eventually.of_forall fun x => norm_adjoint_single_le (J x) i)
  exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    ((ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hJ.1).prodMk
      aestronglyMeasurable_const)

theorem HasW11VectorGradientOn.component {n : ℕ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hZ : HasW11VectorGradientOn Z J U) (i : Fin n) :
    HasW11GradientOn (fun x => Z x i) (fun x => (J x).adjoint (EuclideanSpace.single i 1)) U :=
  ⟨hZ.weak_component i, hZ.integrable_function.eval_piLp i,
    integrable_adjoint_single hZ.integrable_gradient i⟩

theorem HasW11VectorGradientOn.component_bound {n : ℕ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hZ : HasW11VectorGradientOn Z J U) (i : Fin n) :
    lpNorm (fun x => Z x i) 1 (volume.restrict U) +
      lpNorm (fun x => (J x).adjoint (EuclideanSpace.single i 1)) 1 (volume.restrict U) ≤
    (∫ x in U, ‖Z x‖) + ∫ x in U, ‖J x‖ := by
  rw [lpNorm_one_eq_integral_norm (hZ.component i).integrable_function.1,
    lpNorm_one_eq_integral_norm (hZ.component i).integrable_gradient.1]
  apply add_le_add
  · exact integral_mono (hZ.component i).integrable_function.norm hZ.integrable_function.norm
      (fun x => PiLp.norm_apply_le (Z x) i)
  · exact integral_mono (hZ.component i).integrable_gradient.norm hZ.integrable_gradient.norm
      (fun x => norm_adjoint_single_le (J x) i)

lemma norm_euclidean_le_sum_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have hx : x = ∑ i, EuclideanSpace.single i (x i) := by
    ext i
    simp
  calc
    _ = ‖∑ i, EuclideanSpace.single i (x i)‖ := congrArg norm hx
    _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single]

end LiquidDrop
