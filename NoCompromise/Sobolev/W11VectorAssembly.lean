import NoCompromise.Sobolev.W11VectorData

/-! # Recovering actual vector W¹,¹ data from its finitely many scalar rows -/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop

lemma norm_le_sum_adjoint_rows {n : ℕ}
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖J‖ ≤ ∑ i, ‖J.adjoint (EuclideanSpace.single i 1)‖ := by
  classical
  apply J.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  calc
    _ ≤ ∑ i, ‖J v i‖ := norm_euclidean_le_sum_norm (J v)
    _ ≤ ∑ i, ‖J.adjoint (EuclideanSpace.single i 1)‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := norm_inner_le_norm (𝕜 := ℝ) (J.adjoint (EuclideanSpace.single i 1)) v
      simpa only [ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left,
        map_one, one_mul] using h
    _ = _ := by rw [Finset.sum_mul]

theorem hasW11VectorGradientOn_of_components {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hJ : AEStronglyMeasurable J (volume.restrict D))
    (hc : ∀ i, HasW11GradientOn (fun x => Z x i)
      (fun x => (J x).adjoint (EuclideanSpace.single i 1)) D) :
    HasW11VectorGradientOn Z J D := by
  classical
  refine ⟨integrable_piLp_iff.mpr (fun i => (hc i).integrable_function), ?_,
    fun i => (hc i).toHasWeakGradientOn⟩
  have hi := integrable_finsetSum Finset.univ
    (fun i _ => (hc i).integrable_gradient.norm)
  exact hi.mono' hJ (Eventually.of_forall fun x => norm_le_sum_adjoint_rows (J x))

end LiquidDrop
