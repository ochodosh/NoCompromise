import NoCompromise.Elliptic.BoundaryNeumannC2Equation

/-! # The scalar source for the normal second derivative -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

def boundaryNeumannC2Trace :
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single i 1))

lemma boundaryNeumannC2Trace_apply
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannC2Trace L = ∑ i, L (EuclideanSpace.single i 1) i := by
  simp only [boundaryNeumannC2Trace, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  rfl

lemma boundaryNeumannC2Trace_norm : ‖boundaryNeumannC2Trace‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro L
  rw [boundaryNeumannC2Trace_apply, Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, ‖L‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (show |L (EuclideanSpace.single i 1) i| ≤ ‖L (EuclideanSpace.single i 1)‖ from
        by simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le (L (EuclideanSpace.single i 1)) i).trans
      simpa only [PiLp.norm_single, norm_one, mul_one] using L.le_opNorm (EuclideanSpace.single i 1)
    _ = 3 * ‖L‖ := by simp

def boundaryNeumannC2Source
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (w : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  divergenceN H x - inner ℝ (nondivCoefficientDivergence A x) (gradient w x)

/-- The effective scalar source has a Hölder norm controlled by the original
closed data, without using any second derivative of the solution. -/
theorem boundary_neumann_c2_source_holder {α lam cap M N : ℝ}
    (hM : 0 ≤ M) (_hN : 0 ≤ N)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w) :
    HasFiniteHolderNormOn α (boundaryNeumannC2Source A H w) (closure (boundaryHalfBall 1)) ∧
      holderNorm α (boundaryNeumannC2Source A H w) (closure (boundaryHalfBall 1)) ≤
        (3 + 9 * M) * N := by
  have hwN : nondivC1HolderNorm α w (closure (boundaryHalfBall 1)) ≤ N :=
    (le_add_of_nonneg_right d.source.norm_nonneg).trans d.norm_bound
  have hHN : nondivC1HolderNorm α H (closure (boundaryHalfBall 1)) ≤ N :=
    (le_add_of_nonneg_left d.solution.norm_nonneg).trans d.norm_bound
  obtain ⟨hdiv, hdivb⟩ := nondiv_holder_comp_clm d.source.derivative_holder boundaryNeumannC2Trace
  have heq : (fun x => boundaryNeumannC2Trace (fderiv ℝ H x)) = divergenceN H := by
    funext x
    exact boundaryNeumannC2Trace_apply _
  rw [heq] at hdiv hdivb
  have hdivN : holderNorm α (divergenceN H) (closure (boundaryHalfBall 1)) ≤ 3 * N :=
    hdivb.trans (mul_le_mul boundaryNeumannC2Trace_norm
      (d.source.derivative_norm_le.trans hHN) d.source.derivative_holder.norm_nonneg (by norm_num))
  obtain ⟨hDA, hDAb⟩ := nondivCoefficientDivergence_holder d.coefficient
  have hDAN : holderNorm α (nondivCoefficientDivergence A) (closure (boundaryHalfBall 1)) ≤ 3 * M :=
    hDAb.trans (mul_le_mul_of_nonneg_left d.coefficient_norm (by norm_num))
  obtain ⟨hGw, hGwb⟩ := d.solution.gradient_holder
  have hGwN := hGwb.trans (d.solution.derivative_norm_le.trans hwN)
  obtain ⟨hp, hpb⟩ := nondiv_holder_inner hDA hGw
  obtain ⟨hs, hsb⟩ := nondiv_holder_sub hdiv hp
  refine ⟨hs, hsb.trans ?_⟩
  have hpN : holderNorm α (fun x => inner ℝ (nondivCoefficientDivergence A x) (gradient w x))
      (closure (boundaryHalfBall 1)) ≤ 9 * M * N := by
    apply hpb.trans
    calc
      _ ≤ 3 * (3 * M) * N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hDAN (by norm_num)) hGwN
          hGw.norm_nonneg (by positivity)
      _ = _ := by ring
  nlinarith only [hdivN, hpN]

lemma boundary_neumann_c2_source_expansion
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (w : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannC2Source A H w x = divergenceN H x -
      ∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * fderiv ℝ w x (EuclideanSpace.single j 1) := by
  unfold boundaryNeumannC2Source
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, nondivCoefficientDivergence,
    nondivCoefficientContraction_component, gradient_apply_eq_fderiv_single, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end LiquidDrop
