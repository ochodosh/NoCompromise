import NoCompromise.Elliptic.NondivSchauderQuotient
import NoCompromise.Elliptic.NondivSchauderConvergence

/-!
# Convergence of the constructed differentiated datum

The segment primitive converges to g times the direction, with its genuine
Hölder modulus. Together with the coefficient Taylor remainder this identifies
the limit of the entire discrete vector datum, without differentiating g.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_segmentField_sub_le {n : ℕ} {α : ℝ} (hα : 0 < α)
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : HasFiniteHolderNormOn α g U) (h : ℝ) (e : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖ = 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ campanatoSegmentDomain U (h • e)) :
    ‖campanatoSegmentField g h e x - g x • e‖ ≤ holderSeminorm α g U * ‖h‖ ^ α := by
  have hxU : x ∈ U := campanatoSegmentDomain_subset U (h • e) hx
  have hc := hg.nondiv_continuousOn hα
  have hi := campanatoSegmentAverage_integrable_path hc hx
  have hi' : IntegrableOn (fun _ : ℝ => g x) (Icc (0 : ℝ) 1) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have heq : campanatoSegmentAverage g (h • e) x - g x =
      ∫ t in Icc (0 : ℝ) 1, (g (x + t • (h • e)) - g x) := by
    rw [integral_sub hi hi']
    simp [campanatoSegmentAverage, integral_const]
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖g (x + t • (h • e)) - g x‖ ≤ holderSeminorm α g U * ‖h‖ ^ α := by
    apply (hg.nondiv_norm_sub_le (hx t ht) hxU).trans
    apply mul_le_mul_of_nonneg_left _ hg.seminorm_nonneg
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
    simp only [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg h)
  have ht := norm_setIntegral_le_of_norm_le_const (μ := volume)
    isCompact_Icc.measure_lt_top hb
  simpa only [campanatoSegmentField, ← sub_smul, norm_smul, he, mul_one, heq,
    Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one] using ht

/-- The exact limit vector datum for the derivative in coordinate i. -/
def nondivDerivativeDatum {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  nondivDivergenceSource A b z f x • EuclideanSpace.single i 1 -
    fderiv ℝ A x (EuclideanSpace.single i 1) (gradient z x)

lemma nondivQuotientDatum_sub_le {n : ℕ} {α : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0) {x : EuclideanSpace ℝ (Fin n)}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    ‖nondivQuotientDatum A b z f i h x - nondivDerivativeDatum A b z f i x‖ ≤
      (holderSeminorm α (nondivDivergenceSource A b z f) U +
        holderSeminorm α (fderiv ℝ A) U * holderNorm α (gradient z) U) * ‖h‖ ^ α := by
  have hx : x ∈ U := by simpa only [zero_smul, add_zero] using hseg 0 (by simp)
  have hg := (nondivDivergenceSource_holder hA hb hz hf).1
  have hH := nondiv_segmentField_sub_le hα hg h (EuclideanSpace.single i 1) (by simp) hseg
  have hδ := nondiv_norm_coordinateDifferenceQuotient_sub_le hα.le hU hA i hh x hseg
  have hDz := hz.gradient_holder.1.nondiv_norm_le hx
  have heq : nondivQuotientDatum A b z f i h x - nondivDerivativeDatum A b z f i x =
      (campanatoSegmentField (nondivDivergenceSource A b z f) h (EuclideanSpace.single i 1) x -
        nondivDivergenceSource A b z f x • EuclideanSpace.single i 1) -
      (coordinateDifferenceQuotient i h A x -
        fderiv ℝ A x (EuclideanSpace.single i 1)) (gradient z x) := by
    dsimp [nondivQuotientDatum, nondivDifferenceForcing, nondivDerivativeDatum]
    simp only [sub_apply]
    abel
  rw [heq]
  apply (norm_sub_le _ _).trans
  have hp := ((coordinateDifferenceQuotient i h A x -
    fderiv ℝ A x (EuclideanSpace.single i 1)).le_opNorm (gradient z x)).trans
    (mul_le_mul hδ hDz (norm_nonneg _)
      (mul_nonneg hA.derivative_holder.seminorm_nonneg (Real.rpow_nonneg (norm_nonneg h) α)))
  calc
    _ ≤ holderSeminorm α (nondivDivergenceSource A b z f) U * ‖h‖ ^ α +
        (holderSeminorm α (fderiv ℝ A) U * ‖h‖ ^ α) * holderNorm α (gradient z) U :=
      add_le_add hH hp
    _ = _ := by ring

/-- The limiting datum retains Hölder regularity using only DA, Dz, and g. -/
theorem nondivDerivativeDatum_holder {n : ℕ} {α : ℝ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U) (i : Fin n) :
    HasFiniteHolderNormOn α (nondivDerivativeDatum A b z f i) U ∧
      holderNorm α (nondivDerivativeDatum A b z f i) U ≤
        holderNorm α (nondivDivergenceSource A b z f) U +
          3 * holderNorm α (fderiv ℝ A) U * holderNorm α (gradient z) U := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)
  let Q := ContinuousLinearMap.apply ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (EuclideanSpace.single i (1 : ℝ))
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t
    simp [L, norm_smul]
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro D
    simpa only [Q, ContinuousLinearMap.apply_apply, PiLp.norm_single, norm_one, mul_one,
      one_mul] using D.le_opNorm (EuclideanSpace.single i 1)
  have hg := (nondivDivergenceSource_holder hA hb hz hf).1
  obtain ⟨hH, hHb⟩ := nondiv_holder_comp_clm hg L
  obtain ⟨hD, hDb⟩ := nondiv_holder_comp_clm hA.derivative_holder Q
  obtain ⟨hP, hPb⟩ := nondiv_holder_clm_apply hD hz.gradient_holder.1
  obtain ⟨hF, hFb⟩ := nondiv_holder_sub hH hP
  have hHb' : holderNorm α (fun x => L (nondivDivergenceSource A b z f x)) U ≤
      holderNorm α (nondivDivergenceSource A b z f) U :=
    hHb.trans ((mul_le_mul_of_nonneg_right hL hg.norm_nonneg).trans_eq (one_mul _))
  have hDb' : holderNorm α (fun x => Q (fderiv ℝ A x)) U ≤
      holderNorm α (fderiv ℝ A) U :=
    hDb.trans ((mul_le_mul_of_nonneg_right hQ hA.derivative_holder.norm_nonneg).trans_eq
      (one_mul _))
  refine ⟨hF, hFb.trans (add_le_add hHb' (hPb.trans ?_))⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDb' (by norm_num))
    hz.gradient_holder.1.norm_nonneg

end LiquidDrop
