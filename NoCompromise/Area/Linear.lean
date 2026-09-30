module

public import NoCompromise.Conventions
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# The two-dimensional Jacobian and linear image measure

`hausdorffMeasure2` is normalized Euclidean Hausdorff measure: on the Euclidean
plane it agrees exactly with Lebesgue volume. The linear image theorem is derived
from an orthonormal isometry onto the range and equidimensional linear change of
variables. Only the algebraic norm-determinant identities are used from `NormDet`;
its lower-dimensional image-measure theorems are not used.
-/

noncomputable section

open MeasureTheory Set Module
open scoped ENNReal

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Normalized two-dimensional Hausdorff measure in Euclidean space. -/
noncomputable def hausdorffMeasure2 (m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.euclideanHausdorffMeasure 2

/-- On the plane, normalized Hausdorff area is ordinary Lebesgue volume. -/
lemma hausdorffMeasure2_plane : hausdorffMeasure2 2 = volume :=
  EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2

/-- The Gram-determinant formula for the two-dimensional Jacobian of a linear map. -/
noncomputable def jacobian2Linear {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (L.adjoint.comp L).det

/-- The Gram Jacobian is the algebraic norm determinant. -/
lemma jacobian2Linear_eq_normDet {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    jacobian2Linear L = L.normDet := by
  unfold jacobian2Linear
  rw [← L.normDet_sq]
  exact Real.sqrt_sq L.normDet_nonneg

lemma jacobian2Linear_nonneg {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 ≤ jacobian2Linear L := Real.sqrt_nonneg _

lemma jacobian2Linear_zero {m : ℕ} :
    jacobian2Linear (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) = 0 := by
  rw [jacobian2Linear_eq_normDet]
  simp

/-- Rank two is precisely injectivity for a linear map with planar source. -/
lemma rank_two_iff_injective {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    finrank ℝ L.range = 2 ↔ Function.Injective L := by
  have h := L.normDet_ne_zero_tfae.out 3 5
  simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using h

lemma jacobian2Linear_pos_iff_injective {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < jacobian2Linear L ↔ Function.Injective L := by
  have h := L.normDet_ne_zero_tfae.out 1 5
  rw [jacobian2Linear_eq_normDet, lt_iff_le_and_ne]
  simpa only [L.normDet_nonneg, true_and, ne_comm, ContinuousLinearMap.coe_coe] using h

/-- The planar Gram Jacobian is the product of the first two singular values. -/
lemma jacobian2Linear_eq_singularValues {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    jacobian2Linear L = L.singularValues 0 * L.singularValues 1 := by
  rw [jacobian2Linear_eq_normDet, L.normDet_eq_prod_singularValues]
  simp [Finset.prod_range_succ]

/-- The two singular values are ordered and positive when the map has rank two. -/
lemma singularValues_two_pos_and_ordered {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) : 0 < L.singularValues 1 ∧
      L.singularValues 1 ≤ L.singularValues 0 := by
  exact ⟨L.injective_iff_forall_lt_finrank_singularValues_pos.mp hL 1 (by simp),
    L.singularValues_antitone (by norm_num)⟩

/-- The Gram Jacobian depends continuously on the linear map. -/
lemma continuous_jacobian2Linear {m : ℕ} : Continuous
    (jacobian2Linear (m := m)) := by
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id))

/-- The two-dimensional Jacobian of a map, defined using the total Fréchet derivative.
It is zero at nondifferentiability points, since `fderiv` is zero there. -/
noncomputable def jacobian2 {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ := jacobian2Linear (fderiv ℝ f x)

lemma jacobian2_eq_zero_of_not_differentiableAt {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : ¬DifferentiableAt ℝ f x) :
    jacobian2 f x = 0 := by
  rw [jacobian2, fderiv_zero_of_not_differentiableAt hf, jacobian2Linear_zero]

lemma measurable_jacobian2 {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) :
    Measurable (jacobian2 f) :=
  continuous_jacobian2Linear.measurable.comp (measurable_fderiv ℝ f)

lemma jacobian2_nonneg {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ jacobian2 f x :=
  jacobian2Linear_nonneg _

/-- Linear image measure follows from isometry invariance and equidimensional
change of variables. No lower-dimensional area formula is invoked. -/
theorem normalizedHausdorffMeasure_image_linear_injective {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (B : Set (EuclideanSpace ℝ (Fin n))) :
    Measure.euclideanHausdorffMeasure n (L '' B) = ENNReal.ofReal L.normDet * volume B := by
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hL
  have hrank : finrank ℝ L.range = finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
    (L.normDet_ne_zero_tfae.out 2 3).mp hker
  obtain ⟨bv⟩ := (L.normDet_ne_zero_tfae.out 2 4).mp hker
  let g : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] L.range :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))).equiv bv (Equiv.refl _)
  suffices Measure.euclideanHausdorffMeasure n ((L.range.subtypeₗᵢ.comp g.toLinearIsometry) ''
      ((g.symm.toLinearIsometry.toLinearMap.comp L.toLinearMap.rangeRestrict) '' B)) =
        ENNReal.ofReal L.normDet * volume B by
    simpa [Set.image_image] using this
  rw [(LinearIsometry.isometry _).euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
    Measure.addHaar_image_linearMap volume, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ hrank.symm,
    g.symm.toLinearIsometry.normDet_eq_one]
  simp

/-- The blueprint's linear area formula, in the Gram-Jacobian convention.
It holds for every set, and hence in particular for every Borel set. -/
theorem hausdorffMeasure2_image_linear {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) (B : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffMeasure2 m (L '' B) = ENNReal.ofReal (jacobian2Linear L) * volume B := by
  rw [jacobian2Linear_eq_normDet]
  exact normalizedHausdorffMeasure_image_linear_injective L hL B

/-- Rank-two form of the linear image theorem, using the ordered singular values. -/
theorem hausdorffMeasure2_image_linear_singularValues {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : finrank ℝ L.range = 2) (B : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffMeasure2 m (L '' B) =
      ENNReal.ofReal (L.singularValues 0 * L.singularValues 1) * volume B := by
  rw [← jacobian2Linear_eq_singularValues]
  exact hausdorffMeasure2_image_linear L ((rank_two_iff_injective L).mp hL) B

end LiquidDrop
