module

public import NoCompromise.Area.Linear

@[expose] public section

/-!
# Linear algebra of planar chart derivatives

An injective chart derivative identifies its planar source with its range. An arbitrary
second chart derivative therefore induces a unique continuous linear map on that range.
Its Jacobian in any orthonormal coordinates is the quotient of the two chart Jacobians.

For an ambient linear map, the composite Jacobian factors into the range-plane Jacobian
and the chart Jacobian. These are purely linear statements; no intrinsic geometric
notion of tangent plane, almost-everywhere chart assertion, or area formula is assumed.
Only algebraic norm-determinant identities are used from mathlib.
-/

noncomputable section

open Module

namespace LiquidDrop

/-- An injective planar linear map has a range with orthonormal planar coordinates. -/
lemma exists_range_plane_isometry
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K) :
    Nonempty (EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] K.range) := by
  have hker : K.ker = ⊥ := LinearMap.ker_eq_bot.mpr hK
  obtain ⟨b⟩ := (K.normDet_ne_zero_tfae.out 2 4).mp hker
  exact ⟨(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).equiv b (Equiv.refl _)⟩

/-- In orthonormal planar coordinates, the Gram Jacobian is the norm determinant. -/
lemma jacobian2Linear_comp_planeIsometry
    {P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))}
    (D : P →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] P) :
    jacobian2Linear (D.comp e.toContinuousLinearEquiv.toContinuousLinearMap) = D.normDet := by
  rw [jacobian2Linear_eq_normDet]
  change (D.toLinearMap.comp e.toLinearEquiv.toLinearMap).normDet = D.normDet
  have he : e.toLinearEquiv.toLinearMap.normDet = 1 := e.toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ e.toLinearEquiv.finrank_eq, he, mul_one]

/-- The Jacobian chain factor through the range plane. The supplied isometry itself
ensures the range is two-dimensional. -/
lemma jacobian2Linear_comp_factor
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] K.range) :
    jacobian2Linear (L.comp K) =
      jacobian2Linear (L.comp
        (K.range.subtypeₗᵢ.comp e.toLinearIsometry).toContinuousLinearMap) *
        jacobian2Linear K := by
  rw [jacobian2Linear_eq_normDet, jacobian2Linear_eq_normDet,
    jacobian2Linear_eq_normDet]
  change (L.toLinearMap.comp K.toLinearMap).normDet = _
  rw [LinearMap.normDet_comp]
  congr 1
  symm
  change ((L.toLinearMap.domRestrict K.range).comp e.toLinearEquiv.toLinearMap).normDet = _
  have he : e.toLinearEquiv.toLinearMap.normDet = 1 := e.toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ e.toLinearEquiv.finrank_eq, he, mul_one]

/-- The unique linear map on an injective chart derivative's range induced by another
linear map on the chart source. This definition makes no geometric tangent assertion. -/
def chartTangentialMap
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    K.range →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  let e := (LinearEquiv.ofInjective K.toLinearMap hK).toContinuousLinearEquiv
  M.comp e.symm.toContinuousLinearMap

/-- The induced range map has the prescribed composite with the chart derivative. -/
lemma chartTangentialMap_comp_rangeRestrict
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (chartTangentialMap K hK M).comp K.rangeRestrict = M := by
  apply ContinuousLinearMap.ext
  intro x
  change M ((LinearEquiv.ofInjective K.toLinearMap hK).symm
    ((LinearEquiv.ofInjective K.toLinearMap hK) x)) = M x
  rw [LinearEquiv.symm_apply_apply]

/-- The factorization through the range uniquely determines the induced linear map. -/
lemma chartTangentialMap_unique
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (D : K.range →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hD : D.comp K.rangeRestrict = M) : D = chartTangentialMap K hK M := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, hx⟩ := K.toLinearMap.surjective_rangeRestrict y
  rw [← hx]
  exact congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) => A x)
    (hD.trans (chartTangentialMap_comp_rangeRestrict K hK M).symm)

/-- Existence and uniqueness of the range map for any prescribed chart-source map. -/
lemma existsUnique_chartTangentialMap
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃! D : K.range →L[ℝ] EuclideanSpace ℝ (Fin 3), D.comp K.rangeRestrict = M :=
  ⟨chartTangentialMap K hK M, chartTangentialMap_comp_rangeRestrict K hK M,
    fun D hD => chartTangentialMap_unique K hK M D hD⟩

/-- The norm determinant of the induced range map is the remaining Jacobian factor. -/
lemma chartTangentialMap_jacobian_factor
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    jacobian2Linear M = (chartTangentialMap K hK M).normDet * jacobian2Linear K := by
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = finrank ℝ K.range :=
    (LinearEquiv.ofInjective K.toLinearMap hK).finrank_eq
  conv_lhs => rw [← chartTangentialMap_comp_rangeRestrict K hK M]
  rw [jacobian2Linear_eq_normDet]
  change ((chartTangentialMap K hK M).toLinearMap.comp K.toLinearMap.rangeRestrict).normDet = _
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ hdim]
  congr 1
  rw [jacobian2Linear_eq_normDet]
  exact K.toLinearMap.normDet_codRestrict _

/-- The exact Jacobian quotient in any orthonormal range-plane coordinates. -/
lemma chartTangentialMap_jacobian_quotient
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] K.range) :
    jacobian2Linear ((chartTangentialMap K hK M).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap) = jacobian2Linear M / jacobian2Linear K := by
  rw [jacobian2Linear_comp_planeIsometry]
  apply (eq_div_iff (ne_of_gt ((jacobian2Linear_pos_iff_injective K).mpr hK))).mpr
  exact (chartTangentialMap_jacobian_factor K hK M).symm

/-- Changing orthonormal coordinates on a plane does not change its linear Jacobian. -/
lemma jacobian2Linear_comp_planeIsometry_independent
    {P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))}
    (D : P →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (e₁ e₂ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] P) :
    jacobian2Linear (D.comp e₁.toContinuousLinearEquiv.toContinuousLinearMap) =
      jacobian2Linear (D.comp e₂.toContinuousLinearEquiv.toContinuousLinearMap) := by
  rw [jacobian2Linear_comp_planeIsometry, jacobian2Linear_comp_planeIsometry]

/-- The ambient restriction factor is the composite Jacobian divided by the chart Jacobian. -/
lemma jacobian2Linear_comp_factor_quotient
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] K.range) :
    jacobian2Linear (L.comp
        (K.range.subtypeₗᵢ.comp e.toLinearIsometry).toContinuousLinearMap) =
      jacobian2Linear (L.comp K) / jacobian2Linear K := by
  apply (eq_div_iff (ne_of_gt ((jacobian2Linear_pos_iff_injective K).mpr hK))).mpr
  exact (jacobian2Linear_comp_factor K L e).symm

/-- Evaluation of the induced map on a vector in the chart range. -/
lemma chartTangentialMap_apply
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 2)) :
    chartTangentialMap K hK M (K.rangeRestrict x) = M x :=
  congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A x)
    (chartTangentialMap_comp_rangeRestrict K hK M)

/-- Every linear factor through the chart range has the same Jacobian quotient. -/
lemma jacobian2Linear_tangential_quotient
    (K : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hK : Function.Injective K)
    (M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (D : K.range →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hD : D.comp K.rangeRestrict = M)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] K.range) :
    jacobian2Linear (D.comp e.toContinuousLinearEquiv.toContinuousLinearMap) =
      jacobian2Linear M / jacobian2Linear K := by
  rw [chartTangentialMap_unique K hK M D hD]
  exact chartTangentialMap_jacobian_quotient K hK M e

end LiquidDrop
