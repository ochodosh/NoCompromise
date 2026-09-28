import NoCompromise.Elliptic.BoundaryHolderOddField

/-! Orthogonal conjugation and the coefficient extensions for even reflection. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

def boundaryNeumannConjugate
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  let R := (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap
  R.comp (A.comp R)

lemma boundaryNeumannConjugate_apply
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannConjugate A ξ = coordinateReflection (Fin.last 2)
      (A (coordinateReflection (Fin.last 2) ξ)) := rfl

lemma boundaryNeumannConjugate_twice
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannConjugate (boundaryNeumannConjugate A) = A := by
  ext ξ
  simp only [boundaryNeumannConjugate_apply, boundary_reflection_twice]

lemma boundaryNeumannConjugate_sub
    (A B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannConjugate (A - B) =
      boundaryNeumannConjugate A - boundaryNeumannConjugate B := by
  ext ξ
  simp only [boundaryNeumannConjugate_apply, sub_apply, map_sub]

lemma boundaryNeumannConjugate_norm_le
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ‖boundaryNeumannConjugate A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro ξ
  simpa only [boundaryNeumannConjugate_apply,
    (coordinateReflection (Fin.last 2)).norm_map] using
      A.le_opNorm (coordinateReflection (Fin.last 2) ξ)

lemma boundaryNeumannConjugate_norm
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ‖boundaryNeumannConjugate A‖ = ‖A‖ := by
  apply le_antisymm (boundaryNeumannConjugate_norm_le A)
  simpa only [boundaryNeumannConjugate_twice] using
    boundaryNeumannConjugate_norm_le (boundaryNeumannConjugate A)

lemma boundaryNeumannConjugate_inner
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (boundaryNeumannConjugate A ξ) ξ =
      inner ℝ (A (coordinateReflection (Fin.last 2) ξ))
        (coordinateReflection (Fin.last 2) ξ) := by
  conv_lhs => rhs; rw [← boundary_reflection_twice ξ]
  exact (coordinateReflection (Fin.last 2)).inner_map_map _ _

lemma boundaryNeumannConjugate_elliptic {lam : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    lam * ‖ξ‖ ^ 2 ≤ inner ℝ (boundaryNeumannConjugate A ξ) ξ := by
  rw [boundaryNeumannConjugate_inner]
  simpa only [(coordinateReflection (Fin.last 2)).norm_map] using
    hell (coordinateReflection (Fin.last 2) ξ)

lemma boundary_neumann_reflection_fixed {ξ : EuclideanSpace ℝ (Fin 3)}
    (hξ : ξ (Fin.last 2) = 0) : coordinateReflection (Fin.last 2) ξ = ξ := by
  ext i
  by_cases hi : i = Fin.last 2
  · subst i
    simp only [boundary_reflection_last, hξ, neg_zero]
  · simp only [coordinateReflection_apply, ite_eq_right hi]

/-- Both cross rows are needed; symmetry of the coefficient is not assumed. -/
lemma boundaryNeumannConjugate_eq_of_cross_zero
    {A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hcross : ∀ i : Fin 3, i ≠ Fin.last 2 →
      A (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A (EuclideanSpace.single (Fin.last 2) 1) i = 0) :
    boundaryNeumannConjugate A = A := by
  have hs (i : Fin 3) : boundaryNeumannConjugate A (EuclideanSpace.single i 1) =
      A (EuclideanSpace.single i 1) := by
    rw [boundaryNeumannConjugate_apply]
    by_cases hi : i = Fin.last 2
    · subst i
      have he : coordinateReflection (Fin.last 2) (EuclideanSpace.single (Fin.last 2) 1) =
          -EuclideanSpace.single (Fin.last 2) 1 := by
        simpa only [one_smul] using boundary_reflection_normal 1
      rw [he, map_neg, map_neg]
      ext j
      by_cases hj : j = Fin.last 2
      · subst j
        simp only [PiLp.neg_apply, boundary_reflection_last, neg_neg]
      · simp only [PiLp.neg_apply, coordinateReflection_apply, ite_eq_right hj, (hcross j hj).2,
          neg_zero]
    · have he : coordinateReflection (Fin.last 2) (EuclideanSpace.single i 1) =
          EuclideanSpace.single i 1 := by
        apply boundary_neumann_reflection_fixed
        simp only [PiLp.single_apply, ite_eq_right (Ne.symm hi)]
      rw [he]
      exact boundary_neumann_reflection_fixed (hcross i hi).1
  apply ContinuousLinearMap.ext
  intro ξ
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr ξ]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply, hs]

def boundaryNeumannCoefficient
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  if 0 ≤ x (Fin.last 2) then A x
  else boundaryNeumannConjugate (A (coordinateReflection (Fin.last 2) x))

def boundaryNeumannDatum (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  if 0 ≤ x (Fin.last 2) then H x
  else coordinateReflection (Fin.last 2) (H (coordinateReflection (Fin.last 2) x))

lemma boundaryNeumannCoefficient_eq_upper
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 ≤ x (Fin.last 2)) : boundaryNeumannCoefficient A x = A x := ite_eq_left hx

lemma boundaryNeumannDatum_eq_upper
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : 0 ≤ x (Fin.last 2)) :
    boundaryNeumannDatum H x = H x := ite_eq_left hx

end LiquidDrop
