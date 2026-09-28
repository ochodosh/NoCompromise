import NoCompromise.Elliptic.NeumannLocalizeMap
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# The coefficient of the placed and scaled normal chart
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- The exact divergence coefficient of an ambient coordinate map. -/
def neumannLocalizeCoefficient (Θ : AmbientSpace → AmbientSpace) (y : AmbientSpace) :
    AmbientSpace →L[ℝ] AmbientSpace :=
  |(fderiv ℝ Θ y).det| •
    ((fderiv ℝ Θ y).inverse.comp (fderiv ℝ Θ y).inverse.adjoint)

lemma neumannLocalize_abs_det_isometry (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) :
    |(Q : AmbientSpace →L[ℝ] AmbientSpace).det| = 1 := by
  change |Q.toLinearMap.det| = 1
  rw [← LinearMap.normDet_eq_abs_det]
  exact Q.toLinearIsometry.normDet_eq_one

/-- The algebraic Dirichlet pairing holds for arbitrary vectors, including
values of a weak gradient. -/
theorem neumannLocalize_dirichlet_pairing
    (Θ : AmbientSpace → AmbientSpace) {y : AmbientSpace}
    (hy : (fderiv ℝ Θ y).IsInvertible) (v w : AmbientSpace) :
    inner ℝ (neumannLocalizeCoefficient Θ y ((fderiv ℝ Θ y).adjoint v))
      ((fderiv ℝ Θ y).adjoint w) = |(fderiv ℝ Θ y).det| * inner ℝ v w := by
  let L := fderiv ℝ Θ y
  have hstar : L.inverse.adjoint.comp L.adjoint = ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hy.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have hs : L.inverse.adjoint (L.adjoint v) = v :=
    congrArg (fun A : AmbientSpace →L[ℝ] AmbientSpace => A v) hstar
  change inner ℝ (|L.det| • L.inverse (L.inverse.adjoint (L.adjoint v)))
    (L.adjoint w) = _
  rw [hs, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right, hy.self_apply_inverse]

lemma neumannLocalize_scaled_isometry_coefficient
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (L : AmbientSpace →L[ℝ] AmbientSpace)
    (hL : L.IsInvertible) {ρ : ℝ} (hρ : 0 < ρ) :
    |(ρ • (Q : AmbientSpace →L[ℝ] AmbientSpace).comp L).det| •
        ((ρ • (Q : AmbientSpace →L[ℝ] AmbientSpace).comp L).inverse.comp
          (ρ • (Q : AmbientSpace →L[ℝ] AmbientSpace).comp L).inverse.adjoint) =
      ρ • (|L.det| • L.inverse.comp L.inverse.adjoint) := by
  have hdet : |(ρ • (Q : AmbientSpace →L[ℝ] AmbientSpace).comp L).det| =
      ρ ^ 3 * |L.det| := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_smul, LinearMap.det_comp,
      finrank_euclideanSpace, Fintype.card_fin, abs_mul, abs_pow, abs_of_pos hρ]
    rw [show |(Q : AmbientSpace →L[ℝ] AmbientSpace).toLinearMap.det| = 1 from
      neumannLocalize_abs_det_isometry Q, one_mul]
  have hinv : (ρ • (Q : AmbientSpace →L[ℝ] AmbientSpace).comp L).inverse =
      ρ⁻¹ • L.inverse.comp (Q.symm : AmbientSpace →L[ℝ] AmbientSpace) := by
    apply ContinuousLinearMap.inverse_eq
    · ext v
      simp [ContinuousLinearMap.comp_apply, hL.self_apply_inverse, hρ.ne']
    · ext v
      simp [ContinuousLinearMap.comp_apply, hL.inverse_apply_self, hρ.ne']
  rw [hdet, hinv]
  have hQ (v : AmbientSpace) : (Q.symm : AmbientSpace →L[ℝ] AmbientSpace)
      ((Q : AmbientSpace →L[ℝ] AmbientSpace) v) = v := Q.symm_apply_apply v
  apply ContinuousLinearMap.ext
  intro v
  simp only [map_smul, ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, smul_apply,
    ContinuousLinearMap.comp_apply, hQ, smul_smul]
  congr 1
  field_simp [hρ.ne']

/-- In dimension three, the positive scale contributes exactly one factor of
the radius to the normal coefficient; the rigid placement cancels. -/
theorem neumannLocalizeCoefficient_eq
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).IsInvertible) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y =
      ρ • boundaryNormalCoefficient c.height (graphAppendN a 0 + ρ • y) := by
  simp only [neumannLocalizeCoefficient, fderiv_neumannLocalizeMap c hψ,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  exact neumannLocalize_scaled_isometry_coefficient c.placement.linearIsometryEquiv _ hy hρ

/-- The coefficient relation can be used with the regularity assertion for
the actual placed chart returned by the localization theorem. -/
theorem neumannLocalizeCoefficient_eq_of_regular
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y =
      ρ • boundaryNormalCoefficient c.height (graphAppendN a 0 + ρ • y) := by
  apply neumannLocalizeCoefficient_eq c hψ a hρ
  let L := fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)
  have hinj : Function.Injective L := by
    intro v w hvw
    have heq : (fderiv ℝ (neumannLocalizeMap c a ρ) y) (ρ⁻¹ • v) =
        (fderiv ℝ (neumannLocalizeMap c a ρ) y) (ρ⁻¹ • w) := by
      simp only [fderiv_neumannLocalizeMap c hψ, ContinuousLinearMap.comp_apply,
        smul_apply, ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      exact congrArg c.placement.linearIsometryEquiv hvw
    exact (smul_right_injective _ (inv_ne_zero hρ.ne')) (hy.injective heq)
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv, rfl⟩

/-- Both face cross coefficients still vanish after placement and positive
scaling of the normal coordinates. -/
theorem neumannLocalizeCoefficient_cross_face
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    {y : AmbientSpace} (hy : y (Fin.last 2) = 0) {i : Fin 3} (hi : i ≠ Fin.last 2) :
    neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y
        (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
      neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y
        (EuclideanSpace.single (Fin.last 2) 1) i = 0 := by
  have hface : (graphAppendN a 0 + ρ • y) (Fin.last 2) = 0 := by
    simp only [PiLp.add_apply, graphAppendN_last, PiLp.smul_apply, hy, smul_zero, add_zero]
  have hreg : (fderiv ℝ (boundaryNormalChart c.height)
      (graphAppendN a 0 + ρ • y)).IsInvertible := by
    have heq : graphAppendN a 0 + ρ • y =
        graphAppendN (graphProjectionN 2 (graphAppendN a 0 + ρ • y)) 0 := by
      simpa only [hface] using (graphAppendN_projection (graphAppendN a 0 + ρ • y)).symm
    rw [heq, fderiv_boundaryNormalChart_face_equiv (hψ.of_le (by simp))]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [neumannLocalizeCoefficient_eq c hψ a hρ hreg]
  obtain ⟨h₁, h₂⟩ := boundaryNormalCoefficient_cross_face (hψ.of_le (by simp)) hface hi
  simpa only [smul_apply, PiLp.smul_apply, h₁, h₂, smul_zero] using
    (show (0 : ℝ) = 0 ∧ (0 : ℝ) = 0 from ⟨rfl, rfl⟩)

end LiquidDrop
