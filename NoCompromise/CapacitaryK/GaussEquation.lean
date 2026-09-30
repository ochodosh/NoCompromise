module

public import NoCompromise.CapacitaryK.GaussBonnetInput
public import Mathlib.Analysis.InnerProductSpace.Trace

@[expose] public section

/-!
# The Gauss equation on a regular level (chapter 31, input to `prop:K-measure-inequality`)

With the positive-sphere convention, the second fundamental form is the derivative of
the unit normal. Its tangential trace and determinant give `H` and `κ`, respectively, so
`|A|² = H² - 2κ` (`conv:curvature`), the identity `hA` used by `K_measure_ineq_level`, with `κ`
the Gauss curvature of `Surface/Geometry.lean` appearing in `lem:K-gauss-bonnet-input`.
-/

noncomputable section

open Set InnerProductSpace
open scoped Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The tangential divergence is the sum of the two tangential diagonal entries
in any orthonormal frame adapted to the normal. -/
lemma meanCurv_eq_frame {u : E3 → ℝ} {x : E3}
    (f : OrthonormalBasis (Fin 3) ℝ E3) (hf : f 2 = unitNormal u x) :
    meanCurv u x = secondFF u x (f 0) (f 0) + secondFF u x (f 1) (f 1) := by
  have htrace (b : OrthonormalBasis (Fin 3) ℝ E3) :
      LinearMap.trace ℝ E3 (fderiv ℝ (unitNormal u) x).toLinearMap =
        ∑ i, secondFF u x (b i) (b i) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  have hsum := (htrace (EuclideanSpace.basisFun (Fin 3) ℝ)).symm.trans (htrace f)
  simp only [EuclideanSpace.basisFun_apply] at hsum
  rw [meanCurv, hsum, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hf]
  ring

/-- Gauss equation on a regular level: with an orthonormal frame whose last vector is the
level normal,
`|A|² = H² - 2κ`, `κ` the Gauss curvature of the level for the normal `unitNormal u`. -/
theorem sum_secondFF_sq_eq_meanCurv_sq_sub_two_gaussCurvature
    {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {t : ℝ} (hsub : u ⁻¹' {t} ⊆ Ω)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) {x : E3} (hx : u x = t)
    (f : OrthonormalBasis (Fin 3) ℝ E3) (hf : f 2 = unitNormal u x) :
    (∑ a : Fin 2, ∑ b : Fin 2, secondFF u x (f a.castSucc) (f b.castSucc) ^ 2) =
      meanCurv u x ^ 2 - 2 * gaussCurvature (u ⁻¹' {t}) (unitNormal u) x := by
  classical
  have hxS : x ∈ u ⁻¹' {t} := hx
  have hS := isSmoothEmbeddedSurface_level hΩ hu hsub hreg
  have hn := isUnitNormalField_level hΩ hu hsub hreg
  have hmem (a : Fin 2) : f a.castSucc ∈ tangentPlane (u ⁻¹' {t}) x := by
    rw [hn.tangentPlane_eq hS hxS,
      Submodule.mem_orthogonal_singleton_iff_inner_right, ← hf]
    exact f.orthonormal.inner_eq_zero (by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      omega)
  let v : Fin 2 → tangentPlane (u ⁻¹' {t}) x := fun a => ⟨f a.castSucc, hmem a⟩
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    change ⟪f a.castSucc, f b.castSucc⟫ = _
    simpa using (orthonormal_iff_ite.mp f.orthonormal) a.castSucc b.castSucc
  let b : OrthonormalBasis (Fin 2) ℝ (tangentPlane (u ⁻¹' {t}) x) :=
    OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [hS.finrank_tangentPlane hxS])).ge
  have hb (a : Fin 2) : (b a : E3) = f a.castSucc := by
    simp [b, v]
  have hmatrix (i j : Fin 2) :
      LinearMap.toMatrix b.toBasis b.toBasis
        (tangentShapeOperator (u ⁻¹' {t}) (unitNormal u) x).toLinearMap i j =
      secondFF u x (f j.castSucc) (f i.castSucc) := by
    rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    change ⟪(b i : E3), (tangentShapeOperator (u ⁻¹' {t}) (unitNormal u) x (b j) : E3)⟫ = _
    rw [hn.coe_tangentShapeOperator hS hxS, hb, hb]
    exact real_inner_comm _ _
  have hdet : gaussCurvature (u ⁻¹' {t}) (unitNormal u) x =
      secondFF u x (f 0) (f 0) * secondFF u x (f 1) (f 1) -
        secondFF u x (f 1) (f 0) * secondFF u x (f 0) (f 1) := by
    rw [gaussCurvature, ← LinearMap.det_toMatrix b.toBasis, Matrix.det_fin_two]
    simp only [hmatrix]
    rfl
  have hsym : secondFF u x (f 0) (f 1) = secondFF u x (f 1) (f 0) :=
    secondFundamentalForm_symm hS hn hxS (hmem 0) (hmem 1)
  rw [meanCurv_eq_frame f hf, hdet]
  simp only [Fin.sum_univ_two, Fin.castSucc_zero, Fin.castSucc_one]
  rw [hsym]
  ring

end LiquidDrop.CapacitaryK
