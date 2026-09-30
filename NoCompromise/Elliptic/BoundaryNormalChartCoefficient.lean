module

public import NoCompromise.Elliptic.BoundaryNormalChartInverse
public import Mathlib.Analysis.Calculus.Deriv.Abs

@[expose] public section

/-!
# The Dirichlet coefficient in normal graph coordinates

The coefficient includes the absolute Jacobian determinant and the inverse
derivative times its adjoint, as required by the pullback of the Dirichlet form.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

/-- The divergence-form coefficient associated with normal graph coordinates. -/
def boundaryNormalCoefficient (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  |(fderiv ℝ (boundaryNormalChart ψ) y).det| •
    ((fderiv ℝ (boundaryNormalChart ψ) y).inverse.comp
      (fderiv ℝ (boundaryNormalChart ψ) y).inverse.adjoint)

/-- The determinant is a smooth polynomial in the entries of a Euclidean operator. -/
lemma boundaryNormal_contDiff_det {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L.det) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
      L.det = Matrix.det (Matrix.of (fun i j : Fin 3 => L (EuclideanSpace.single j 1) i)) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
  simp_rw [he, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) (σ i)).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

lemma boundaryNormal_det_ne_zero
    {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hL : L.IsInvertible) : L.det ≠ 0 := by
  obtain ⟨e, rfl⟩ := hL
  exact e.toLinearEquiv.isUnit_det'.ne_zero

lemma boundaryNormal_isInvertible_iff_det_ne_zero
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    L.IsInvertible ↔ L.det ≠ 0 := by
  refine ⟨boundaryNormal_det_ne_zero, fun h => ?_⟩
  have hk : L.toLinearMap.ker = ⊥ := by
    by_contra hk
    exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap
    (LinearMap.ker_eq_bot.mp hk)).toContinuousLinearEquiv, rfl⟩

theorem isOpen_boundaryNormalChart_regular
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    IsOpen {x | (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible} := by
  have hD := (smooth_boundaryNormalChart hψ).continuous_fderiv (by simp)
  have ho : IsOpen {t : ℝ | t ≠ 0} := isOpen_ne
  simp only [boundaryNormal_isInvertible_iff_det_ne_zero]
  convert! ho.preimage (ContinuousLinearMap.continuous_det.comp hD) using 1

/-- A face chart can be chosen with smooth inverse on its whole open target
and invertible derivative on its whole open source. -/
theorem boundaryNormalChart_local_diffeomorphism_on
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) = boundaryNormalChart ψ ∧
      graphAppendN x 0 ∈ e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ y ∈ e.source, (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible := by
  obtain ⟨e₀, he₀, hx, _⟩ := boundaryNormalChart_local_diffeomorphism hψ x
  let U := {y | (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible}
  let e := e₀.restrOpen U (isOpen_boundaryNormalChart_regular hψ)
  have he : (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) =
      boundaryNormalChart ψ := he₀
  have hreg : ∀ y ∈ e.source, (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible :=
    fun y hy => hy.2
  refine ⟨e, he, ⟨hx, ?_⟩, ?_, ?_, hreg⟩
  · change (fderiv ℝ (boundaryNormalChart ψ) (graphAppendN x 0)).IsInvertible
    rw [fderiv_boundaryNormalChart_face_equiv (hψ.of_le (by simp))]
    exact ContinuousLinearMap.isInvertible_equiv
  · rw [he]
    exact (smooth_boundaryNormalChart hψ).contDiffOn
  · intro y hy
    obtain ⟨L, hL⟩ := hreg (e.symm y) (e.map_target hy)
    have hd : HasFDerivAt e (L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) (e.symm y) := by
      rw [he, hL]
      exact ((smooth_boundaryNormalChart hψ).differentiable (by simp) _).hasFDerivAt
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) e (e.symm y) := by
      rw [he]
      exact (smooth_boundaryNormalChart hψ).contDiffAt
    exact (e.contDiffAt_symm hy hd hc).contDiffWithinAt

/-- The normal coefficient is smooth at every point with invertible chart derivative. -/
theorem contDiffAt_boundaryNormalCoefficient
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {y : EuclideanSpace ℝ (Fin 3)}
    (hy : (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible) :
    ContDiffAt ℝ (⊤ : ℕ∞) (boundaryNormalCoefficient ψ) y := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (boundaryNormalChart ψ)) :=
    (smooth_boundaryNormalChart hψ).fderiv_right (by simp)
  have hI := hy.contDiffAt_map_inverse.comp y hD.contDiffAt
  have hJ := (contDiffAt_abs (boundaryNormal_det_ne_zero hy)).comp y
    (boundaryNormal_contDiff_det.contDiffAt.comp y hD.contDiffAt)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L.adjoint) :=
    (ContinuousLinearMap.adjoint :
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))).contDiff
  exact hJ.smul (hI.clm_comp (hA.contDiffAt.comp y hI))

/-- Symmetry holds even at points where the totalized inverse is zero. -/
theorem boundaryNormalCoefficient_symmetric (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (boundaryNormalCoefficient ψ y v) w =
      inner ℝ v (boundaryNormalCoefficient ψ y w) := by
  let B := (fderiv ℝ (boundaryNormalChart ψ) y).inverse
  simp only [boundaryNormalCoefficient, smul_apply,
    ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
  rw [← B.adjoint_inner_right (B.adjoint v) w, ← B.adjoint_inner_left (B.adjoint w) v]

/-- The quadratic form is an absolute Jacobian times a squared norm. -/
lemma boundaryNormalCoefficient_quadratic (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (boundaryNormalCoefficient ψ y v) =
      |(fderiv ℝ (boundaryNormalChart ψ) y).det| *
        ‖(fderiv ℝ (boundaryNormalChart ψ) y).inverse.adjoint v‖ ^ 2 := by
  simp only [boundaryNormalCoefficient, smul_apply,
    ContinuousLinearMap.comp_apply, real_inner_smul_right]
  rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- The Gram form has no mixed tangential-normal terms. -/
lemma boundaryNormalLinear_inner (p : EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (boundaryNormalLinear p v) (boundaryNormalLinear p w) =
      inner ℝ (graphProjectionN 2 v) (graphProjectionN 2 w) +
      inner ℝ p (graphProjectionN 2 v) * inner ℝ p (graphProjectionN 2 w) +
      v (Fin.last 2) * w (Fin.last 2) * (1 + ‖p‖ ^ 2) := by
  rw [boundaryNormalLinear_apply, boundaryNormalLinear_apply, inner_graphAppendN,
    graphProjectionN_append, graphAppendN_last]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (graphProjectionN 2 v) p]
  ring

lemma boundaryNormalLinear_gram_last (p : EuclideanSpace ℝ (Fin 2)) :
    (boundaryNormalLinear p).adjoint
      (boundaryNormalLinear p (EuclideanSpace.single (Fin.last 2) 1)) =
        (1 + ‖p‖ ^ 2) • EuclideanSpace.single (Fin.last 2) 1 := by
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, boundaryNormalLinear_inner]
  have hp : graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) 1) = 0 := by
    ext i
    simp only [graphProjectionN_apply, PiLp.single_apply, PiLp.zero_apply,
      Fin.castSucc_ne_last, ite_false]
  rw [hp]
  simp [real_inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]

/-- Inverse Gram operators preserve the normal axis at a face point. -/
lemma boundaryNormalLinear_inverse_gram_last (p : EuclideanSpace ℝ (Fin 2)) :
    (boundaryNormalLinear p).inverse
      ((boundaryNormalLinear p).inverse.adjoint (EuclideanSpace.single (Fin.last 2) 1)) =
        (1 + ‖p‖ ^ 2)⁻¹ • EuclideanSpace.single (Fin.last 2) 1 := by
  let L := boundaryNormalLinear p
  have hL : L.IsInvertible := ⟨boundaryNormalLinearEquiv p, rfl⟩
  have hstar : L.inverse.adjoint.comp L.adjoint = ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hL.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have he := congrArg (fun v => L.inverse (L.inverse.adjoint v))
    (boundaryNormalLinear_gram_last p)
  have hc (v : EuclideanSpace ℝ (Fin 3)) : L.inverse.adjoint (L.adjoint v) = v :=
    congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hstar
  change L.inverse (L.inverse.adjoint (L.adjoint (L _))) = _ at he
  rw [hc, hL.inverse_apply_self, map_smul, map_smul] at he
  have hn : (1 + ‖p‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  calc
    _ = (1 + ‖p‖ ^ 2)⁻¹ • ((1 + ‖p‖ ^ 2) •
        L.inverse (L.inverse.adjoint (EuclideanSpace.single (Fin.last 2) 1))) := by
      rw [inv_smul_smul₀ hn]
    _ = _ := by rw [← he]

/-- Both cross coefficients vanish on the face, in the indexing used by the
flat Neumann regularity theorem. -/
theorem boundaryNormalCoefficient_cross_face
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x (Fin.last 2) = 0)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    boundaryNormalCoefficient ψ x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
      boundaryNormalCoefficient ψ x (EuclideanSpace.single (Fin.last 2) 1) i = 0 := by
  have hx' : x = graphAppendN (graphProjectionN 2 x) 0 := by
    simpa only [hx] using (graphAppendN_projection x).symm
  have hnormal : boundaryNormalCoefficient ψ x (EuclideanSpace.single (Fin.last 2) 1) i = 0 := by
    conv_lhs => rw [hx']
    simp only [boundaryNormalCoefficient, fderiv_boundaryNormalChart_face hψ,
      smul_apply, ContinuousLinearMap.comp_apply, boundaryNormalLinear_inverse_gram_last,
      PiLp.smul_apply]
    simp only [PiLp.single_apply, ite_eq_right hi, smul_eq_mul, mul_zero]
  refine ⟨?_, hnormal⟩
  have hs := boundaryNormalCoefficient_symmetric ψ x
    (EuclideanSpace.single i 1) (EuclideanSpace.single (Fin.last 2) 1)
  have hs' : boundaryNormalCoefficient ψ x (EuclideanSpace.single i 1) (Fin.last 2) =
      boundaryNormalCoefficient ψ x (EuclideanSpace.single (Fin.last 2) 1) i := by
    simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
      RCLike.conj_to_real, mul_one, one_mul] using hs
  exact hs'.trans hnormal

/-- The adjoint of an invertible Euclidean operator is invertible. -/
lemma boundaryNormal_adjoint_invertible
    {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hL : L.IsInvertible) : L.adjoint.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := L.inverse.adjoint)
  · rw [← ContinuousLinearMap.adjoint_comp, hL.inverse_comp_self,
      ContinuousLinearMap.adjoint_id]
  · rw [← ContinuousLinearMap.adjoint_comp, hL.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]

/-- The coefficient is positive definite wherever the chart derivative is invertible. -/
theorem boundaryNormalCoefficient_pos
    (ψ : EuclideanSpace ℝ (Fin 2) → ℝ) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    0 < inner ℝ v (boundaryNormalCoefficient ψ y v) := by
  rw [boundaryNormalCoefficient_quadratic]
  apply mul_pos (abs_pos.mpr (boundaryNormal_det_ne_zero hy))
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact fun h => hv ((boundaryNormal_adjoint_invertible hy.inverse).injective
    (h.trans (map_zero _).symm))

/-- On a compact subset of the invertibility set there are uniform positive
ellipticity and finite operator-norm constants. -/
theorem boundaryNormalCoefficient_compact_bounds
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K,
      ‖boundaryNormalCoefficient ψ x‖ ≤ C ∧
      ∀ v : EuclideanSpace ℝ (Fin 3),
        c * ‖v‖ ^ 2 ≤ inner ℝ v (boundaryNormalCoefficient ψ x v) := by
  have hA : ContinuousOn (boundaryNormalCoefficient ψ) K := fun x hx =>
    (contDiffAt_boundaryNormalCoefficient hψ (hreg x hx)).continuousAt.continuousWithinAt
  have hQ : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      inner ℝ z.2 (boundaryNormalCoefficient ψ z.1 z.2)) (K ×ˢ sphere 0 1) :=
    continuous_snd.continuousOn.inner
      ((hA.comp continuous_fst.continuousOn (fun z hz => hz.1)).clm_apply
        continuous_snd.continuousOn)
  obtain ⟨c, hc, hcall⟩ := (hK.prod (isCompact_sphere 0 1)).exists_forall_le' hQ
    (show ∀ z ∈ K ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      0 < inner ℝ z.2 (boundaryNormalCoefficient ψ z.1 z.2) from by
      intro z hz
      apply boundaryNormalCoefficient_pos ψ (hreg z.1 hz.1)
      intro he
      simpa [he] using hz.2)
  obtain ⟨C, hC, hCall⟩ := (hK.image_of_continuousOn hA).isBounded.exists_pos_norm_le
  refine ⟨c, hc, C, hC, fun x hx => ⟨hCall _ (mem_image_of_mem _ hx), ?_⟩⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let w := ‖v‖⁻¹ • v
  have hw : w ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm hv
  have he : ‖v‖ ^ 2 * inner ℝ w (boundaryNormalCoefficient ψ x w) =
      inner ℝ v (boundaryNormalCoefficient ψ x v) := by
    dsimp only [w]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    c * ‖v‖ ^ 2 = ‖v‖ ^ 2 * c := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * inner ℝ w (boundaryNormalCoefficient ψ x w) :=
      mul_le_mul_of_nonneg_left (hcall (x, w) ⟨hx, hw⟩) (sq_nonneg _)
    _ = _ := he

end LiquidDrop
