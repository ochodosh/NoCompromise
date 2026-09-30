module

public import NoCompromise.Elliptic.BoundaryC2aCurvedHolder

@[expose] public section

/-!
# `thm:boundary-C2a` in a shear chart with a C^{2,α} height

For a graph chart with height `h` and placement `P`, the shear flattening
`Θ y = P (a + ρ y', h (a + ρ y') - ρ yₙ)` is the sum of an affine map and
`y ↦ h (a + ρ y') • P_lin eₙ`. Hence `DΘ y = ℓ + K (Dh (a + ρ y'))` for a fixed linear map
`ℓ` and a fixed continuous linear map `K`, and `D²Θ y = K ∘ D²h (a + ρ y') ∘ (ρ π)` with `π`
the projection to the first two coordinates. A C² height whose second derivative is
α-Hölder on a set containing the feet `a + ρ y'` of the closed unit half ball therefore gives
`DΘ ∈ C^{1,α}` there, which is the hypothesis of `boundary_c2a_curved_half_ball_holder`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The affine-linear part of the shear chart, without the height term. -/
def boundaryShearHolderLinear (c : C1BoundaryChart) (ρ : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (c.placement.linearIsometryEquiv.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
    (ρ • ((graphBaseN 2).comp (graphProjectionN 2) -
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (Fin.last 2) (1 : ℝ))))

/-- The image under the linear part of the placement of the last basis vector. -/
def boundaryShearHolderNormal (c : C1BoundaryChart) : EuclideanSpace ℝ (Fin 3) :=
  c.placement.linearIsometryEquiv (EuclideanSpace.single (Fin.last 2) (1 : ℝ))

/-- The shear chart is an affine map plus the height term. -/
lemma boundaryShearHolder_eq (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    boundaryShearMap c a ρ = fun y => c.placement (graphBaseN 2 a) +
      boundaryShearHolderLinear c ρ y +
      c.height (a + (ρ • graphProjectionN 2) y) • boundaryShearHolderNormal c := by
  funext y
  have hP : ∀ z w : EuclideanSpace ℝ (Fin 3),
      c.placement (z + w) = c.placement z + c.placement.linearIsometryEquiv w := by
    intro z w
    have := c.placement.map_vadd z w
    simpa [vadd_eq_add, add_comm] using this
  simp only [boundaryShearMap, boundaryShearBase, graphAppendN, map_add, map_smul]
  rw [hP, hP]
  simp only [boundaryShearHolderLinear, boundaryShearHolderNormal,
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    sub_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, map_sub, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, PiLp.smul_apply, smul_eq_mul, sub_smul,
    mul_smul]
  simp only [EuclideanSpace.proj, PiLp.proj_apply]
  module

/-- The derivative of the shear chart. -/
lemma boundaryShearHolder_fderiv (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (hh : ContDiff ℝ 1 c.height) (y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (boundaryShearMap c a ρ) y = boundaryShearHolderLinear c ρ +
      ((fderiv ℝ c.height (a + (ρ • graphProjectionN 2) y)).comp
        (ρ • graphProjectionN 2)).smulRight (boundaryShearHolderNormal c) := by
  rw [boundaryShearHolder_eq]
  have hψ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => a + (ρ • graphProjectionN 2) y)
      (ρ • graphProjectionN 2) y :=
    ((ρ • graphProjectionN 2 : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)).hasFDerivAt).const_add a
  have hhd : HasFDerivAt c.height (fderiv ℝ c.height (a + (ρ • graphProjectionN 2) y))
      (a + (ρ • graphProjectionN 2) y) :=
    ((hh.differentiable one_ne_zero) _).hasFDerivAt
  have hs := (hhd.comp y hψ).smul_const (boundaryShearHolderNormal c)
  have hl := ((boundaryShearHolderLinear c ρ).hasFDerivAt (x := y)).const_add
    (c.placement (graphBaseN 2 a))
  exact (hl.add hs).fderiv

/-- The fixed linear map sending `Dh` to the height part of `DΘ`. -/
def boundaryShearHolderK (c : C1BoundaryChart) (ρ : ℝ) :
    (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
  ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3))).flip (boundaryShearHolderNormal c)).comp
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 2)) ℝ).flip
      (ρ • graphProjectionN 2))

lemma boundaryShearHolder_fderiv_eq (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (hh : ContDiff ℝ 1 c.height) :
    fderiv ℝ (boundaryShearMap c a ρ) = fun y => boundaryShearHolderLinear c ρ +
      boundaryShearHolderK c ρ (fderiv ℝ c.height (a + (ρ • graphProjectionN 2) y)) := by
  funext y
  rw [boundaryShearHolder_fderiv c a ρ hh y]
  rfl

/-- The second derivative of the shear chart. -/
lemma boundaryShearHolder_fderiv_fderiv (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (hh : ContDiff ℝ 2 c.height) (y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fderiv ℝ (boundaryShearMap c a ρ)) y =
      (boundaryShearHolderK c ρ).comp
        ((fderiv ℝ (fderiv ℝ c.height) (a + (ρ • graphProjectionN 2) y)).comp
          (ρ • graphProjectionN 2)) := by
  rw [boundaryShearHolder_fderiv_eq c a ρ (hh.of_le (by norm_num))]
  have hψ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => a + (ρ • graphProjectionN 2) y)
      (ρ • graphProjectionN 2) y :=
    ((ρ • graphProjectionN 2 : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)).hasFDerivAt).const_add a
  have hD : ContDiff ℝ 1 (fderiv ℝ c.height) := hh.fderiv_right (by norm_num)
  have hhd : HasFDerivAt (fderiv ℝ c.height)
      (fderiv ℝ (fderiv ℝ c.height) (a + (ρ • graphProjectionN 2) y))
      (a + (ρ • graphProjectionN 2) y) :=
    ((hD.differentiable one_ne_zero) _).hasFDerivAt
  have hK := ((boundaryShearHolderK c ρ).hasFDerivAt.comp y (hhd.comp y hψ)).const_add
    (boundaryShearHolderLinear c ρ)
  exact hK.fderiv

/-- A C² height whose second derivative is α-Hölder on a set containing the feet of the
closed unit half ball gives a shear chart with `DΘ ∈ C^{1,α}` on the closed unit half ball. -/
theorem boundaryShearHolder_hasC1HolderOn_fderiv {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (hh : ContDiff ℝ 2 c.height) {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : ∀ y ∈ closure (boundaryHalfBall 1), a + (ρ • graphProjectionN 2) y ∈ S)
    {Ch : ℝ} (hhol : ∀ x ∈ S, ∀ x' ∈ S,
      ‖fderiv ℝ (fderiv ℝ c.height) x - fderiv ℝ (fderiv ℝ c.height) x'‖ ≤ Ch * dist x x' ^ α) :
    HasC1HolderOn α (fderiv ℝ (boundaryShearMap c a ρ)) (closure (boundaryHalfBall 1)) := by
  set K := closure (boundaryHalfBall (1 : ℝ)) with hK_def
  have hKc : IsCompact K := boundaryC2aCurved_isCompact_closure_halfBall
  have hKv : Convex ℝ K := (convex_boundaryHalfBall 1).closure
  have hΘ : ContDiff ℝ 2 (boundaryShearMap c a ρ) := by
    have h := contDiff_boundaryShearMap c a ρ (n := 2) (by simpa using hh)
    simpa using h
  have hΘ1 : ContDiff ℝ 1 (fderiv ℝ (boundaryShearMap c a ρ)) := hΘ.fderiv_right (by norm_num)
  have hfun := (hasC1HolderOn_of_contDiffOn_two hα.le hα1 hKc hKv isOpen_univ (subset_univ K)
    hΘ.contDiffOn).derivative_holder
  -- the second derivative is bounded on the compact set
  obtain ⟨A, hA⟩ := hKc.exists_bound_of_continuousOn
    (hΘ1.continuous_fderiv one_ne_zero).continuousOn
  set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) := ρ • graphProjectionN 2
  set Ch' := max Ch 0
  set B := ‖boundaryShearHolderK c ρ‖ * (Ch' * ‖L‖ ^ α * ‖L‖) with hB_def
  have hB : 0 ≤ B := by positivity
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  refine ⟨hΘ1.contDiffOn, hfun, HasFiniteHolderNormOn.of_bounds hA0 hB
    (fun x hx => (hA x hx).trans (le_max_left _ _)) ?_⟩
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simpa using hB
  have hpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  rw [div_le_iff₀ hpos, boundaryShearHolder_fderiv_fderiv c a ρ hh,
    boundaryShearHolder_fderiv_fderiv c a ρ hh, ← ContinuousLinearMap.comp_sub,
    ← ContinuousLinearMap.sub_comp]
  set D := fderiv ℝ (fderiv ℝ c.height)
  have hd : ‖(a + L x) - (a + L y)‖ ≤ ‖L‖ * ‖x - y‖ := by
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact L.le_opNorm _
  have hH : ‖D (a + L x) - D (a + L y)‖ ≤ Ch' * (‖L‖ ^ α * ‖x - y‖ ^ α) := by
    have h1 := hhol _ (hS x hx) _ (hS y hy)
    rw [dist_eq_norm] at h1
    have h2 : ‖(a + L x) - (a + L y)‖ ^ α ≤ (‖L‖ * ‖x - y‖) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hd hα.le
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at h2
    calc ‖D (a + L x) - D (a + L y)‖ ≤ Ch * ‖(a + L x) - (a + L y)‖ ^ α := h1
      _ ≤ Ch' * ‖(a + L x) - (a + L y)‖ ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ Ch' * (‖L‖ ^ α * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  calc ‖(boundaryShearHolderK c ρ).comp ((D (a + L x) - D (a + L y)).comp L)‖
      ≤ ‖boundaryShearHolderK c ρ‖ * (‖D (a + L x) - D (a + L y)‖ * ‖L‖) :=
        ((boundaryShearHolderK c ρ).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖boundaryShearHolderK c ρ‖ * (Ch' * (‖L‖ ^ α * ‖x - y‖ ^ α) * ‖L‖) := by
        gcongr
    _ = B * ‖x - y‖ ^ α := by rw [hB_def]; ring

/-- **`thm:boundary-C2a` in a shear chart with a C^{2,α} height.** For a graph chart whose
height is C², globally Lipschitz, with second derivative α-Hölder on a set `S` containing the
feet `a + ρ y'` of the closed unit half ball, and `ρ ≠ 0`, the conclusion of
`boundary_c2a_curved_half_ball_holder` holds for the shear flattening
`Θ = boundaryShearMap c a ρ`, with coefficient and datum `A`, `G` C¹ near
`Θ(closure B⁺₁)` and `A ∘ Θ`, `G ∘ Θ`, `∇(φ ∘ Θ)` C^{1,α} on the closed unit half ball. -/
theorem boundary_c2a_shear_half_ball_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hh : ContDiff ℝ 2 c.height) {Lh : ℝ≥0} (hhlip : LipschitzWith Lh c.height)
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : ∀ y ∈ closure (boundaryHalfBall 1), a + (ρ • graphProjectionN 2) y ∈ S)
    {Ch : ℝ} (hhol : ∀ x ∈ S, ∀ x' ∈ S,
      ‖fderiv ℝ (fderiv ℝ c.height) x - fderiv ℝ (fderiv ℝ c.height) x'‖ ≤ Ch * dist x x' ^ α)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : boundaryShearMap c a ρ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 1 A W) (hG : ContDiffOn ℝ 1 G W)
    (hAΘ : HasC1HolderOn α (A ∘ boundaryShearMap c a ρ) (closure (boundaryHalfBall 1)))
    (hGΘ : HasC1HolderOn α (G ∘ boundaryShearMap c a ρ) (closure (boundaryHalfBall 1)))
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ boundaryShearMap c a ρ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hφ : ContDiff ℝ 2 φ)
    (hgφΘ : HasC1HolderOn α (gradient (φ ∘ boundaryShearMap c a ρ))
      (closure (boundaryHalfBall 1)))
    (hu : HasH1GradientOn u F (boundaryShearMap c a ρ '' boundaryHalfBall 1))
    (hw : IsWeakDivergenceEquationOn A F G (boundaryShearMap c a ρ '' boundaryHalfBall 1))
    (htr : HasZeroFlatTraceOn
      (fun y => u (boundaryShearMap c a ρ y) - φ (boundaryShearMap c a ρ y))
      (fun y => (fderiv ℝ (boundaryShearMap c a ρ) y).adjoint (F (boundaryShearMap c a ρ y)) -
        gradient (φ ∘ boundaryShearMap c a ρ) y) (ball 0 1)) :
    ∃ C > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      v =ᵐ[volume.restrict (boundaryShearMap c a ρ '' boundaryHalfBall (1 / 2))] u ∧
      ContDiffOn ℝ 2 (v ∘ boundaryShearMap c a ρ) (boundaryHalfBall (1 / 2)) ∧
      (∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry (v ∘ boundaryShearMap c a ρ) x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry (v ∘ boundaryShearMap c a ρ) x i j -
            boundaryNeumannC2Entry (v ∘ boundaryShearMap c a ρ) y i j| ≤ C * dist x y ^ α) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), |(v ∘ boundaryShearMap c a ρ) x| ≤ C) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), ‖gradient (v ∘ boundaryShearMap c a ρ) x‖ ≤ C) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
        ‖gradient (v ∘ boundaryShearMap c a ρ) x - gradient (v ∘ boundaryShearMap c a ρ) y‖ ≤
          C * dist x y ^ α) := by
  obtain ⟨CΘ, hCΘ⟩ := boundaryShearMap_lipschitz c a ρ hhlip
  obtain ⟨KΘ, hKΘ⟩ := boundaryShearInv_lipschitz c a ρ hhlip
  have hΘ : ContDiff ℝ 2 (boundaryShearMap c a ρ) := by
    have h := contDiff_boundaryShearMap c a ρ (n := 2) (by simpa using hh)
    simpa using h
  have hΘi : ContDiff ℝ 1 (boundaryShearInv c a ρ) := by
    have h := contDiff_boundaryShearInv c a ρ (n := 1) (by simpa using hh.of_le (by norm_num))
    simpa using h
  exact boundary_c2a_curved_half_ball_holder hα hα1 hΘ hΘi
    (boundaryShearMap_leftInverse c a hρ) (boundaryShearMap_rightInverse c a hρ) hCΘ hKΘ
    (boundaryShearHolder_hasC1HolderOn_fderiv hα hα1.le c a ρ hh hS hhol) hW hWΘ hA hG hAΘ hGΘ
    hlamA hAe hφ hgφΘ hu hw htr

end LiquidDrop
