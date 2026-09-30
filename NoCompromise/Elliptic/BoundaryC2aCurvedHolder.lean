module

public import NoCompromise.Elliptic.BoundaryC2aCurved
public import NoCompromise.Elliptic.BoundaryNeumannC2HolderAlgebra

@[expose] public section

/-!
# `thm:boundary-C2a` for a curved boundary with the TeX regularity

In shear (graph) coordinates the derivative of the flattening map has the regularity of the
derivative of the height, so a C^{2,α} boundary gives `Θ ∈ C²` with `DΘ ∈ C^{1,α}`. With
`A ∘ Θ`, `G ∘ Θ` in `C^{1,α}`, the pulled-back coefficient `|det DΘ| DΘ⁻¹ (A ∘ Θ) DΘ⁻ᵀ` and datum
`|det DΘ| DΘ⁻¹ (G ∘ Θ)` are again `C^{1,α}`: the determinant is a polynomial in the entries,
its absolute value is a fixed sign times the determinant, and the inverse is C^{1,α} because
`D(L⁻¹) = -L⁻¹ (DL) L⁻¹`. The curved estimate then follows from the flat one exactly as in
`boundary_c2a_curved_half_ball`, with the weaker hypotheses.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Composition with a C¹ map of a finite-dimensional space preserves C⁰,α. -/
lemma boundaryC2aCurvedHolder_holder_comp {E R S : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    {α : ℝ} {g : R → S} (hg : ContDiff ℝ 1 g) {f : E → R} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) :
    HasFiniteHolderNormOn α (fun x => g (f x)) U := by
  set r := holderUniformNorm f U
  have hr : 0 ≤ r := holderUniformNorm_nonneg hf.uniform_bounded
  have hfr : ∀ x ∈ U, f x ∈ closedBall (0 : R) r := fun x hx =>
    mem_closedBall_zero_iff.mpr (norm_le_holderUniformNorm hf.uniform_bounded hx)
  have hKc := isCompact_closedBall (0 : R) r
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨D, hD⟩ :=
    hKc.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  have h0 : (0 : R) ∈ closedBall (0 : R) r := mem_closedBall_self hr
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 h0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 h0)
  refine HasFiniteHolderNormOn.of_bounds (A := C) (B := D * holderSeminorm α f U) hC0
    (mul_nonneg hD0 hf.seminorm_nonneg) (fun x hx => hC _ (hfr x hx)) ?_
  intro x hx y hy
  have hlip : ‖g (f x) - g (f y)‖ ≤ D * ‖f x - f y‖ :=
    (convex_closedBall (0 : R) r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hg.differentiable one_ne_zero z) (fun z hz => hD z hz) (hfr y hy) (hfr x hx)
  calc ‖g (f x) - g (f y)‖ / ‖x - y‖ ^ α ≤ D * ‖f x - f y‖ / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right hlip (by positivity)
    _ = D * (‖f x - f y‖ / ‖x - y‖ ^ α) := mul_div_assoc _ _ _
    _ ≤ D * holderSeminorm α f U :=
        mul_le_mul_of_nonneg_left (schauder_holder_quotient_le hf hx hy) hD0

/-- Composition with a C² map of a finite-dimensional space preserves C¹,α, when the inner map is
C¹ on an open neighbourhood `O` of the set. -/
theorem boundaryC2aCurvedHolder_c1Holder_comp {E R S : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    {α : ℝ} {g : R → S} (hg : ContDiff ℝ 2 g) {f : E → R} {U O : Set E} (hO : IsOpen O)
    (hUO : U ⊆ O) (hfO : ContDiffOn ℝ 1 f O) (hf : HasC1HolderOn α f U) :
    HasC1HolderOn α (fun x => g (f x)) U ∧ ContDiffOn ℝ 1 (fun x => g (f x)) O := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hDg : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have h0 := boundaryC2aCurvedHolder_holder_comp hg1 hf.function_holder
  have h1 := boundaryC2aCurvedHolder_holder_comp hDg hf.function_holder
  obtain ⟨h2, -⟩ := nondiv_holder_bilinear h1 hf.derivative_holder
    (ContinuousLinearMap.compL ℝ E R S)
  obtain ⟨h3, -⟩ := boundaryNeumann_holder_congr h2 (g := fderiv ℝ (fun x => g (f x)))
    (fun x hx => by
      have hfd : DifferentiableAt ℝ f x :=
        (hfO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hUO hx))
      rw [ContinuousLinearMap.compL_apply]
      exact ((hg1.differentiable one_ne_zero (f x)).hasFDerivAt.comp x
        hfd.hasFDerivAt).fderiv.symm)
  exact ⟨⟨hg1.comp_contDiffOn hf.contDiff, h0, h3⟩, hg1.comp_contDiffOn hfO⟩

/-- The C⁰,α bound for the inverse of an invertible-operator-valued map with bounded inverse. -/
lemma boundaryC2aCurvedHolder_holder_inverse {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α B : ℝ} (hB : 0 ≤ B) {L : E → F →L[ℝ] F} {U : Set E}
    (hL : HasFiniteHolderNormOn α L U) (hinv : ∀ x ∈ U, (L x).IsInvertible)
    (hbd : ∀ x ∈ U, ‖(L x).inverse‖ ≤ B) :
    HasFiniteHolderNormOn α (fun x => (L x).inverse) U := by
  refine HasFiniteHolderNormOn.of_bounds (A := B) (B := B * B * holderSeminorm α L U) hB
    (by have := hL.seminorm_nonneg; positivity) hbd ?_
  intro x hx y hy
  have hid : (L x).inverse - (L y).inverse =
      (L x).inverse ∘L ((L y - L x) ∘L (L y).inverse) := by
    rw [ContinuousLinearMap.sub_comp, (hinv y hy).self_comp_inverse,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      ← ContinuousLinearMap.comp_assoc, (hinv x hx).inverse_comp_self,
      ContinuousLinearMap.id_comp]
  have hn : ‖(L x).inverse - (L y).inverse‖ ≤ B * B * ‖L x - L y‖ := by
    rw [hid]
    calc _ ≤ ‖(L x).inverse‖ * ‖(L y - L x) ∘L (L y).inverse‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(L x).inverse‖ * (‖L y - L x‖ * ‖(L y).inverse‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ B * (‖L x - L y‖ * B) := by
          rw [norm_sub_rev (L y)]
          exact mul_le_mul (hbd x hx) (mul_le_mul_of_nonneg_left (hbd y hy) (norm_nonneg _))
            (by positivity) hB
      _ = B * B * ‖L x - L y‖ := by ring
  calc _ ≤ B * B * ‖L x - L y‖ / ‖x - y‖ ^ α := div_le_div_of_nonneg_right hn (by positivity)
    _ = B * B * (‖L x - L y‖ / ‖x - y‖ ^ α) := mul_div_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (schauder_holder_quotient_le hL hx hy) (by positivity)

/-- The derivative of `x ↦ (L x)⁻¹` at a point where `L x` is invertible. -/
lemma boundaryC2aCurvedHolder_fderiv_inverse {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {L : E → F →L[ℝ] F} {x : E} (hLd : DifferentiableAt ℝ L x) (hinv : (L x).IsInvertible) :
    fderiv ℝ (fun y => (L y).inverse) x =
      (-ContinuousLinearMap.mulLeftRight ℝ (F →L[ℝ] F) (L x).inverse (L x).inverse).comp
        (fderiv ℝ L x) := by
  obtain ⟨e, he⟩ := hinv
  have hr := hasFDerivAt_ringInverse (𝕜 := ℝ) (ContinuousLinearEquiv.toUnit e)
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at hr
  have hu : ((ContinuousLinearEquiv.toUnit e : (F →L[ℝ] F)ˣ) : F →L[ℝ] F) = L x := he
  have hu' : (((ContinuousLinearEquiv.toUnit e)⁻¹ : (F →L[ℝ] F)ˣ) : F →L[ℝ] F) =
      (L x).inverse := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    rfl
  rw [hu, hu'] at hr
  exact (hr.comp x hLd.hasFDerivAt).fderiv

/-- C¹,α is preserved by operator inversion, when the operator field is C¹ and invertible on an
open neighbourhood `O` of the compact set `U`. -/
theorem boundaryC2aCurvedHolder_c1Holder_inverse {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : ℝ} {L : E → F →L[ℝ] F} {U O : Set E} (hU : IsCompact U) (hO : IsOpen O)
    (hUO : U ⊆ O) (hLO : ContDiffOn ℝ 1 L O) (hL : HasC1HolderOn α L U)
    (hinv : ∀ x ∈ O, (L x).IsInvertible) :
    HasC1HolderOn α (fun x => (L x).inverse) U ∧
      ContDiffOn ℝ 1 (fun x => (L x).inverse) O := by
  have hIO : ContDiffOn ℝ 1 (fun x => (L x).inverse) O := by
    intro x hx
    exact ((hinv x hx).contDiffAt_map_inverse.comp x
      (hLO.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  obtain ⟨B, hB⟩ := hU.exists_bound_of_continuousOn (hIO.continuousOn.mono hUO)
  have hbd : ∀ x ∈ U, ‖(L x).inverse‖ ≤ max B 0 := fun x hx =>
    (hB x hx).trans (le_max_left _ _)
  have h0 := boundaryC2aCurvedHolder_holder_inverse (le_max_right B 0) hL.function_holder
    (fun x hx => hinv x (hUO hx)) hbd
  obtain ⟨h1, -⟩ := nondiv_holder_bilinear h0 h0
    (-ContinuousLinearMap.mulLeftRight ℝ (F →L[ℝ] F))
  obtain ⟨h2, -⟩ := nondiv_holder_bilinear h1 hL.derivative_holder
    (ContinuousLinearMap.compL ℝ E (F →L[ℝ] F) (F →L[ℝ] F))
  obtain ⟨h3, -⟩ := boundaryNeumann_holder_congr h2
    (g := fderiv ℝ (fun x => (L x).inverse)) (fun x hx => by
      have hLd : DifferentiableAt ℝ L x :=
        (hLO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hUO hx))
      rw [boundaryC2aCurvedHolder_fderiv_inverse hLd (hinv x (hUO hx)),
        ContinuousLinearMap.compL_apply, neg_apply,
        neg_apply])
  exact ⟨⟨hIO.mono hUO, h0, h3⟩, hIO⟩

/-- For a C¹ diffeomorphism of `ℝ³` the Jacobian determinant has a fixed sign, so its absolute
value is a constant multiple of it. -/
lemma boundaryC2aCurvedHolder_abs_det_eq
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ) :
    ∃ ε : ℝ, ∀ y, |(fderiv ℝ Θ y).det| = ε * (fderiv ℝ Θ y).det := by
  have hc : Continuous (fun y => (fderiv ℝ Θ y).det) :=
    (dirichletPullback_contDiff_det (r := 0)).continuous.comp (hΘ.continuous_fderiv one_ne_zero)
  have hne : ∀ y, (fderiv ℝ Θ y).det ≠ 0 := fun y =>
    dirichletPullback_det_ne_zero (dirichletPullback_isInvertible hΘ hΘi hl hr y)
  by_cases hpos : ∀ y, 0 < (fderiv ℝ Θ y).det
  · exact ⟨1, fun y => by rw [one_mul, abs_of_pos (hpos y)]⟩
  · push Not at hpos
    obtain ⟨a, ha⟩ := hpos
    have ha' : (fderiv ℝ Θ a).det < 0 := lt_of_le_of_ne ha (hne a)
    refine ⟨-1, fun y => ?_⟩
    have hy : (fderiv ℝ Θ y).det < 0 := by
      by_contra h
      push Not at h
      have hiv := intermediate_value_univ a y hc
      obtain ⟨c, hc0⟩ := hiv ⟨ha'.le, h⟩
      exact hne c hc0
    rw [abs_of_neg hy]
    ring

/-- The C¹,α pieces of the pullback: `|det DΘ|`, `DΘ⁻¹` and `DΘ⁻*` are C¹,α on a compact `K`
when `DΘ` is, for a C² diffeomorphism `Θ`; all three are C¹ on every open set. -/
theorem boundaryC2aCurvedHolder_pieces {α : ℝ}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 2 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hDΘ : HasC1HolderOn α (fderiv ℝ Θ) K) :
    (HasC1HolderOn α (fun y => |(fderiv ℝ Θ y).det|) K ∧
        ContDiff ℝ 1 (fun y => |(fderiv ℝ Θ y).det|)) ∧
      (HasC1HolderOn α (fun y => (fderiv ℝ Θ y).inverse) K ∧
        ContDiff ℝ 1 (fun y => (fderiv ℝ Θ y).inverse)) ∧
      (HasC1HolderOn α (fun y => (fderiv ℝ Θ y).inverse.adjoint) K ∧
        ContDiff ℝ 1 (fun y => (fderiv ℝ Θ y).inverse.adjoint)) := by
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ Θ) univ :=
    (hΘ.fderiv_right (m := 1) (by norm_num)).contDiffOn
  obtain ⟨ε, hε⟩ := boundaryC2aCurvedHolder_abs_det_eq hΘ1 hΘi hl hr
  have hg : ContDiff ℝ 2 (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
      ε * L.det) := contDiff_const.mul dirichletPullback_contDiff_det
  obtain ⟨hdet, hdet1⟩ := boundaryC2aCurvedHolder_c1Holder_comp hg isOpen_univ (subset_univ K)
    hD1 hDΘ
  have hfe : (fun y => |(fderiv ℝ Θ y).det|) = fun y => ε * (fderiv ℝ Θ y).det :=
    funext hε
  obtain ⟨hinv, hinv1⟩ := boundaryC2aCurvedHolder_c1Holder_inverse hK isOpen_univ
    (subset_univ K) hD1 hDΘ (fun y _ => dirichletPullback_isInvertible hΘ1 hΘi hl hr y)
  let T : (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    LinearMap.mkContinuous
      { toFun := fun L => ContinuousLinearMap.adjoint L
        map_add' := fun L M => map_add _ L M
        map_smul' := fun c L => by simp } 1 (fun L => by simp)
  obtain ⟨hadj, hadj1⟩ := boundaryC2aCurvedHolder_c1Holder_comp (g := T) T.contDiff isOpen_univ
    (subset_univ K) hinv1 hinv
  rw [hfe]
  exact ⟨⟨hdet, contDiffOn_univ.mp hdet1⟩, ⟨hinv, contDiffOn_univ.mp hinv1⟩,
    ⟨hadj, contDiffOn_univ.mp hadj1⟩⟩

/-- **The pulled-back coefficient is C¹,α.** For a C² diffeomorphism `Θ` of `ℝ³` with
`DΘ ∈ C^{1,α}(K)` on a compact `K`, and `A` C¹ on an open `W ⊇ Θ '' K` with `A ∘ Θ ∈ C^{1,α}(K)`,
the coefficient `|det DΘ| DΘ⁻¹ (A ∘ Θ) DΘ⁻*` is C¹,α on `K`. -/
theorem hasC1HolderOn_dirichletPullbackGeneralCoefficient {α : ℝ}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 2 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hDΘ : HasC1HolderOn α (fderiv ℝ Θ) K)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWΘ : Θ '' K ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 1 A W) (hAΘ : HasC1HolderOn α (A ∘ Θ) K) :
    HasC1HolderOn α (dirichletPullbackGeneralCoefficient A Θ) K := by
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  set O := Θ ⁻¹' W with hOdef
  have hO : IsOpen O := hW.preimage hΘ1.continuous
  have hKO : K ⊆ O := fun y hy => hWΘ (mem_image_of_mem Θ hy)
  obtain ⟨⟨hdet, hdet1⟩, ⟨hinv, hinv1⟩, ⟨hadj, hadj1⟩⟩ :=
    boundaryC2aCurvedHolder_pieces hΘ hΘi hl hr hK hDΘ
  have hAO : ContDiffOn ℝ 1 (A ∘ Θ) O := hA.comp hΘ1.contDiffOn (fun y hy => hy)
  obtain ⟨hY, -⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hKO hAO hadj1.contDiffOn hAΘ hadj
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)))
  simp only [ContinuousLinearMap.compL_apply, Function.comp_apply] at hY
  have hY1 : ContDiffOn ℝ 1 (fun y => (A (Θ y)).comp (fderiv ℝ Θ y).inverse.adjoint) O :=
    hAO.clm_comp hadj1.contDiffOn
  obtain ⟨hX, -⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hKO hinv1.contDiffOn hY1 hinv hY
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)))
  simp only [ContinuousLinearMap.compL_apply] at hX
  have hX1 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ Θ y).inverse.comp ((A (Θ y)).comp (fderiv ℝ Θ y).inverse.adjoint)) O :=
    hinv1.contDiffOn.clm_comp hY1
  exact (boundaryNeumann_hasC1HolderOn_smul hO hKO hdet1.contDiffOn hX1 hdet hX).1

/-- **The pulled-back datum is C¹,α.** Under the hypotheses of
`hasC1HolderOn_dirichletPullbackGeneralCoefficient` for `G` in place of `A`, the datum
`|det DΘ| DΘ⁻¹ (G ∘ Θ)` is C¹,α on `K`. -/
theorem hasC1HolderOn_dirichletPullbackGeneralDatum {α : ℝ}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 2 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hDΘ : HasC1HolderOn α (fderiv ℝ Θ) K)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWΘ : Θ '' K ⊆ W)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hG : ContDiffOn ℝ 1 G W) (hGΘ : HasC1HolderOn α (G ∘ Θ) K) :
    HasC1HolderOn α (dirichletPullbackGeneralDatum G Θ) K := by
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  set O := Θ ⁻¹' W with hOdef
  have hO : IsOpen O := hW.preimage hΘ1.continuous
  have hKO : K ⊆ O := fun y hy => hWΘ (mem_image_of_mem Θ hy)
  obtain ⟨⟨hdet, hdet1⟩, ⟨hinv, hinv1⟩, -⟩ :=
    boundaryC2aCurvedHolder_pieces hΘ hΘi hl hr hK hDΘ
  have hGO : ContDiffOn ℝ 1 (G ∘ Θ) O := hG.comp hΘ1.contDiffOn (fun y hy => hy)
  obtain ⟨hX, -⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hKO hinv1.contDiffOn hGO hinv hGΘ
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  simp only [ContinuousLinearMap.id_apply, Function.comp_apply] at hX
  have hX1 : ContDiffOn ℝ 1 (fun y => (fderiv ℝ Θ y).inverse (G (Θ y))) O :=
    hinv1.contDiffOn.clm_apply hGO
  exact (boundaryNeumann_hasC1HolderOn_smul hO hKO hdet1.contDiffOn hX1 hdet hX).1

/-- **`thm:boundary-C2a`, curved boundary after flattening, with the TeX regularity.** Let `Θ` be
a C² diffeomorphism of `ℝ³` with C¹ inverse `Θi`, both globally Lipschitz, with
`DΘ ∈ C^{1,α}(closure B⁺_1)` (a C^{2,α} boundary in shear coordinates). If `u ∈ H¹` solves
`div (A ∇u - G) = 0` on `Θ '' B⁺_1`, with `A`, `G` C¹ on an open `W ⊇ Θ '' closure B⁺_1`,
`A ∘ Θ`, `G ∘ Θ` C^{1,α} on `closure B⁺_1`, `A` elliptic on `Θ '' closure B⁺_1`, and the flattened
trace condition `u ∘ Θ = φ ∘ Θ` on the flat face for a C² function `φ` with
`∇(φ ∘ Θ) ∈ C^{1,α}(closure B⁺_1)`, then the conclusion of `boundary_c2a_curved_half_ball`
holds. -/
theorem boundary_c2a_curved_half_ball_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 2 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {CΘ KΘ : ℝ≥0} (hΘlip : LipschitzWith CΘ Θ) (hΘilip : LipschitzWith KΘ Θi)
    (hDΘ : HasC1HolderOn α (fderiv ℝ Θ) (closure (boundaryHalfBall 1)))
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : Θ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 1 A W) (hG : ContDiffOn ℝ 1 G W)
    (hAΘ : HasC1HolderOn α (A ∘ Θ) (closure (boundaryHalfBall 1)))
    (hGΘ : HasC1HolderOn α (G ∘ Θ) (closure (boundaryHalfBall 1)))
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ Θ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hφ : ContDiff ℝ 2 φ)
    (hgφΘ : HasC1HolderOn α (gradient (φ ∘ Θ)) (closure (boundaryHalfBall 1)))
    (hu : HasH1GradientOn u F (Θ '' boundaryHalfBall 1))
    (hw : IsWeakDivergenceEquationOn A F G (Θ '' boundaryHalfBall 1))
    (htr : HasZeroFlatTraceOn (fun y => u (Θ y) - φ (Θ y))
      (fun y => (fderiv ℝ Θ y).adjoint (F (Θ y)) - gradient (φ ∘ Θ) y) (ball 0 1)) :
    ∃ C > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      v =ᵐ[volume.restrict (Θ '' boundaryHalfBall (1 / 2))] u ∧
      ContDiffOn ℝ 2 (v ∘ Θ) (boundaryHalfBall (1 / 2)) ∧
      (∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry (v ∘ Θ) x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry (v ∘ Θ) x i j - boundaryNeumannC2Entry (v ∘ Θ) y i j| ≤
            C * dist x y ^ α) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), |(v ∘ Θ) x| ≤ C) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), ‖gradient (v ∘ Θ) x‖ ≤ C) ∧
      (∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
        ‖gradient (v ∘ Θ) x - gradient (v ∘ Θ) y‖ ≤ C * dist x y ^ α) := by
  set K := closure (boundaryHalfBall 1) with hK_def
  have hKc : IsCompact K := boundaryC2aCurved_isCompact_closure_halfBall
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  let e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := Θ
      invFun := Θi
      left_inv := hl
      right_inv := hr
      continuous_toFun := hΘ1.continuous
      continuous_invFun := hΘi.continuous }
  have hVo : IsOpen (Θ '' boundaryHalfBall 1) := e.isOpenMap _ (isOpen_boundaryHalfBall 1)
  -- the flattened problem
  set At := dirichletPullbackGeneralCoefficient A Θ with hAt
  set Gt := dirichletPullbackGeneralDatum G Θ with hGt
  set Ft : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun y => (fderiv ℝ Θ y).adjoint (F (Θ y)) with hFt
  set phit := φ ∘ Θ with hphit
  obtain ⟨hũ, hwt⟩ := isWeakDivergenceEquationOn_dirichletPullbackGeneral hΘ1 hΘi hl hr
    hΘlip hΘilip (isOpen_boundaryHalfBall 1) hVo (mapsTo_image Θ _) hu hw
  -- C¹,α regularity of the coefficient and datum on `K`
  have hAth : HasC1HolderOn α At K :=
    hasC1HolderOn_dirichletPullbackGeneralCoefficient hΘ hΘi hl hr hKc hDΘ hW hWΘ hA hAΘ
  have hGth : HasC1HolderOn α Gt K :=
    hasC1HolderOn_dirichletPullbackGeneralDatum hΘ hΘi hl hr hKc hDΘ hW hWΘ hG hGΘ
  -- the flattened boundary datum
  have hphit2 : ContDiff ℝ 2 phit := hφ.comp hΘ
  have hgphit1 : ContDiff ℝ 1 (gradient phit) :=
    contDiff_gradient_of_contDiff_succ (r := 1) (hphit2.of_le (by norm_num))
  have hphith : HasC1HolderOn α phit K :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα hα1.le hphit2
  have hgphith : HasC1HolderOn α (gradient phit) K := hgφΘ
  obtain ⟨P₁, hP₁⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    |>.exists_bound_of_continuousOn hgphit1.continuous.continuousOn
  have hP₁0 : 0 ≤ P₁ := (norm_nonneg _).trans (hP₁ 0 (mem_closedBall_self zero_le_one))
  have hgphitfin : HasFiniteHolderNormOn α (gradient phit) (closedBall 0 1) :=
    dirichletPullback_hasFiniteHolderNormOn_of_contDiff hα hα1.le hgphit1 subset_rfl
  set P₂ := holderNorm α (gradient phit) (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) with hP₂
  have hP₂0 : 0 ≤ P₂ := hgphitfin.norm_nonneg
  have hP₂b := boundary_c2a_local_holder_pointwise hgphitfin le_rfl
  -- bounds and ellipticity of the coefficient on `K`
  have hAc : ContinuousOn A (Θ '' K) := (hA.continuousOn).mono hWΘ
  obtain ⟨capA, hcapA⟩ := (hKc.image hΘ1.continuous).exists_bound_of_continuousOn hAc
  obtain ⟨lam, cap, hlam, hlamcap, hAtb⟩ :=
    dirichletPullbackGeneralCoefficient_bounds hΘ1 hΘi hl hr hKc hlamA hcapA hAe
  -- the constants of the flat estimate
  set M := nondivC1HolderNorm α At K with hM
  set N := nondivC1HolderNorm α phit K + nondivC1HolderNorm α (gradient phit) K +
    nondivC1HolderNorm α Gt K with hN
  set E := ∫ x in boundaryHalfBall 1, ‖Ft x - gradient phit x‖ ^ 2 with hE
  have hM0 : 0 ≤ M := hAth.norm_nonneg
  have hN0 : 0 ≤ N := by
    have := hphith.norm_nonneg
    have := hgphith.norm_nonneg
    have := hGth.norm_nonneg
    linarith
  have hE0 : 0 ≤ E := integral_nonneg fun _ => by positivity
  obtain ⟨C, hC, hflat⟩ :=
    boundary_c2a_half_ball_full_of_h1 hα hα1 hlam hlamcap hM0 hN0 hP₁0 hP₂0 hE0
  obtain ⟨w, hwC, hwu, hent, hwb, hgwb, hgwh⟩ :=
    hflat (u ∘ Θ) phit Ft Gt At hphit2 hAth hGth hphith hgphith le_rfl le_rfl
      (fun x hx => (hAtb x hx).1) (fun x hx => (hAtb x hx).2) hP₁ hP₂b hũ hwt htr le_rfl
  -- transport the representative back
  refine ⟨C, hC, w ∘ Θi, ?_, ?_⟩
  swap
  · have hvw : (w ∘ Θi) ∘ Θ = w := funext fun y => by simp [hl y]
    rw [hvw]
    exact ⟨hwC, hent, hwb, hgwb, hgwh⟩
  have hBm : MeasurableSet (boundaryHalfBall (1 / 2 : ℝ)) :=
    (isOpen_boundaryHalfBall _).measurableSet
  have hΘBm : MeasurableSet (Θ '' boundaryHalfBall (1 / 2 : ℝ)) :=
    (e.isOpenMap _ (isOpen_boundaryHalfBall _)).measurableSet
  have hnull := ae_iff.mp ((ae_restrict_iff' hBm).mp hwu)
  rw [EventuallyEq, ae_restrict_iff' hΘBm, ae_iff]
  refine measure_mono_null ?_
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hΘ1.differentiable one_ne_zero).differentiableOn hnull)
  intro x hx
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨⟨y, hy, rfl⟩, hne⟩ := hx
  refine ⟨y, ?_, rfl⟩
  simp only [mem_ofPred_eq, not_imp]
  refine ⟨hy, ?_⟩
  simpa [hl y] using hne

end LiquidDrop
