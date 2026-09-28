import NoCompromise.Elliptic.BoundaryC2aPullbackGeneral
import NoCompromise.Elliptic.BoundaryC2aCoverNorm
import NoCompromise.Elliptic.InteriorH2Energy
import NoCompromise.Elliptic.BoundaryC2aShear

/-!
# `thm:boundary-C2a` after flattening a curved boundary

Let `Θ` be a C³ diffeomorphism of `ℝ³` with C¹ inverse `Θi`, both globally Lipschitz (e.g. the
shear flattening `boundaryShearMap` of a graph chart whose height is C³ and globally Lipschitz,
`boundary_c2a_shear_half_ball`). If `u ∈ H¹` solves the
weak equation `div (A ∇u - G) = 0` on the curved half ball `Θ '' B⁺_1`, with `A`, `G` C² on an
open set containing `Θ '' closure B⁺_1`, `A` elliptic there, and the flattened trace condition
`u ∘ Θ = φ ∘ Θ` on the flat face for a C³ function `φ`, then `u` has a representative `v` such that
`v ∘ Θ` is C² on `B⁺_{1/2}` with bounded and α-Hölder second derivatives, bounded values and
bounded, α-Hölder gradient there. The proof pulls the equation back with
`isWeakDivergenceEquationOn_dirichletPullbackGeneral` and applies the flat estimate
`boundary_c2a_half_ball_full_of_h1`; the constant depends on the data, the chart being fixed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundaryC2aCurved_isCompact_closure_halfBall :
    IsCompact (closure (boundaryHalfBall 1)) :=
  (isBounded_ball.subset (inter_subset_left : boundaryHalfBall 1 ⊆ ball 0 1)).isCompact_closure

/-- **`thm:boundary-C2a`, curved boundary after flattening.** -/
theorem boundary_c2a_curved_half_ball {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 3 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {CΘ KΘ : ℝ≥0} (hΘlip : LipschitzWith CΘ Θ) (hΘilip : LipschitzWith KΘ Θi)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : Θ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 2 A W) (hG : ContDiffOn ℝ 2 G W)
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ Θ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hφ : ContDiff ℝ 3 φ)
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
  have hKcv : Convex ℝ K := (convex_boundaryHalfBall 1).closure
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
  -- regularity of the coefficient and datum on a neighbourhood of `K`
  have hO : IsOpen (Θ ⁻¹' W) := hW.preimage hΘ1.continuous
  have hKO : K ⊆ Θ ⁻¹' W := fun y hy => hWΘ (mem_image_of_mem Θ hy)
  obtain ⟨hAt2, hGt2⟩ := contDiffOn_two_dirichletPullbackGeneral hΘ hΘi hl hr hW hA hG
  have hAth : HasC1HolderOn α At K :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKcv hO hKO hAt2
  have hGth : HasC1HolderOn α Gt K :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKcv hO hKO hGt2
  -- the flattened boundary datum
  have hphit3 : ContDiff ℝ 3 phit := hφ.comp hΘ
  have hphit2 : ContDiff ℝ 2 phit := hphit3.of_le (by norm_num)
  have hgphit2 : ContDiff ℝ 2 (gradient phit) :=
    contDiff_gradient_of_contDiff_succ (r := 2) (hphit3.of_le (by norm_num))
  have hgphit1 : ContDiff ℝ 1 (gradient phit) := hgphit2.of_le (by norm_num)
  have hphith : HasC1HolderOn α phit K :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα hα1.le hphit2
  have hgphith : HasC1HolderOn α (gradient phit) K :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα hα1.le hgphit2
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

/-- A graph append of Lipschitz data is Lipschitz. -/
lemma boundaryShear_lipschitz_graphAppendN {X : Type*} [PseudoEMetricSpace X]
    {x : X → EuclideanSpace ℝ (Fin 2)} {t : X → ℝ} {Kx Kt : ℝ≥0}
    (hx : LipschitzWith Kx x) (ht : LipschitzWith Kt t) :
    ∃ K, LipschitzWith K (fun w => graphAppendN (x w) (t w)) := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (Fin.last 2) 1)
  have h := ((graphBaseN 2).lipschitzWith.comp hx).add (L.lipschitzWith.comp ht)
  have heq : (fun w => graphAppendN (x w) (t w)) =
      fun w => (graphBaseN 2 ∘ x) w + (L ∘ t) w := by
    funext w
    simp [graphAppendN, L]
  refine ⟨‖graphBaseN 2‖₊ * Kx + ‖L‖₊ * Kt, ?_⟩
  rw [heq]
  exact h

/-- The shear flattening of a chart with a Lipschitz height is Lipschitz. -/
lemma boundaryShearMap_lipschitz (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {Lh : ℝ≥0} (hh : LipschitzWith Lh c.height) :
    ∃ C, LipschitzWith C (boundaryShearMap c a ρ) := by
  have hs : LipschitzWith ‖ρ‖₊ (fun y : EuclideanSpace ℝ (Fin 3) => ρ • y) := lipschitzWith_smul ρ
  have hx : LipschitzWith (0 + ‖graphProjectionN 2‖₊ * ‖ρ‖₊)
      (fun y : EuclideanSpace ℝ (Fin 3) => a + graphProjectionN 2 (ρ • y)) :=
    (LipschitzWith.const a).add ((graphProjectionN 2).lipschitzWith.comp hs)
  have hl : LipschitzWith (‖(EuclideanSpace.proj (Fin.last 2) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖₊ * ‖ρ‖₊)
      (fun y : EuclideanSpace ℝ (Fin 3) => (ρ • y) (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).lipschitzWith.comp hs
  obtain ⟨K, hK⟩ := boundaryShear_lipschitz_graphAppendN hx ((hh.comp hx).sub hl)
  exact ⟨_, c.placement.isometry.lipschitzWith.comp hK⟩

/-- The inverse of the shear flattening of a chart with a Lipschitz height is Lipschitz. -/
lemma boundaryShearInv_lipschitz (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {Lh : ℝ≥0} (hh : LipschitzWith Lh c.height) :
    ∃ K, LipschitzWith K (boundaryShearInv c a ρ) := by
  have hP : LipschitzWith 1 (fun z : EuclideanSpace ℝ (Fin 3) => c.placement.symm z) :=
    c.placement.symm.isometry.lipschitzWith
  have hπ := (graphProjectionN 2).lipschitzWith.comp hP
  have hx := hπ.sub (LipschitzWith.const a)
  have hl : LipschitzWith (‖(EuclideanSpace.proj (Fin.last 2) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖₊ * 1)
      (fun z : EuclideanSpace ℝ (Fin 3) => c.placement.symm z (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).lipschitzWith.comp hP
  obtain ⟨K, hK⟩ := boundaryShear_lipschitz_graphAppendN hx ((hh.comp hπ).sub hl)
  exact ⟨_, (lipschitzWith_smul ρ⁻¹).comp hK⟩

/-- **`thm:boundary-C2a` in a shear-flattened graph chart.** For a graph chart with a C³,
globally Lipschitz height and `ρ ≠ 0`, the conclusion of `boundary_c2a_curved_half_ball` holds
for the shear flattening `Θ = boundaryShearMap c a ρ`. -/
theorem boundary_c2a_shear_half_ball {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hh3 : ContDiff ℝ 3 c.height) {Lh : ℝ≥0} (hhlip : LipschitzWith Lh c.height)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : boundaryShearMap c a ρ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 2 A W) (hG : ContDiffOn ℝ 2 G W)
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ boundaryShearMap c a ρ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hφ : ContDiff ℝ 3 φ)
    (hu : HasH1GradientOn u F (boundaryShearMap c a ρ '' boundaryHalfBall 1))
    (hw : IsWeakDivergenceEquationOn A F G (boundaryShearMap c a ρ '' boundaryHalfBall 1))
    (htr : HasZeroFlatTraceOn (fun y => u (boundaryShearMap c a ρ y) - φ (boundaryShearMap c a ρ y))
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
  have hΘ : ContDiff ℝ 3 (boundaryShearMap c a ρ) := by
    have h := contDiff_boundaryShearMap c a ρ (n := 3) (by simpa using hh3)
    simpa using h
  have hΘi : ContDiff ℝ 1 (boundaryShearInv c a ρ) := by
    have h := contDiff_boundaryShearInv c a ρ (n := 1) (by simpa using hh3.of_le (by norm_num))
    simpa using h
  exact boundary_c2a_curved_half_ball hα hα1 hΘ hΘi (boundaryShearMap_leftInverse c a hρ)
    (boundaryShearMap_rightInverse c a hρ) hCΘ hKΘ hW hWΘ hA hG hlamA hAe hφ hu hw htr

end LiquidDrop
