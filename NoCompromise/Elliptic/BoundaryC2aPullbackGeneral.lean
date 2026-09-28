import NoCompromise.Elliptic.BoundaryC2aPullback
import NoCompromise.Elliptic.BoundaryNeumannC2InhomFinite
import NoCompromise.Sobolev.H1Chain

/-!
# Pullback of a general divergence-form equation under a C¹ diffeomorphism

For a global C¹ diffeomorphism `Θ` of `ℝ³` (with C¹ inverse `Θi`), the weak equation
`div (A F - G) = 0` on `V` pulls back to the weak equation for the transported field
`DΘᵀ (F ∘ Θ)` on any `U` with `Θ '' U ⊆ V`, with coefficient `|det DΘ| DΘ⁻¹ (A ∘ Θ) DΘ⁻ᵀ` and
datum `|det DΘ| DΘ⁻¹ (G ∘ Θ)`. The change of variables is pointwise linear algebra and uses
no regularity of the field `F`. When `F` is the weak gradient of an H¹ function `u` and `Θ`,
`Θi` are Lipschitz, the transported field is the weak gradient of `u ∘ Θ`. The coefficient and
datum are C² where `A`, `G` are C² when `Θ` is C³, and the coefficient is bounded and elliptic
on compact sets whose image carries a bound and an ellipticity constant for `A`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The pullback coefficient `|det DΘ| · DΘ⁻¹ (A ∘ Θ) DΘ⁻*`. -/
def dirichletPullbackGeneralCoefficient
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  |(fderiv ℝ Θ y).det| •
    ((fderiv ℝ Θ y).inverse.comp ((A (Θ y)).comp (fderiv ℝ Θ y).inverse.adjoint))

/-- The pullback datum `|det DΘ| · DΘ⁻¹ (G ∘ Θ)`. -/
def dirichletPullbackGeneralDatum (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  |(fderiv ℝ Θ y).det| • (fderiv ℝ Θ y).inverse (G (Θ y))

/-- The pointwise flux pairing transforms by the pullback coefficient and datum. -/
lemma dirichletPullbackGeneral_pairing
    {Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hΘ : DifferentiableAt ℝ Θ y) (hψ : DifferentiableAt ℝ ψ (Θ y))
    (hy : (fderiv ℝ Θ y).IsInvertible) :
    inner ℝ (dirichletPullbackGeneralCoefficient A Θ y ((fderiv ℝ Θ y).adjoint (F (Θ y))) -
        dirichletPullbackGeneralDatum G Θ y) (gradient (ψ ∘ Θ) y) =
      |(fderiv ℝ Θ y).det| * inner ℝ (A (Θ y) (F (Θ y)) - G (Θ y)) (gradient ψ (Θ y)) := by
  set L := fderiv ℝ Θ y with hLdef
  have hstar : L.inverse.adjoint.comp L.adjoint = ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hy.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have hs (v : EuclideanSpace ℝ (Fin 3)) : L.inverse.adjoint (L.adjoint v) = v :=
    congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hstar
  rw [dirichletPullback_gradient_comp hΘ hψ]
  have hsplit : dirichletPullbackGeneralCoefficient A Θ y (L.adjoint (F (Θ y))) -
      dirichletPullbackGeneralDatum G Θ y =
        |L.det| • L.inverse (A (Θ y) (F (Θ y)) - G (Θ y)) := by
    change |L.det| • L.inverse (A (Θ y) (L.inverse.adjoint (L.adjoint (F (Θ y))))) -
      |L.det| • L.inverse (G (Θ y)) = _
    rw [hs, map_sub, smul_sub]
  rw [hsplit, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right,
    hy.self_apply_inverse]

/-- **Pullback of the weak equation.** The weak equation `div (A F - G) = 0` on `V` pulls back
under a C¹ diffeomorphism `Θ` to the weak equation for `DΘᵀ (F ∘ Θ)` on `U`, with the general
pullback coefficient and datum. No regularity or integrability of `F` is used. -/
theorem isWeakDivergenceEquationOn_dirichletPullbackGeneral_field
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {V U : Set (EuclideanSpace ℝ (Fin 3))} (hUV : MapsTo Θ U V)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : IsWeakDivergenceEquationOn A F G V) :
    IsWeakDivergenceEquationOn (dirichletPullbackGeneralCoefficient A Θ)
      (fun y => (fderiv ℝ Θ y).adjoint (F (Θ y))) (dirichletPullbackGeneralDatum G Θ) U := by
  intro φ hφ hφc hφU
  let e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := Θ
      invFun := Θi
      left_inv := hl
      right_inv := hr
      continuous_toFun := hΘ.continuous
      continuous_invFun := hΘi.continuous }
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ψ = φ ∘ Θi := ⟨_, rfl⟩
  have hψ : ContDiff ℝ 1 ψ := hψdef ▸ hφ.comp hΘi
  have hψc : HasCompactSupport ψ := hψdef ▸ hφc.comp_homeomorph e.symm
  have hψs : tsupport ψ = Θ '' tsupport φ := by
    have h := tsupport_comp_eq_preimage φ e.symm
    rw [hψdef]
    change tsupport (φ ∘ e.symm) = _
    rw [h, e.preimage_symm]
    rfl
  have hψV : tsupport ψ ⊆ V := hψs ▸ (image_mono hφU).trans hUV.image_subset
  have h0 := hw ψ hψ hψc hψV
  have hφψ : φ = ψ ∘ Θ := funext fun y => by simp [hψdef, hl y]
  have hderiv : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))),
      HasFDerivWithinAt Θ (fderiv ℝ Θ y) univ y :=
    fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hderiv
    hl.injective.injOn (fun x => inner ℝ (A x (F x) - G x) (gradient ψ x))
  rw [image_univ, hr.surjective.range_eq, Measure.restrict_univ] at hcv
  rw [hcv] at h0
  rw [← h0]
  congr 1
  funext y
  rw [smul_eq_mul, hφψ]
  exact dirichletPullbackGeneral_pairing (hΘ.differentiable one_ne_zero y)
    (hψ.differentiable one_ne_zero _) (dirichletPullback_isInvertible hΘ hΘi hl hr y)

/-- **Pullback of an H¹ weak solution.** If `u ∈ H¹(V)` has weak gradient `F` and solves the
weak equation `div (A F - G) = 0` on `V`, and `Θ`, `Θi` are Lipschitz C¹ mutually inverse maps
with `Θ '' U ⊆ V` (`U`, `V` open), then `u ∘ Θ ∈ H¹(U)` has weak gradient `DΘᵀ (F ∘ Θ)` and
solves the pulled-back weak equation on `U`. -/
theorem isWeakDivergenceEquationOn_dirichletPullbackGeneral
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {C K : ℝ≥0} (hΘlip : LipschitzWith C Θ) (hΘilip : LipschitzWith K Θi)
    {V U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : MapsTo Θ U V)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u F V) (hw : IsWeakDivergenceEquationOn A F G V) :
    HasH1GradientOn (u ∘ Θ) (fun y => (fderiv ℝ Θ y).adjoint (F (Θ y))) U ∧
      IsWeakDivergenceEquationOn (dirichletPullbackGeneralCoefficient A Θ)
        (fun y => (fderiv ℝ Θ y).adjoint (F (Θ y))) (dirichletPullbackGeneralDatum G Θ) U := by
  let e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := Θ
      invFun := Θi
      left_inv := hl
      right_inv := hr
      continuous_toFun := hΘ.continuous
      continuous_invFun := hΘi.continuous }
  exact ⟨(hu.comp_homeomorph_on hU hV e hΘlip hΘilip hUV).1,
    isWeakDivergenceEquationOn_dirichletPullbackGeneral_field hΘ hΘi hl hr hUV hw⟩

/-- Local smoothness of `y ↦ DΘ(y)⁻¹`, `y ↦ DΘ(y)⁻*` and `y ↦ |det DΘ(y)|`. -/
lemma dirichletPullbackGeneral_contDiffAt_pieces {m : ℕ∞} {n : WithTop ℕ∞}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ n Θ) (hmn : (m : WithTop ℕ∞) + 1 ≤ n) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse) y ∧
      ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse.adjoint) y ∧
      ContDiffAt ℝ m (fun z => |(fderiv ℝ Θ z).det|) y := by
  have hD : ContDiff ℝ m (fderiv ℝ Θ) := hΘ.fderiv_right hmn
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (le_add_self.trans hmn)
  have hy := dirichletPullback_isInvertible hΘ1 hΘi hl hr y
  obtain ⟨e, he⟩ := hy
  have hinv : ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse) y :=
    ContDiffAt.comp (g := ContinuousLinearMap.inverse) y
      (he ▸ contDiffAt_map_inverse e) hD.contDiffAt
  have hadj : ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse.adjoint) y :=
    dirichletPullback_contDiff_adjoint.contDiffAt.comp y hinv
  have hdet : ContDiffAt ℝ m (fun z => |(fderiv ℝ Θ z).det|) y :=
    (dirichletPullback_contDiff_det.contDiffAt.comp y hD.contDiffAt).abs
      (dirichletPullback_det_ne_zero ⟨e, he⟩)
  exact ⟨hinv, hadj, hdet⟩

/-- The general pullback coefficient is `C^m` where `A ∘ Θ` is, when `Θ` is `C^{m+1}`. -/
theorem contDiffOn_dirichletPullbackGeneralCoefficient {m : ℕ∞} {n : WithTop ℕ∞}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ n Θ) (hmn : (m : WithTop ℕ∞) + 1 ≤ n) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hA : ContDiffOn ℝ m A W) :
    ContDiffOn ℝ m (dirichletPullbackGeneralCoefficient A Θ) (Θ ⁻¹' W) := by
  intro y hy
  obtain ⟨hinv, hadj, hdet⟩ := dirichletPullbackGeneral_contDiffAt_pieces hΘ hmn hΘi hl hr y
  have hΘm : ContDiff ℝ m Θ := hΘ.of_le (le_self_add.trans hmn)
  have hAΘ : ContDiffAt ℝ m (fun z => A (Θ z)) y :=
    (hA.contDiffAt (hW.mem_nhds hy)).comp y hΘm.contDiffAt
  exact (hdet.smul (hinv.clm_comp (hAΘ.clm_comp hadj))).contDiffWithinAt

/-- The general pullback datum is `C^m` where `G ∘ Θ` is, when `Θ` is `C^{m+1}`. -/
theorem contDiffOn_dirichletPullbackGeneralDatum {m : ℕ∞} {n : WithTop ℕ∞}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ n Θ) (hmn : (m : WithTop ℕ∞) + 1 ≤ n) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hG : ContDiffOn ℝ m G W) :
    ContDiffOn ℝ m (dirichletPullbackGeneralDatum G Θ) (Θ ⁻¹' W) := by
  intro y hy
  obtain ⟨hinv, -, hdet⟩ := dirichletPullbackGeneral_contDiffAt_pieces hΘ hmn hΘi hl hr y
  have hΘm : ContDiff ℝ m Θ := hΘ.of_le (le_self_add.trans hmn)
  have hGΘ : ContDiffAt ℝ m (fun z => G (Θ z)) y :=
    (hG.contDiffAt (hW.mem_nhds hy)).comp y hΘm.contDiffAt
  exact (hdet.smul (hinv.clm_apply hGΘ)).contDiffWithinAt

/-- **Regularity.** For a C³ diffeomorphism `Θ` and `A`, `G` C² on an open `W`, the pullback
coefficient and datum are C² on `Θ⁻¹ W`. -/
theorem contDiffOn_two_dirichletPullbackGeneral
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 3 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hA : ContDiffOn ℝ 2 A W)
    (hG : ContDiffOn ℝ 2 G W) :
    ContDiffOn ℝ 2 (dirichletPullbackGeneralCoefficient A Θ) (Θ ⁻¹' W) ∧
      ContDiffOn ℝ 2 (dirichletPullbackGeneralDatum G Θ) (Θ ⁻¹' W) :=
  ⟨contDiffOn_dirichletPullbackGeneralCoefficient (m := 2) hΘ (by norm_num) hΘi hl hr hW hA,
    contDiffOn_dirichletPullbackGeneralDatum (m := 2) hΘ (by norm_num) hΘi hl hr hW hG⟩

/-- **Bounds.** On a compact `S`, if `A` is bounded by `capA` and `lamA`-elliptic on `Θ '' S`,
the general pullback coefficient is uniformly bounded and elliptic on `S`. -/
theorem dirichletPullbackGeneralCoefficient_bounds
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {lamA capA : ℝ} (hlamA : 0 < lamA)
    (hAb : ∀ x ∈ Θ '' S, ‖A x‖ ≤ capA)
    (hAe : ∀ x ∈ Θ '' S, ∀ ξ, lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) :
    ∃ lam cap : ℝ, 0 < lam ∧ lam ≤ cap ∧
      ∀ y ∈ S, ‖dirichletPullbackGeneralCoefficient A Θ y‖ ≤ cap ∧
        ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (dirichletPullbackGeneralCoefficient A Θ y ξ) ξ := by
  have hcont : Continuous (fun y => |(fderiv ℝ Θ y).det| * ‖(fderiv ℝ Θ y).inverse‖ ^ 2) := by
    rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨hinv, -, hdet⟩ :=
      dirichletPullbackGeneral_contDiffAt_pieces (m := 0) hΘ (by simp) hΘi hl hr y
    exact hdet.continuousAt.mul (hinv.continuousAt.norm.pow 2)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨M, δ, hM, hδ, hMδ⟩ := dirichletPullback_fderiv_det_bounds hΘ hΘi hl hr hS
  refine ⟨δ * lamA / M ^ 2, max (B * max capA 0) (δ * lamA / M ^ 2), by positivity,
    le_max_right _ _, fun y hy => ⟨?_, fun ξ => ?_⟩⟩
  · obtain ⟨hLM, hδL⟩ := hMδ y hy
    set L := fderiv ℝ Θ y with hLdef
    have hAy : ‖A (Θ y)‖ ≤ max capA 0 := (hAb _ (mem_image_of_mem Θ hy)).trans (le_max_left _ _)
    have hBy : |L.det| * ‖L.inverse‖ ^ 2 ≤ B := by
      have := hB y hy
      rwa [Real.norm_of_nonneg (by positivity)] at this
    refine le_trans ?_ (le_max_left _ _)
    change ‖|L.det| • (L.inverse.comp ((A (Θ y)).comp L.inverse.adjoint))‖ ≤ _
    calc ‖|L.det| • (L.inverse.comp ((A (Θ y)).comp L.inverse.adjoint))‖
        ≤ |L.det| * (‖L.inverse‖ * (‖A (Θ y)‖ * ‖L.inverse.adjoint‖)) := by
          rw [norm_smul, Real.norm_of_nonneg (abs_nonneg _)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
      _ = (|L.det| * ‖L.inverse‖ ^ 2) * ‖A (Θ y)‖ := by
          rw [LinearIsometryEquiv.norm_map]; ring
      _ ≤ B * max capA 0 :=
          mul_le_mul hBy hAy (norm_nonneg _) ((norm_nonneg _).trans (hB y hy))
  · obtain ⟨hLM, hδL⟩ := hMδ y hy
    set L := fderiv ℝ Θ y with hLdef
    have hL : L.IsInvertible := dirichletPullback_isInvertible hΘ hΘi hl hr y
    set w := L.inverse.adjoint ξ with hw
    have hinner : inner ℝ (dirichletPullbackGeneralCoefficient A Θ y ξ) ξ =
        |L.det| * inner ℝ (A (Θ y) w) w := by
      change inner ℝ (|L.det| • L.inverse (A (Θ y) (L.inverse.adjoint ξ))) ξ = _
      rw [real_inner_smul_left, ← ContinuousLinearMap.adjoint_inner_right]
    have hξ : ξ = L.adjoint w := by
      have hstar : L.adjoint.comp L.inverse.adjoint = ContinuousLinearMap.id ℝ _ := by
        rw [← ContinuousLinearMap.adjoint_comp, hL.inverse_comp_self,
          ContinuousLinearMap.adjoint_id]
      exact (congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A ξ)
        hstar).symm
    have hξw : ‖ξ‖ ≤ M * ‖w‖ := by
      calc ‖ξ‖ = ‖L.adjoint w‖ := congrArg norm hξ
        _ ≤ ‖L.adjoint‖ * ‖w‖ := L.adjoint.le_opNorm w
        _ = ‖L‖ * ‖w‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ M * ‖w‖ := mul_le_mul_of_nonneg_right hLM (norm_nonneg _)
    have hsq : ‖ξ‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hξw 2
    have hAw := hAe _ (mem_image_of_mem Θ hy) w
    rw [hinner]
    calc δ * lamA / M ^ 2 * ‖ξ‖ ^ 2 ≤ δ * lamA / M ^ 2 * (M ^ 2 * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = δ * (lamA * ‖w‖ ^ 2) := by field_simp
      _ ≤ |L.det| * inner ℝ (A (Θ y) w) w :=
          mul_le_mul hδL hAw (by positivity) (abs_nonneg _)

end LiquidDrop
