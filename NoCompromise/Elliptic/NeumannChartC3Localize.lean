import NoCompromise.Elliptic.NeumannChartC3Regularity

/-!
# Localization of weak Neumann solutions with C² chart heights
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- C² height suffices for the C¹ coordinate map used in localization. -/
lemma contDiff_neumannLocalizeMap_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    ContDiff ℝ 1 (neumannLocalizeMap c a ρ) :=
  contDiff_neumannLocalizeMap_of_contDiff c hψ a ρ

lemma fderiv_neumannLocalizeMap_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (y : AmbientSpace) :
    fderiv ℝ (neumannLocalizeMap c a ρ) y =
      c.placement.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).comp
          (ρ • ContinuousLinearMap.id ℝ AmbientSpace)) := by
  have hs : HasFDerivAt (fun y : AmbientSpace => graphAppendN a 0 + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ AmbientSpace) y :=
    ((hasFDerivAt_id y).const_smul ρ).const_add _
  exact ((hasFDerivAt_rigidPlacement c.placement _).comp y
    (((contDiff_boundaryNormalChart (r := 1) hψ).differentiable one_ne_zero _).hasFDerivAt.comp
      y hs)).fderiv

lemma neumannLocalizeMap_regular_c2 (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 2 c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).IsInvertible) :
    (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible := by
  rw [fderiv_neumannLocalizeMap_c2 c hψ]
  apply ContinuousLinearMap.isInvertible_equiv.comp
  apply hy.comp
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ρ⁻¹ • ContinuousLinearMap.id ℝ AmbientSpace)
  · ext v
    simp [hρ.ne']
  · ext v
    simp [hρ.ne']

/-- C² height gives a regular C¹ normal chart and a global bilipschitz extension. -/
theorem C1BoundaryChart.IsChartFor.exists_neumannLocalizeMap_c2
    {D : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ 2 c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0,
      let Θ := neumannLocalizeMap c (graphProjectionN 2 (c.placement.symm p)) ρ
      Θ 0 = p ∧ ContDiff ℝ 1 Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧
      Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      ∃ (E : AmbientSpace ≃ₜ AmbientSpace) (C K : ℝ≥0),
        LipschitzWith C E ∧ LipschitzWith K E.symm ∧ EqOn Θ E (ball 0 2) := by
  let a := graphProjectionN 2 (c.placement.symm p)
  let b := graphAppendN a 0
  have hpa : c.placement (graphMapN c.height a) = p := by
    have hpg : p ∈ c.graphSurface :=
      (hc.frontier_inter_eq ▸ (show p ∈ frontier D ∩ c.region from ⟨hp, hpc⟩)).1
    obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hpg
    change c.placement (graphMapN c.height
      (graphProjectionN 2 (c.placement.symm (c.placement (graphMapN c.height x))))) = _
    rw [c.placement.symm_apply_apply]
    change c.placement (graphMapN c.height
      (graphProjectionN 2 (graphAppendN x (c.height x)))) = _
    rw [graphProjectionN_append]
  obtain ⟨e, he, hb, _, _, hreg⟩ :=
    boundaryNormalChart_local_diffeomorphism_on_of_contDiff (r := 1) le_rfl hψ a
  obtain ⟨E, C, K, U, hE, hEi, hU, hbU, hEq⟩ :=
    neumannLocalize_exists_bilipschitz_extension
      ((contDiff_boundaryNormalChart (r := 1) hψ).contDiffAt) (hreg b hb)
  obtain ⟨δ, hδ, ε, hε, hsides⟩ := boundaryNormalChart_sides c.height_contDiff a
  let V := (e.source ∩ U) ∩
    (fun x => c.placement (boundaryNormalChart c.height x)) ⁻¹' c.region ∩
    (graphProjectionN 2) ⁻¹' ball a δ ∩
    (fun x : AmbientSpace => x (Fin.last 2)) ⁻¹' Ioo (-ε) ε
  have hV : IsOpen V :=
    (((e.open_source.inter hU).inter (c.isOpen_region.preimage
      (c.placement.continuous.comp (contDiff_boundaryNormalChart (r := 1) hψ).continuous))).inter
      (isOpen_ball.preimage (graphProjectionN 2).continuous)).inter
        (isOpen_Ioo.preimage (EuclideanSpace.proj (Fin.last 2)).continuous)
  have hbV : b ∈ V := by
    refine ⟨⟨⟨⟨hb, hbU⟩, ?_⟩, ?_⟩, ?_⟩
    · change c.placement (boundaryNormalChart c.height (graphAppendN a 0)) ∈ c.region
      rwa [boundaryNormalChart_face, hpa]
    · change graphProjectionN 2 (graphAppendN a 0) ∈ ball a δ
      simpa only [graphProjectionN_append] using mem_ball_self hδ
    · change graphAppendN a 0 (Fin.last 2) ∈ Ioo (-ε) ε
      simpa only [graphAppendN_last] using
        (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbV)
  let ρ := r / 3
  have hρ : 0 < ρ := div_pos hr (by norm_num)
  let S : AmbientSpace → AmbientSpace := fun y => b + ρ • y
  have hSV : MapsTo S (ball 0 2) V := by
    intro y hy
    apply hrV
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    have hy' : ‖y‖ < 2 := mem_ball_zero_iff.mp hy
    dsimp only [ρ]
    nlinarith
  have hSsource : S '' ball 0 2 ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hSV hy).1.1.1.1
  have hSopen : IsOpen (S '' ball 0 2) :=
    ((isOpenMap_add_left b).comp (isOpenMap_smul₀ hρ.ne')) _ isOpen_ball
  have hSinj : Function.Injective S := by
    intro y z hyz
    exact (smul_right_injective _ hρ.ne') (add_left_cancel hyz)
  have hregion (y : AmbientSpace) (hy : y ∈ ball 0 2) :
      neumannLocalizeMap c a ρ y ∈ c.region := (hSV hy).1.1.2
  have hside (y : AmbientSpace) (hy : y ∈ ball 0 2) :=
    hsides (graphProjectionN 2 (S y)) (hSV hy).1.2
      (S y (Fin.last 2)) (hSV hy).2
  have hlast (y : AmbientSpace) : S y (Fin.last 2) = ρ * y (Fin.last 2) := by
    simp only [S, b, PiLp.add_apply, graphAppendN_last, PiLp.smul_apply,
      smul_eq_mul, zero_add]
  have hinside (y : AmbientSpace) (hy : y ∈ ball 0 2) :
      neumannLocalizeMap c a ρ y ∈ D ↔ 0 < y (Fin.last 2) := by
    rw [hc _ (hregion y hy)]
    change c.placement.symm (c.placement (boundaryNormalChart c.height (S y))) ∈
      smoothSubgraph c.height ↔ _
    rw [c.placement.symm_apply_apply]
    have h := (hside y hy).1
    rw [graphAppendN_projection, hlast, mul_pos_iff_of_pos_left hρ] at h
    exact h
  refine ⟨ρ, hρ, ?_⟩
  change neumannLocalizeMap c a ρ 0 = p ∧ _
  refine ⟨?_, contDiff_neumannLocalizeMap_c2 c hψ a ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [neumannLocalizeMap, smul_zero, add_zero, boundaryNormalChart_face] using hpa
  · intro y hy z hz heq
    apply hSinj
    apply e.injOn (hSV hy).1.1.1.1 (hSV hz).1.1.1.1
    rw [he]
    exact c.placement.injective heq
  · intro y hy
    exact neumannLocalizeMap_regular_c2 c hψ a hρ (hreg _ (hSV hy).1.1.1.1)
  · rintro _ ⟨y, hy, rfl⟩
    exact hregion y hy
  · rintro _ ⟨y, hy, rfl⟩
    exact (hinside y hy.1).mpr hy.2
  · rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hcl
    have hcl' : neumannLocalizeMap c a ρ y ∈ closure c.graphDomain :=
      (hc.closure_inter_eq ▸ (show neumannLocalizeMap c a ρ y ∈ closure D ∩ c.region
        from ⟨hcl, hregion y hy.1⟩)).1
    rw [c.mem_closure_graphDomain_iff] at hcl'
    change c.placement.symm (c.placement (boundaryNormalChart c.height (S y)))
      (Fin.last 2) ≤ c.height (graphProjectionN 2
        (c.placement.symm (c.placement (boundaryNormalChart c.height (S y))))) at hcl'
    simp only [c.placement.symm_apply_apply] at hcl'
    have h := (hside y hy.1).2
    rw [graphAppendN_projection, hlast] at h
    exact (not_lt_of_ge hcl') (h.mpr (mul_neg_of_pos_of_neg hρ hy.2))
  · rintro _ ⟨y, hy, rfl⟩
    have hzero : S y (Fin.last 2) = 0 := by rw [hlast, hy.2, mul_zero]
    have hface : boundaryNormalChart c.height (S y) =
        graphMapN c.height (graphProjectionN 2 (S y)) := by
      conv_lhs => rw [← graphAppendN_projection (S y), hzero]
      exact boundaryNormalChart_face _ _
    have hg : neumannLocalizeMap c a ρ y ∈ c.graphSurface :=
      ⟨boundaryNormalChart c.height (S y), ⟨graphProjectionN 2 (S y), hface.symm⟩, rfl⟩
    exact (hc.frontier_inter_eq.symm ▸
      (show neumannLocalizeMap c a ρ y ∈ c.graphSurface ∩ c.region from
        ⟨hg, hregion y hy.1⟩)).1
  · have ho := c.placement.toHomeomorph.isOpenMap _
      (e.isOpen_image_of_subset_source hSopen hSsource)
    change IsOpen (c.placement '' (e '' (S '' ball 0 2))) at ho
    rw [image_image, image_image, he] at ho
    exact ho
  · let T := neumannLocalizeDilation b hρ.ne'
    refine ⟨(T.trans E).trans c.placement.toHomeomorph, _, _,
      (c.placement.isometry.lipschitzWith.comp hE).comp
        (neumannLocalizeDilation_lipschitz b hρ.ne'),
      ((neumannLocalizeDilation_symm_lipschitz b hρ.ne').comp hEi).comp
        c.placement.symm.isometry.lipschitzWith, ?_⟩
    intro y hy
    exact congrArg c.placement (hEq (hSV hy).1.1.1.2)

/-- The exact localized weak equation needs only C² height. -/
theorem IsWeakNeumannSolution.normal_chart_test_eq_c2
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ 2 c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) (E : AmbientSpace ≃ₜ AmbientSpace)
    (hEq : EqOn (neumannLocalizeMap c a ρ) E (ball 0 2))
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    (hregion : neumannLocalizeMap c a ρ '' ball 0 2 ⊆ c.region)
    (hupper : neumannLocalizeMap c a ρ '' boundaryHalfBall 2 ⊆ D)
    (hlower : Disjoint (neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D))
    (hface : neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball 0 1) :
    let Θ := neumannLocalizeMap c a ρ
    (∫ y in boundaryHalfBall 1,
        inner ℝ (neumannLocalizeCoefficient Θ y
          ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)) =
      -(∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y) -
        ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
          (-(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
            Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) * φ (graphBaseEmbedding t) := by
  let Θ := neumannLocalizeMap c a ρ
  let Ψ := φ ∘ E.symm
  have hΘ : ContDiff ℝ 1 Θ := contDiff_neumannLocalizeMap_c2 c hψ a ρ
  obtain ⟨hΨ, hcΨ, hsΨ, hcomp⟩ := neumannLocalize_pushforward_test hΘ E hEq hreg hφ hcφ hsφ
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hside := fun y hy => neumannLocalize_mem_domain_iff hD hupper hlower hface (y := y) hy
  have hinj : InjOn Θ (boundaryHalfBall 1) := by
    intro x hx y hy heq
    apply E.injective
    rw [← hEq (hball hx.1), ← hEq (hball hy.1)]
    exact heq
  have hgrad (y : AmbientSpace) (hy : y ∈ boundaryHalfBall 1) :
      gradient φ y = (fderiv ℝ Θ y).adjoint (gradient Ψ (Θ y)) := by
    have he : Ψ ∘ Θ =ᶠ[𝓝 y] φ :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (hball hy.1)) (fun x hx => hcomp hx)
    exact he.gradient_eq.symm.trans
      (neumannLocalize_gradient_comp (hΘ.differentiable one_ne_zero _)
        (hΨ.differentiable one_ne_zero _))
  have hsinner : tsupport (fun x => inner ℝ (z.gradientLp x) (gradient Ψ x)) ⊆ tsupport Ψ := by
    apply closure_minimal ?_ (isClosed_tsupport Ψ)
    intro x hx
    by_contra hn
    apply hx
    change inner ℝ (z.gradientLp x) (gradient Ψ x) = 0
    rw [gradient_eq_zero_of_notMem_tsupport hn, inner_zero_right]
  have henergy : (∫ x in D, inner ℝ (z.gradientLp x) (gradient Ψ x)) =
      ∫ y in boundaryHalfBall 1, inner ℝ
        (neumannLocalizeCoefficient Θ y ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y))))
        (gradient φ y) := by
    rw [neumannLocalize_integral_domain hD E hEq hside (hsinner.trans hsΨ)]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (isOpen_boundaryHalfBall 1).measurableSet
      (fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt) hinj]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall 1).measurableSet
    intro y hy
    change |(fderiv ℝ Θ y).det| * inner ℝ (z.gradientLp (Θ y)) (gradient Ψ (Θ y)) =
      inner ℝ (neumannLocalizeCoefficient Θ y
        ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)
    rw [hgrad y hy]
    exact (neumannLocalize_dirichlet_pairing Θ (hreg y (hball hy.1))
      (z.gradientLp (Θ y)) (gradient Ψ (Θ y))).symm
  have hforcing : (∫ x in D, f₀ x * Ψ x) =
      ∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y := by
    rw [neumannLocalize_integral_domain hD E hEq hside
      (tsupport_mul_subset_right.trans hsΨ)]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (isOpen_boundaryHalfBall 1).measurableSet
      (fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt) hinj]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall 1).measurableSet
    intro y hy
    have hp : Ψ (Θ y) = φ y := hcomp (hball hy.1)
    change |(fderiv ℝ Θ y).det| * (f₀ (Θ y) * Ψ (Θ y)) =
      f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y
    rw [hp]
    ring
  have hboundary := neumannLocalize_boundary_integral hc a hρ E hEq hregion
    (fun y hy hfront => neumannLocalize_face_of_mem_frontier hD hupper hlower hy hfront) h₀ hsφ
  have hw := hz.ambient_test_eq hf hh hΨ hcΨ
  rw [henergy, hforcing] at hw
  dsimp only [Function.comp_def] at hw
  rw [hboundary] at hw
  simpa only [neg_mul, integral_neg, sub_neg_eq_add] using hw

/-- A C² boundary chart supplies the H¹ pullback and its exact weak Neumann equation. -/
theorem IsWeakNeumannSolution.exists_normal_chart_c2_of_c3
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ 2 c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0,
      let a := graphProjectionN 2 (c.placement.symm p)
      let Θ := neumannLocalizeMap c a ρ
      Θ 0 = p ∧ ContDiff ℝ 1 Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧ Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      HasH1GradientOn (fun y => z (Θ y))
        (fun y => (fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y))) (boundaryHalfBall 1) ∧
      ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ ball 0 1 →
        (∫ y in boundaryHalfBall 1,
          inner ℝ (neumannLocalizeCoefficient Θ y
            ((fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))) (gradient φ y)) =
          -(∫ y in boundaryHalfBall 1, f₀ (Θ y) * |(fderiv ℝ Θ y).det| * φ y) -
            ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
              (-(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
                Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) *
                  φ (graphBaseEmbedding t) := by
  obtain ⟨ρ, hρ, h0, hΘ, hinj, hreg, hregion, hupper, hlower, hface, hopen,
    E, C, K, hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap_c2 hψ hp hpc
  refine ⟨ρ, hρ, h0, hΘ, hinj, hreg, hregion, hupper, hlower, hface, hopen, ?_, ?_⟩
  · exact neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
      ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  · intro φ hφ hcφ hsφ
    exact hz.normal_chart_test_eq_c2 hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      hφ hcφ hsφ

end LiquidDrop
