import NoCompromise.Elliptic.BoundaryNeumannSmoothTangential
import NoCompromise.Elliptic.BoundaryHolderTranslate

/-!
# Differentiating the weak divergence equation (`thm:boundary-C2a`, iteration)

The weak divergence equation `div(A F) = div G` on an open set `U`, with C¹ compactly
supported test functions whose support lies in `U`, is invariant under small translations of
the test function. If the flux `A F - G` is C¹ on `U`, dominated convergence passes the
translated identities to the coordinate derivative of the flux: `∫ ⟨∂ᵢ(A F - G), ∇φ⟩ = 0`.
For a C² function `u` with `F = ∇u` and C¹ coefficient and datum this says that the
coordinate derivative `∂ᵢu` solves `div(A ∇∂ᵢu) = div(∂ᵢG - (∂ᵢA) ∇u)` on the same open set.
On a flat half ball the test functions vanish near the face, so this is the tangential and the
normal differentiation step of the Dirichlet boundary iteration; no ellipticity is used.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The gradient of a C¹ function vanishes off the topological support. -/
lemma boundaryC2aDifferentiate_gradient_eq_zero {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ tsupport φ) : gradient φ x = 0 := by
  have h : φ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [gradient, h.fderiv_eq]
  simp

/-- A function continuous on a compact set and vanishing off it is integrable. -/
lemma boundaryC2aDifferentiate_integrable {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hf : ContinuousOn f K)
    (h0 : ∀ x ∉ K, f x = 0) : Integrable f := by
  have hs : Function.support f ⊆ K := fun x hx => by
    by_contra h
    exact hx (h0 x h)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp (hf.integrableOn_compact hK)

/-- Differentiation of the weak divergence equation along a coordinate direction: if the flux
`A F - G` is C¹ on the open set `U`, its coordinate derivative has vanishing weak divergence
on `U` against every C¹ compactly supported test function supported in `U`. -/
theorem isWeakDivergenceEquationOn_flux_derivative
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : IsWeakDivergenceEquationOn A F G U)
    (hΦ : ContDiffOn ℝ 1 (fun x => A x (F x) - G x) U) (i : Fin 3) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ x, inner ℝ (fderiv ℝ (fun y => A y (F y) - G y) x (EuclideanSpace.single i 1))
        (gradient φ x)) = 0 := by
  intro φ hφ hcφ hsφ
  set Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun y => A y (F y) - G y
    with hΦdef
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i (1 : ℝ) with he
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hcφ
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hsφ
  have hL : IsCompact (cthickening δ K) := hK.cthickening
  have hDΦ : ContinuousOn (fderiv ℝ Φ) U :=
    (hΦ.fderiv_of_isOpen hU (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (hDΦ.mono hδU)
  have hgφ : Continuous (gradient φ) := continuous_gradient_of_contDiff hφ
  have he1 : ‖e‖ = 1 := by simp [he]
  have hgz : ∀ x ∉ K, gradient φ x = 0 := fun x hx => boundaryC2aDifferentiate_gradient_eq_zero hx
  -- translates of `K` by at most `δ` stay in `U`
  have hmemL {s : ℝ} (hs : |s| ≤ δ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K) :
      x + s • e ∈ cthickening δ K := by
    refine mem_cthickening_of_dist_le _ x δ K hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he1, mul_one, Real.norm_eq_abs]
    exact hs
  have hsmall : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| ≤ δ := by
    have ht : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ ball 0 δ :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ)
    exact ht.mono fun s hs => (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs]
      using hs : |s| < δ).le
  -- continuity of the translated flux on `K`
  have hcont {s : ℝ} (hs : |s| ≤ δ) : ContinuousOn (fun x => Φ (x + s • e)) K :=
    (hΦ.continuousOn.mono hδU).comp (continuous_id.add continuous_const).continuousOn
      (fun x hx => hmemL hs hx)
  have hint {s : ℝ} (hs : |s| ≤ δ) :
      Integrable (fun x => inner ℝ (Φ (x + s • e)) (gradient φ x)) :=
    boundaryC2aDifferentiate_integrable hK ((hcont hs).inner hgφ.continuousOn)
      fun x hx => by simp [hgz x hx]
  -- the translated identities
  have hshift {s : ℝ} (hs : |s| ≤ δ) :
      (∫ x, inner ℝ (Φ (x + s • e)) (gradient φ x)) = 0 := by
    have ht := hw.boundary_translate (s • e) (V := K) fun x hx => hδU (hmemL hs hx)
    exact ht φ hφ hcφ subset_rfl
  have hquot {s : ℝ} (hs : |s| ≤ δ) :
      (∫ x, inner ℝ (coordinateDifferenceQuotient i s Φ x) (gradient φ x)) = 0 := by
    have h0 : |(0 : ℝ)| ≤ δ := by simpa using hδ.le
    have hsplit : (fun x => inner ℝ (coordinateDifferenceQuotient i s Φ x) (gradient φ x)) =
        fun x => s⁻¹ * (inner ℝ (Φ (x + s • e)) (gradient φ x) -
          inner ℝ (Φ (x + (0 : ℝ) • e)) (gradient φ x)) := by
      funext x
      simp only [coordinateDifferenceQuotient, zero_smul, add_zero, inner_smul_left,
        inner_sub_left, he]
      simp
    rw [hsplit, integral_const_mul, integral_sub (hint hs) (hint h0), hshift hs, hshift h0]
    simp
  -- the difference quotients are bounded by `B` on `K`
  have hbound {s : ℝ} (hs : |s| ≤ δ) (hs0 : s ≠ 0) {x : EuclideanSpace ℝ (Fin 3)}
      (hx : x ∈ K) : ‖coordinateDifferenceQuotient i s Φ x‖ ≤ B := by
    have hball : closedBall x δ ⊆ cthickening δ K := fun y hy =>
      mem_cthickening_of_dist_le y x δ K hx (mem_closedBall.mp hy)
    have hy : x + s • e ∈ closedBall x δ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, he1, mul_one,
        Real.norm_eq_abs]
      exact hs
    have hb := (convex_closedBall x δ).norm_image_sub_le_of_norm_fderiv_le
      (f := Φ) (C := B)
      (fun y hy => (hΦ.contDiffAt (hU.mem_nhds (hδU (hball hy)))).differentiableAt
        one_ne_zero)
      (fun y hy => hB y (hball hy)) (mem_closedBall_self hδ.le) hy
    rw [coordinateDifferenceQuotient, norm_smul]
    apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
    rw [add_sub_cancel_left, norm_smul, he1, mul_one, norm_inv, mul_left_comm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs0), mul_one]
  have hlimit : Tendsto
      (fun s : ℝ => ∫ x, inner ℝ (coordinateDifferenceQuotient i s Φ x) (gradient φ x))
      (𝓝[≠] 0) (𝓝 (∫ x, inner ℝ (fderiv ℝ Φ x e) (gradient φ x))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => B * ‖gradient φ x‖)
    · filter_upwards [hsmall] with s hs
      have h0 : |(0 : ℝ)| ≤ δ := by simpa using hδ.le
      have hc : Integrable fun x =>
          inner ℝ (coordinateDifferenceQuotient i s Φ x) (gradient φ x) := by
        have hsplit : (fun x => inner ℝ (coordinateDifferenceQuotient i s Φ x)
            (gradient φ x)) = fun x => s⁻¹ * (inner ℝ (Φ (x + s • e)) (gradient φ x) -
              inner ℝ (Φ (x + (0 : ℝ) • e)) (gradient φ x)) := by
          funext x
          simp only [coordinateDifferenceQuotient, zero_smul, add_zero, inner_smul_left,
            inner_sub_left, he]
          simp
        rw [hsplit]
        exact ((hint hs).sub (hint h0)).const_mul _
      exact hc.aestronglyMeasurable
    · filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hs0
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hbound hs hs0 hx) (norm_nonneg _))
      · rw [hgz x hx]
        simp
    · exact boundaryC2aDifferentiate_integrable hK (hgφ.norm.const_mul B).continuousOn
        fun x hx => by simp [hgz x hx]
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K
      · exact (boundary_neumann_smooth_quotient_tendsto
          ((hΦ.contDiffAt (hU.mem_nhds (hsφ hx))).differentiableAt one_ne_zero) i).inner
            tendsto_const_nhds
      · simp only [hgz x hx, inner_zero_right]
        exact tendsto_const_nhds
  have hzero : ∀ᶠ s : ℝ in 𝓝[≠] 0,
      (∫ x, inner ℝ (coordinateDifferenceQuotient i s Φ x) (gradient φ x)) = 0 := by
    filter_upwards [hsmall] with s hs
    exact hquot hs
  exact tendsto_nhds_unique (hlimit.congr' hzero) tendsto_const_nhds

/-- **The differentiated weak equation.** If `u` is C² on the open set `U`, the coefficient
`A` and datum `G` are C¹ on `U`, and `div(A ∇u) = div G` weakly on `U`, then for every
coordinate direction `i` the derivative `∂ᵢu` solves `div(A ∇∂ᵢu) = div(∂ᵢG - (∂ᵢA) ∇u)`
weakly on `U`. -/
theorem IsWeakDivergenceEquationOn.coordinate_derivative
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 1 A U) (hG : ContDiffOn ℝ 1 G U) (hu : ContDiffOn ℝ 2 u U)
    (hw : IsWeakDivergenceEquationOn A (gradient u) G U) (i : Fin 3) :
    IsWeakDivergenceEquationOn A
      (gradient (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)))
      (fun x => fderiv ℝ G x (EuclideanSpace.single i 1) -
        fderiv ℝ A x (EuclideanSpace.single i 1) (gradient u x)) U := by
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hGu : ContDiffOn ℝ 1 (gradient u) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDu
  have hΦ : ContDiffOn ℝ 1 (fun x => A x (gradient u x) - G x) U :=
    (hA.clm_apply hGu).sub hG
  intro φ hφ hcφ hsφ
  rw [← isWeakDivergenceEquationOn_flux_derivative hU hw hΦ i φ hφ hcφ hsφ]
  congr 1
  funext x
  by_cases hx : x ∈ tsupport φ
  · have hxU := hsφ hx
    have hAd := (hA.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero
    have hGd := (hG.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero
    have hgd := (hGu.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero
    have hder : fderiv ℝ (fun y => A y (gradient u y) - G y) x (EuclideanSpace.single i 1) =
        A x (fderiv ℝ (gradient u) x (EuclideanSpace.single i 1)) +
          fderiv ℝ A x (EuclideanSpace.single i 1) (gradient u x) -
          fderiv ℝ G x (EuclideanSpace.single i 1) := by
      rw [fderiv_fun_sub (hAd.clm_apply hgd) hGd, fderiv_clm_apply hAd hgd]
      simp only [sub_apply, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [hder, boundary_neumann_smooth_gradient_coordinate hU hu hxU i]
    congr 1
    exact sub_sub_eq_add_sub (a := A x (fderiv ℝ (gradient u) x (EuclideanSpace.single i 1)))
      (b := fderiv ℝ G x (EuclideanSpace.single i 1))
      (c := fderiv ℝ A x (EuclideanSpace.single i 1) (gradient u x))
  · simp [boundaryC2aDifferentiate_gradient_eq_zero hx]

/-- **The classical equation from the weak one.** For `u` C² and `A`, `G` C¹ on an open set
`U`, the weak equation `div(A ∇u) = div G` on `U` holds pointwise on `U` in the expanded form
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ (∂ᵢAᵢⱼ) ∂ⱼu = div G`, with `Aᵢⱼ = A x eⱼ · eᵢ`. -/
theorem IsWeakDivergenceEquationOn.pointwise_equation
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 1 A U) (hG : ContDiffOn ℝ 1 G U) (hu : ContDiffOn ℝ 2 u U)
    (hw : IsWeakDivergenceEquationOn A (gradient u) G U) :
    ∀ x ∈ U,
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry u x i j) +
      (∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * fderiv ℝ u x (EuclideanSpace.single j 1)) =
      divergenceN G x := by
  intro x hx
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hGu : ContDiffOn ℝ 1 (gradient u) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDu
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient u y) - G y) U := (hA.clm_apply hGu).sub hG
  have hflux : divergenceN (fun y => A y (gradient u y) - G y) x = 0 :=
    boundary_neumann_c2_divergence_eq_zero hU hF (fun φ hφ hcφ hsφ => hw φ hφ hcφ hsφ) hx
  have hdG := (hGu.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hpartial (i j : Fin 3) :
      fderiv ℝ (gradient u) x (EuclideanSpace.single i 1) j =
        boundaryNeumannC2Entry u x i j := by
    have he : (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) =
        fun y => gradient u y j := funext fun y => (gradient_apply_eq_fderiv_single u y j).symm
    unfold boundaryNeumannC2Entry
    rw [he]
    change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient u) x _
    rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
    rfl
  have hdA := (hA.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdH := (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hp := boundary_neumann_c2_divergence_product hdA hdG hdH
  rw [hflux] at hp
  simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
  linarith

end LiquidDrop
