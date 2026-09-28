import NoCompromise.Flow.FlowBox
import NoCompromise.Surface.Geometry

/-!
# Integral curves tangent to an embedded surface

`cor:flow-manifold` for embedded surfaces at the C¹ level, pending the user's
wording decision on C¹ versus smooth. Local coordinates are obtained from the
implicit function theorem; tangential differentiation of the resulting local
retraction identifies the coordinate ODE with the ambient ODE.
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A local surface parametrization with a fixed linear coordinate projection.
Its derivative is inverse to that projection on the intrinsic tangent plane. -/
theorem IsSmoothEmbeddedSurface.exists_tangent_parametrization
    {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) {U : Set E₃} (hU : IsOpen U)
    {q : E₃} (hq : q ∈ S ∩ U) :
    ∃ (K : Submodule ℝ E₃) (P : E₃ →L[ℝ] K) (r : K → E₃) (V : Set K),
      IsOpen V ∧ (0 : K) ∈ V ∧ r 0 = q ∧ ContDiffOn ℝ 1 r V ∧
      ∀ k ∈ V, r k ∈ S ∩ U ∧
        ∀ v ∈ tangentPlane S (r k), fderiv ℝ r k (P v) = v := by
  obtain ⟨W, φ, hW, hqW, hφ, hzero, hreg⟩ := hS q hq.1
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hd := hφ1.contDiffAt.hasStrictFDerivAt one_ne_zero (x := q)
  have hsurj : (fderiv ℝ φ q).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hh
    apply hreg q ⟨hq.1, hqW⟩
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hh
  let K := (fderiv ℝ φ q).ker
  have hK := (fderiv ℝ φ q).ker_closedComplemented_of_finiteDimensional_range
  let P : E₃ →L[ℝ] K := Classical.choose hK
  let d := hd.implicitFunctionDataOfComplemented φ (fderiv ℝ φ q) hsurj hK
  let e := d.toOpenPartialHomeomorph
  have he (x : E₃) : e x = (φ x, P (x - q)) := rfl
  have hqzero : φ q = 0 := (hzero ▸ (show q ∈ S ∩ W from ⟨hq.1, hqW⟩)).2
  have heq : e q = (0, 0) := by simp [he, hqzero]
  have hqs : q ∈ e.source := d.pt_mem_toOpenPartialHomeomorph_source
  have hqt : (0, 0) ∈ e.target := heq ▸ e.map_source hqs
  have hinv : e.symm (0, 0) = q := heq ▸ e.left_inv hqs
  have heC : ContDiff ℝ 1 e :=
    hφ1.prodMk (P.contDiff.comp (contDiff_id.sub contDiff_const))
  have hiC : ContDiffAt ℝ 1 e.symm (0, 0) := by
    apply e.contDiffAt_symm hqt
    · rw [hinv]
      exact d.hasStrictFDerivAt.hasFDerivAt
    · exact heC.contDiffAt
  let r : K → E₃ := fun k => e.symm (0, k)
  have hr0 : r 0 = q := hinv
  have hrC : ContDiffAt ℝ 1 r 0 :=
    hiC.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨A, hAo, h0A, hAC⟩ := hrC.contDiffOn' le_rfl (by simp)
  have hAC : ContDiffOn ℝ 1 r A := by simpa using hAC
  have hn : ∀ᶠ k in 𝓝 (0 : K), r k ∈ W ∩ U ∧ r k ∈ e.source ∧
      (0, k) ∈ e.target := by
    have h₁ := hrC.continuousAt.preimage_mem_nhds
      (hr0.symm ▸ (hW.inter hU).mem_nhds ⟨hqW, hq.2⟩)
    have h₂ : ∀ᶠ k in 𝓝 (0 : K), r k ∈ e.source :=
      hrC.continuousAt.eventually (by rw [hr0]; exact e.open_source.mem_nhds hqs)
    have hpair : Continuous (fun k : K => ((0 : ℝ), k)) :=
      continuous_const.prodMk continuous_id
    have h₃ := hpair.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds hqt)
    filter_upwards [h₁, h₂, h₃] with k h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨B, hBsub, hBo, h0B⟩ := mem_nhds_iff.mp hn
  refine ⟨K, P, r, A ∩ B, hAo.inter hBo, ⟨h0A, h0B⟩, hr0,
    hAC.mono inter_subset_left, ?_⟩
  intro k hk
  obtain ⟨hkWU, hks, hkt⟩ := hBsub hk.2
  have hcoord : (φ (r k), P (r k - q)) = (0, k) := e.right_inv hkt
  have hkS : r k ∈ S :=
    ((congrArg (fun T : Set E₃ => r k ∈ T) hzero).mpr
      ⟨hkWU.1, congrArg Prod.fst hcoord⟩).1
  refine ⟨⟨hkS, hkWU.2⟩, fun v hv => ?_⟩
  have hPk : P (r k - q) = k := congrArg Prod.snd hcoord
  have hrD : DifferentiableAt ℝ r k :=
    (hAC.contDiffAt (hAo.mem_nhds hk.1)).differentiableAt one_ne_zero
  have hcomp : HasFDerivAt (fun x => r (P (x - q)))
      ((fderiv ℝ r k).comp P) (r k) := by
    have hdP : HasFDerivAt (fun x => P (x - q)) P (r k) := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using!
        P.hasFDerivAt.comp (r k) ((hasFDerivAt_id (r k)).sub_const q)
    have hrD' : HasFDerivAt r (fderiv ℝ r k) (P (r k - q)) := by
      rw [hPk]
      exact hrD.hasFDerivAt
    exact hrD'.comp (r k) hdP
  have heqS : (fun x => r (P (x - q))) =ᶠ[𝓝[S] (r k)] id := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hkWU.1),
      mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hks)] with x hxS hxW hxs
    have hxzero : φ x = 0 :=
      (hzero ▸ (show x ∈ S ∩ W from ⟨hxS, hxW⟩)).2
    change e.symm (0, P (x - q)) = x
    rw [← hxzero, ← he]
    exact e.left_inv hxs
  have hh := fderiv_eq_on_tangentPlane hcomp.differentiableAt
    (differentiableAt_id (𝕜 := ℝ)) heqS hv
  simpa only [hcomp.fderiv, ContinuousLinearMap.comp_apply, fderiv_id,
    ContinuousLinearMap.id_apply] using hh

/-- `cor:flow-manifold`, local existence on an embedded surface for a C¹ ambient
field tangent to the surface. C¹ is pending the user's wording decision on C¹
versus smooth. -/
theorem exists_integralCurve_local_on_surface {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {U : Set E₃} (hU : IsOpen U)
    {X : E₃ → E₃} (hX : ContDiffOn ℝ 1 X U)
    (htan : ∀ p ∈ S ∩ U, X p ∈ tangentPlane S p)
    {q : E₃} (hq : q ∈ S ∩ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → E₃, γ 0 = q ∧
      ∀ t ∈ Ioo (-ε) ε, γ t ∈ S ∩ U ∧ HasDerivAt γ (X (γ t)) t := by
  obtain ⟨K, P, r, V, hVo, h0V, hr0, hrC, hr⟩ :=
    hS.exists_tangent_parametrization hU hq
  let Y : K → K := fun k => P (X (r k))
  have hY : ContDiffOn ℝ 1 Y V :=
    P.contDiff.comp_contDiffOn (hX.comp hrC (fun k hk => (hr k hk).1.2))
  obtain ⟨ε, hε, hex⟩ := exists_integralCurve_local hVo hY
    (isCompact_singleton (x := (0 : K))) (singleton_subset_iff.mpr h0V)
  obtain ⟨γ, hγ0, hγ⟩ := hex 0 (mem_singleton 0)
  refine ⟨ε, hε, r ∘ γ, by simp [hγ0, hr0], fun t ht => ?_⟩
  have hγV := (hγ t ht).1
  refine ⟨(hr (γ t) hγV).1, ?_⟩
  have hrD := (hrC.contDiffAt (hVo.mem_nhds hγV)).differentiableAt one_ne_zero
  have hd := hrD.hasFDerivAt.comp_hasDerivAt t (hγ t ht).2
  have he := (hr (γ t) hγV).2 (X (r (γ t))) (htan _ (hr (γ t) hγV).1)
  simpa only [Y, he, Function.comp_def] using hd

/-- `cor:flow-manifold`: an integral curve of a C¹ field tangent to a closed
embedded surface stays on that surface. C¹ is pending the user's wording
decision on C¹ versus smooth. -/
theorem integralCurve_mem_of_tangent {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hSc : IsClosed S) {U : Set E₃} (hU : IsOpen U) {X : E₃ → E₃}
    (hX : ContDiffOn ℝ 1 X U) (htan : ∀ p ∈ S ∩ U, X p ∈ tangentPlane S p)
    {I : Set ℝ} (hI : I.OrdConnected) {γ : ℝ → E₃} {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hγ : ∀ t ∈ I, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t) (hγ0 : γ t₀ ∈ S) :
    ∀ t ∈ I, γ t ∈ S := by
  have hc : ContinuousOn γ I := fun t ht => (hγ t ht).2.continuousAt.continuousWithinAt
  let A : Set I := {t | γ t ∈ S}
  have hAc : IsClosed A := hSc.preimage (continuousOn_iff_continuous_domRestrict.mp hc)
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨ε, hε, η, hη0, hη⟩ := exists_integralCurve_local_on_surface hS hU hX htan
      (show γ s ∈ S ∩ U from ⟨hs, (hγ s s.property).1⟩)
    let J := I ∩ Ioo ((s : ℝ) - ε) ((s : ℝ) + ε)
    have hsJ : (s : ℝ) ∈ J := ⟨s.property, by constructor <;> linarith⟩
    have hJ : J.OrdConnected := hI.inter ordConnected_Ioo
    have htime (t : ℝ) (ht : t ∈ J) : t - s ∈ Ioo (-ε) ε := by
      constructor <;> linarith [ht.2.1, ht.2.2]
    have heq : EqOn γ (fun t => η (t - s)) J := by
      apply integralCurve_unique_of_contDiffOn hU hX hJ hsJ
      · exact fun t ht => hγ t ht.1
      · intro t ht
        exact ⟨(hη (t - s) (htime t ht)).1.2,
          HasDerivAt.comp_sub_const t s (hη (t - s) (htime t ht)).2⟩
      · simpa using hη0.symm
    have hnear : ∀ᶠ t : I in 𝓝 s, (t : ℝ) ∈ Ioo ((s : ℝ) - ε) ((s : ℝ) + ε) :=
      continuous_subtype_val.continuousAt.eventually
        (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hnear] with t ht
    change γ t ∈ S
    rw [heq ⟨t.property, ht⟩]
    exact (hη (t - s) (htime t ⟨t.property, ht⟩)).1.1
  have : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI.isPreconnected
  have hA : A = univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ ⟨⟨t₀, ht₀⟩, hγ0⟩
  intro t ht
  exact (show (⟨t, ht⟩ : I) ∈ A from hA ▸ mem_univ _)

/-- `cor:flow-manifold`, compact case (C¹ level, pending the user's wording decision on C¹ versus
smooth): a C¹ field defined near a compact embedded surface and tangent to it is complete on the
surface; its integral curve through any point of the surface exists for all time and stays in the
surface. -/
theorem exists_complete_integralCurve_of_tangent {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hSc : IsCompact S) {U : Set E₃} (hU : IsOpen U) (hSU : S ⊆ U) {X : E₃ → E₃}
    (hX : ContDiffOn ℝ 1 X U) (htan : ∀ p ∈ S, X p ∈ tangentPlane S p) {x : E₃}
    (hx : x ∈ S) :
    ∃ γ : ℝ → E₃, γ 0 = x ∧ ∀ t, γ t ∈ S ∧ HasDerivAt γ (X (γ t)) t := by
  obtain ⟨Y, hY, hYc, V, _, hSV, _, hYX⟩ := exists_compactSupport_eq_near hU hX hSc hSU
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  let γ : ℝ → E₃ := fun t => globalFlow Y hL hM t x
  have hd : ∀ t, HasDerivAt γ (Y (γ t)) t := fun t => hasDerivAt_globalFlow hL hM x t
  have hmem : ∀ t ∈ (univ : Set ℝ), γ t ∈ S :=
    integralCurve_mem_of_tangent hS hSc.isClosed isOpen_univ hY.contDiffOn
      (fun p hp => (hYX (hSV hp.1)).symm ▸ htan p hp.1) ordConnected_univ (mem_univ 0)
      (fun t _ => ⟨mem_univ _, hd t⟩) (by simpa [γ] using hx)
  refine ⟨γ, by simp [γ], fun t => ⟨hmem t (mem_univ t), ?_⟩⟩
  rw [← hYX (hSV (hmem t (mem_univ t)))]
  exact hd t

end LiquidDrop
