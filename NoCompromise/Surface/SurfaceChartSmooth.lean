module

public import NoCompromise.Surface.MorseChart
import all Mathlib.Analysis.Calculus.Implicit

@[expose] public section

/-!
# Smooth projection charts and smooth chart pull-backs

`C^∞` versions of `IsSmoothEmbeddedSurface.exists_projection_chart` (`SurfaceChart.lean`) and
`exists_chart_pullback` (`MorseChart.lean`): the projection chart of an embedded surface has a
`C^∞` inverse on its whole target, and the pull-back of a smooth function through it is `C^∞`
on the whole target. This is the form in which `lem:morse-coords` is applied on the surface
(`lem:local-sectors` on `Σ`).
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

set_option maxSynthPendingDepth 8

/-- A `C^∞` chart of an embedded surface near `q` (input of `lem:morse-coords` on `Σ`), onto
an open subset of the plane, whose forward map is the restriction of a continuous linear
projection `x ↦ P (x - q)` and whose source is the trace of an ambient open set; the inverse
chart is `C^∞` on the whole target. -/
theorem IsSmoothEmbeddedSurface.exists_projection_chart_smooth {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {q : E₃} (hq : q ∈ S) :
    ∃ (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (U : Set E₃),
      IsOpen U ∧ q ∈ U ∧ e.source = Subtype.val ⁻¹' U ∧
      (⟨q, hq⟩ : S) ∈ e.source ∧ e ⟨q, hq⟩ = 0 ∧
      (∀ x : S, e x = P ((x : E₃) - q)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (e.symm y : E₃)) e.target := by
  classical
  obtain ⟨W, φ, hW, hqW, hφ, hzero, hreg⟩ := hS q hq
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hd := hφ1.contDiffAt.hasStrictFDerivAt one_ne_zero (x := q)
  have hsurj : (fderiv ℝ φ q).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hh
    apply hreg q ⟨hq, hqW⟩
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hh
  let K := (fderiv ℝ φ q).ker
  have hK := (fderiv ℝ φ q).ker_closedComplemented_of_finiteDimensional_range
  let P₀ : E₃ →L[ℝ] K := Classical.choose hK
  let d := hd.implicitFunctionDataOfComplemented φ (fderiv ℝ φ q) hsurj hK
  let E := d.toOpenPartialHomeomorph
  have hE (x : E₃) : E x = (φ x, P₀ (x - q)) := rfl
  have hKr : Module.finrank ℝ K = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)
    have hr : Module.finrank ℝ (LinearMap.range (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)) = 1 := by
      have : LinearMap.range (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ) = ⊤ := hsurj
      rw [this, finrank_top, Module.finrank_self]
    rw [hr, finrank_euclideanSpace_fin] at h1
    change Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)) = 2
    omega
  let J : K ≃L[ℝ] E2 :=
    (LinearEquiv.ofFinrankEq K E2
      (by rw [hKr, finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  let P : E₃ →L[ℝ] E2 := (J : K →L[ℝ] E2).comp P₀
  let ψ : E2 → E₃ := fun y => E.symm (0, J.symm y)
  have hqzero : φ q = 0 := (hzero ▸ (show q ∈ S ∩ W from ⟨hq, hqW⟩)).2
  have heq : E q = (0, 0) := by simp [hE, hqzero]
  have hqs : q ∈ E.source := d.pt_mem_toOpenPartialHomeomorph_source
  have hqt : (0, 0) ∈ E.target := heq ▸ E.map_source hqs
  have hinv : E.symm (0, 0) = q := heq ▸ E.left_inv hqs
  have heC : ContDiff ℝ (⊤ : ℕ∞) E :=
    (hφ.of_le (by exact_mod_cast le_top)).prodMk
      (P₀.contDiff.comp (contDiff_id.sub contDiff_const))
  -- the set where the derivative of `E` is invertible is open and contains `q`
  have hEd : Continuous (fderiv ℝ E) := heC.continuous_fderiv (by simp)
  let V : Set E₃ :=
    fderiv ℝ E ⁻¹' range ((↑) : (E₃ ≃L[ℝ] (ℝ × K)) → E₃ →L[ℝ] ℝ × K)
  have hVo : IsOpen V := ContinuousLinearEquiv.isOpen.preimage hEd
  have hqV : q ∈ V := ⟨_, (d.hasStrictFDerivAt.hasFDerivAt.fderiv).symm⟩
  have hiC : ∀ z ∈ E.target, E.symm z ∈ V → ContDiffAt ℝ (⊤ : ℕ∞) E.symm z := by
    intro z hz hzV
    obtain ⟨A, hA⟩ := hzV
    apply E.contDiffAt_symm hz (f₀' := A)
    · rw [hA]
      exact (heC.differentiable (by simp) _).hasFDerivAt
    · exact heC.contDiffAt
  have hpair : Continuous (fun y : E2 => ((0 : ℝ), J.symm y)) :=
    continuous_const.prodMk J.symm.continuous
  let O : Set E2 :=
    {y | ((0 : ℝ), J.symm y) ∈ E.target ∧ E.symm ((0 : ℝ), J.symm y) ∈ V}
  have hOo : IsOpen O := by
    have hψc : ContinuousOn ψ {y | ((0 : ℝ), J.symm y) ∈ E.target} :=
      E.continuousOn_symm.comp hpair.continuousOn fun y hy => hy
    exact hψc.isOpen_inter_preimage (E.open_target.preimage hpair) hVo
  have h0O : (0 : E2) ∈ O := by
    refine ⟨by simpa using hqt, ?_⟩
    simpa [hinv] using hqV
  have hψO' : ContDiffOn ℝ (⊤ : ℕ∞) ψ O := by
    intro y hy
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E2 => ((0 : ℝ), J.symm y)) y :=
      contDiffAt_const.prodMk (J.symm : E2 →L[ℝ] K).contDiff.contDiffAt
    exact ((hiC _ hy.1 hy.2).comp y hlin).contDiffWithinAt
  let T : Set E2 := O ∩ ({y | ((0 : ℝ), J.symm y) ∈ E.target} ∩ ψ ⁻¹' W)
  let U : Set E₃ := E.source ∩ W ∩ (fun x => P (x - q)) ⁻¹' O
  have hU : IsOpen U :=
    (E.open_source.inter hW).inter
      (hOo.preimage (P.continuous.comp (continuous_id.sub continuous_const)))
  have hT : IsOpen T := by
    refine hOo.inter ?_
    have hψc : ContinuousOn ψ {y | ((0 : ℝ), J.symm y) ∈ E.target} :=
      E.continuousOn_symm.comp hpair.continuousOn fun y hy => hy
    exact hψc.isOpen_inter_preimage (E.open_target.preimage hpair) hW
  -- basic identities
  have hPψ : ∀ y ∈ T, P (ψ y - q) = y := by
    intro y hy
    have h := E.right_inv hy.2.1
    have h2 : P₀ (ψ y - q) = J.symm y := by
      have := congrArg Prod.snd h
      simpa [hE, ψ] using this
    change J (P₀ (ψ y - q)) = y
    rw [h2]; simp
  have hψS : ∀ y ∈ T, ψ y ∈ S := by
    intro y hy
    have h := E.right_inv hy.2.1
    have h1 : φ (ψ y) = 0 := by
      have := congrArg Prod.fst h
      simpa [hE, ψ] using this
    have hmem : ψ y ∈ {x ∈ W | φ x = 0} := ⟨hy.2.2, h1⟩
    rw [← hzero] at hmem
    exact hmem.1
  have hψU : ∀ y ∈ T, ψ y ∈ U := by
    intro y hy
    refine ⟨⟨E.map_target hy.2.1, hy.2.2⟩, ?_⟩
    change P (ψ y - q) ∈ O
    rw [hPψ y hy]; exact hy.1
  have hEx : ∀ x : E₃, x ∈ S → x ∈ W → E x = ((0 : ℝ), J.symm (P (x - q))) := by
    intro x hxS hxW
    have hx0 : φ x = 0 := (hzero ▸ (show x ∈ S ∩ W from ⟨hxS, hxW⟩)).2
    simp [hE, hx0, P]
  have hmapT : ∀ x : E₃, x ∈ S → x ∈ U → P (x - q) ∈ T ∧ ψ (P (x - q)) = x := by
    intro x hxS hxU
    have hEx' := hEx x hxS hxU.1.2
    have hleft : ψ (P (x - q)) = x := by
      change E.symm ((0 : ℝ), J.symm (P (x - q))) = x
      rw [← hEx']
      exact E.left_inv hxU.1.1
    refine ⟨⟨hxU.2, ?_, ?_⟩, hleft⟩
    · change ((0 : ℝ), J.symm (P (x - q))) ∈ E.target
      rw [← hEx']
      exact E.map_source hxU.1.1
    · change ψ (P (x - q)) ∈ W
      rw [hleft]; exact hxU.1.2
  let inv : E2 → S := fun y => if hy : y ∈ T then ⟨ψ y, hψS y hy⟩ else ⟨q, hq⟩
  have hinvT : ∀ y ∈ T, (inv y : E₃) = ψ y := by
    intro y hy
    simp [inv, hy]
  let e : OpenPartialHomeomorph S E2 :=
    { toFun := fun x => P ((x : E₃) - q)
      invFun := inv
      source := Subtype.val ⁻¹' U
      target := T
      map_source' := fun x hx => (hmapT x x.2 hx).1
      map_target' := fun y hy => by
        change (inv y : E₃) ∈ U
        rw [hinvT y hy]; exact hψU y hy
      left_inv' := fun x hx => by
        apply Subtype.ext
        rw [hinvT _ (hmapT x x.2 hx).1]
        exact (hmapT x x.2 hx).2
      right_inv' := fun y hy => by
        rw [hinvT y hy]; exact hPψ y hy
      open_source := hU.preimage continuous_subtype_val
      open_target := hT
      continuousOn_toFun :=
        (P.continuous.comp (continuous_subtype_val.sub continuous_const)).continuousOn
      continuousOn_invFun := by
        rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
        exact (hψO'.continuousOn.mono inter_subset_left).congr fun y hy => hinvT y hy }
  refine ⟨e, P, U, hU, ?_, rfl, ?_, ?_, fun x => rfl, ?_⟩
  · have := hψU 0 ?_
    · simpa [ψ, hinv] using this
    · refine ⟨h0O, ?_, ?_⟩
      · simpa using hqt
      · change E.symm ((0 : ℝ), J.symm 0) ∈ W
        simpa [hinv] using hqW
  · change q ∈ U
    have := hψU 0 ?_
    · simpa [ψ, hinv] using this
    · refine ⟨h0O, ?_, ?_⟩
      · simpa using hqt
      · change E.symm ((0 : ℝ), J.symm 0) ∈ W
        simpa [hinv] using hqW
  · change P (q - q) = 0
    simp
  · exact (hψO'.mono inter_subset_left).congr fun y hy => hinvT y hy

/-- Polarization expansion of the surface Hessian (copy of the private helper in
`MorseChart.lean`, used for `lem:morse-coords` on `Σ`). -/
lemma surfaceHessian_add_add' (n : E₃ → E₃) (h : E₃ → ℝ) (p X Y : E₃) :
    surfaceHessian n h p (X + Y) (X + Y) =
      surfaceHessian n h p X X + surfaceHessian n h p X Y + surfaceHessian n h p Y X +
        surfaceHessian n h p Y Y := by
  simp only [surfaceHessian, secondFundamentalForm, map_add, add_apply,
    inner_add_left, inner_add_right]
  ring

/-- Smooth pull-back of a surface critical point through a projection chart (input of
`lem:morse-coords` on `Σ`): the chart inverse and the pulled-back function are `C^∞` on the
whole chart target, the pulled-back function vanishes to second order at `0`, and its Hessian
there is the tangential Hessian transported by a linear isomorphism, so nondegeneracy and the
index agree with those of `h` at `p`. -/
theorem exists_chart_pullback_smooth {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p) :
    ∃ (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (U : Set E₃),
      IsOpen U ∧ p ∈ U ∧ e.source = Subtype.val ⁻¹' U ∧
      (⟨p, hcrit.1⟩ : S) ∈ e.source ∧ e ⟨p, hcrit.1⟩ = 0 ∧
      (∀ x : S, e x = P ((x : E₃) - p)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (e.symm y : E₃)) e.target ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (chartPullback e h p) e.target ∧
      chartPullback e h p 0 = 0 ∧ fderiv ℝ (chartPullback e h p) 0 = 0 ∧
      (IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) ↔
        IsNondegenerateForm (tangentHessian S n h p)) ∧
      formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) =
        surfaceIndex S n h p := by
  obtain ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hCtop⟩ :=
    hS.exists_projection_chart_smooth hcrit.1
  have hgCtop : ContDiffOn ℝ (⊤ : ℕ∞) (chartPullback e h p) e.target :=
    (hh.comp_contDiffOn hCtop).sub contDiffOn_const
  refine ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hCtop, hgCtop, ?_⟩
  have hC : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => (e.symm y : E₃)) e.target :=
    hCtop.of_le (WithTop.coe_le_coe.mpr le_top)
  have h0t : (0 : E2) ∈ e.target := he0 ▸ e.map_source hps
  have hψ0 : (e.symm 0 : E₃) = p := by
    have := e.left_inv hps
    rw [he0] at this
    exact congrArg Subtype.val this
  have hψC : ContDiffAt ℝ 3 (fun y => (e.symm y : E₃)) 0 :=
    hC.contDiffAt (e.open_target.mem_nhds h0t)
  have hψd : DifferentiableAt ℝ (fun y => (e.symm y : E₃)) 0 :=
    hψC.differentiableAt (by norm_num)
  have hh3 : ContDiff ℝ 3 h :=
    hh.of_le (show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hgC : ContDiffAt ℝ 3 (chartPullback e h p) 0 :=
    (hh3.contDiffAt.comp 0 hψC).sub contDiffAt_const
  have hg0 : chartPullback e h p 0 = 0 := by simp [chartPullback, hψ0]
  have htan : ∀ v, fderiv ℝ (fun y => (e.symm y : E₃)) 0 v ∈ tangentPlane S p := by
    intro v
    have := chart_fderiv_mem_tangentPlane (by norm_num) hC h0t v
    rwa [hψ0] at this
  have hinj : Injective (fderiv ℝ (fun y => (e.symm y : E₃)) 0) := by
    intro v w hvw
    have hv := chart_projection_fderiv heP (by norm_num) hC h0t v
    have hw := chart_projection_fderiv heP (by norm_num) hC h0t w
    rw [← hv, ← hw, hvw]
  have hhd : HasFDerivAt h (fderiv ℝ h p) (e.symm 0 : E₃) := by
    rw [hψ0]
    exact (hh3.differentiable (by norm_num) p).hasFDerivAt
  have hgd : fderiv ℝ (chartPullback e h p) 0 = 0 := by
    have hd : HasFDerivAt (chartPullback e h p)
        ((fderiv ℝ h p).comp (fderiv ℝ (fun y => (e.symm y : E₃)) 0)) 0 :=
      (hhd.comp 0 hψd.hasFDerivAt).sub_const (h p)
    rw [hd.fderiv]
    ext v
    simp [hcrit.2 _ (htan v)]
  have hdiag : ∀ v, fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v v =
      surfaceHessian n h p (fderiv ℝ (fun y => (e.symm y : E₃)) 0 v)
        (fderiv ℝ (fun y => (e.symm y : E₃)) 0 v) := by
    intro v
    let γ : ℝ → E₃ := fun t => (e.symm (t • v) : E₃)
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hγC : ContDiffAt ℝ 2 γ 0 := by
      have hl3 : ContDiffAt ℝ 3 (fun t : ℝ => t • v) 0 :=
        (contDiff_id.smul contDiff_const).contDiffAt
      have h' : ContDiffAt ℝ 3 (fun y => (e.symm y : E₃)) ((0 : ℝ) • v) := by
        simpa using hψC
      have h3 : ContDiffAt ℝ 3 ((fun y => (e.symm y : E₃)) ∘ (fun t : ℝ => t • v)) 0 :=
        ContDiffAt.comp 0 h' hl3
      exact h3.of_le (by norm_num)
    have hγ0 : γ 0 = p := by simp [γ, hψ0]
    have hA := hasDerivAt_deriv_comp_eq_surfaceHessian hS hn
      (hh3.of_le (by norm_num)).contDiffAt hcrit hγC hγ0
      (Eventually.of_forall fun t => (e.symm (t • v)).2)
    have hB := hasDerivAt_deriv_comp_line (hgC.of_le (by norm_num)) v
    have hfun : deriv (fun t : ℝ => chartPullback e h p (t • v)) = deriv (h ∘ γ) := by
      funext t
      exact deriv_sub_const (h p)
    have hγd : deriv γ 0 = fderiv ℝ (fun y => (e.symm y : E₃)) 0 v := by
      have h' : HasFDerivAt (fun y => (e.symm y : E₃))
          (fderiv ℝ (fun y => (e.symm y : E₃)) 0) ((0 : ℝ) • v) := by
        simpa using hψd.hasFDerivAt
      exact (h'.comp_hasDerivAt (0 : ℝ) hl).deriv
    rw [hfun] at hB
    rw [hB.unique hA, hγd]
  have hdim : Module.finrank ℝ E2 = Module.finrank ℝ (tangentPlane S p) := by
    rw [finrank_euclideanSpace_fin, hS.finrank_tangentPlane hcrit.1]
  let L₀ : E2 →ₗ[ℝ] tangentPlane S p :=
    ((fderiv ℝ (fun y => (e.symm y : E₃)) 0 : E2 →L[ℝ] E₃) : E2 →ₗ[ℝ] E₃).codRestrict
      (tangentPlane S p) htan
  have hL₀ : Injective L₀ := by
    intro v w hvw
    exact hinj (congrArg Subtype.val hvw)
  let L : E2 ≃ₗ[ℝ] tangentPlane S p := LinearMap.linearEquivOfInjective L₀ hL₀ hdim
  have hLv : ∀ v, ((L v : tangentPlane S p) : E₃) = fderiv ℝ (fun y => (e.symm y : E₃)) 0 v :=
    fun v => rfl
  have hsymg : ∀ v w, fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w =
      fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 w v :=
    fun v w => (hgC.isSymmSndFDerivAt (by norm_num)) v w
  have hsymH : ∀ X ∈ tangentPlane S p, ∀ Y ∈ tangentPlane S p,
      surfaceHessian n h p X Y = surfaceHessian n h p Y X := by
    intro X hX Y hY
    simp only [surfaceHessian]
    rw [(hh.contDiffAt.isSymmSndFDerivAt (by simp)) X Y,
      secondFundamentalForm_symm hS hn hcrit.1 hX hY]
  have hform : (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) =
      fun v w => tangentHessian S n h p (L v) (L w) := by
    funext v w
    simp only [tangentHessian, hLv]
    have h1 := hdiag (v + w)
    simp only [map_add, add_apply] at h1
    rw [surfaceHessian_add_add', hdiag v, hdiag w] at h1
    have h2 := hsymg v w
    have h3 := hsymH _ (htan v) _ (htan w)
    linarith
  refine ⟨hg0, hgd, ?_, ?_⟩
  · rw [hform]
    exact isNondegenerateForm_comp_linearEquiv L (tangentHessian S n h p)
  · rw [hform]
    exact formIndex_comp_linearEquiv L (tangentHessian S n h p)

end LiquidDrop
