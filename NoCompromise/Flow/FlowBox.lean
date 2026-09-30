module

public import NoCompromise.Flow.FlowCk
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Joint C¹ regularity and C¹ flow boxes

The field is C¹, globally Lipschitz, and bounded on a real Banach space. Joint
differentiability follows from joint continuity of its spatial derivative and the
time derivative of the flow. In finite dimension, any linear complement of the
nonzero flow direction gives a C¹ flow box.

The final section proves `cor:flow-manifold` for open subsets of a
finite-dimensional real normed space at the C¹ level (C¹ pending the user's
wording decision on C¹ versus smooth): localization, uniqueness, uniform local
existence on compact sets, and continuation of curves confined to compact sets.
Joint C¹ regularity and flow boxes follow by applying
`contDiff_one_globalFlow_uncurry` and `exists_contDiff_flowBox` to the localized
field. This does not assert the abstract-manifold or higher-regularity versions.
-/

open Set Filter Asymptotics
open scoped NNReal Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {X : E → E} {L : ℝ≥0} {M : ℝ}

/-- The joint derivative of the global flow in time and initial position. -/
theorem hasFDerivAt_globalFlow_uncurry
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M)
    (hX1 : ContDiff ℝ 1 X) (q : ℝ × E) :
    HasFDerivAt (fun q : ℝ × E => globalFlow X hX hM q.1 q.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (X (globalFlow X hX hM q.1 q.2)) +
       (variationalMatrix X hX hM hX1 q.1 q.2).comp
         (ContinuousLinearMap.snd ℝ ℝ E)) q := by
  let Φ := globalFlow X hX hM
  let A := variationalMatrix X hX hM hX1
  have hs : (fun z : ℝ × E =>
      Φ (q.1 + z.1) (q.2 + z.2) - Φ (q.1 + z.1) q.2 - A q.1 q.2 z.2)
      =o[𝓝 0] (fun z => z) := by
    rw [isLittleO_iff]
    intro c hc
    obtain ⟨δ, hδ, hδA⟩ := Metric.continuousAt_iff.mp
      ((continuous_variationalMatrix hX hM hX1).continuousAt (x := q)) c hc
    have hz : ∀ᶠ z : ℝ × E in 𝓝 0, ‖z‖ < δ := by
      simpa using (continuous_norm.tendsto (0 : ℝ × E)).eventually
        (gt_mem_nhds (by simpa using hδ))
    filter_upwards [hz] with z hz
    have hbound : ∀ y ∈ Metric.ball q.2 δ,
        ‖fderiv ℝ (Φ (q.1 + z.1)) y - A q.1 q.2‖ ≤ c := by
      intro y hy
      rw [(hasFDerivAt_globalFlow hX hM hX1 (q.1 + z.1) y).fderiv]
      apply le_of_lt
      rw [← dist_eq_norm]
      apply hδA (x := (q.1 + z.1, y))
      rw [Prod.dist_eq]
      exact max_lt (by simpa [dist_eq_norm] using (norm_fst_le z).trans_lt hz) hy
    have h := (convex_ball q.2 δ).norm_image_sub_le_of_norm_fderiv_le'
      (f := Φ (q.1 + z.1)) (φ := A q.1 q.2) (C := c)
      (x := q.2) (y := q.2 + z.2)
      (fun y _ => (hasFDerivAt_globalFlow hX hM hX1 (q.1 + z.1) y).differentiableAt)
      hbound (Metric.mem_ball_self hδ)
      (by simpa [Metric.mem_ball, dist_eq_norm] using (norm_snd_le z).trans_lt hz)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left (norm_snd_le z) hc.le)
  have ht := hasFDerivAt_iff_isLittleO_nhds_zero.mp
    (hasDerivAt_globalFlow hX hM q.2 q.1).hasFDerivAt
  have ht' : (fun z : ℝ × E => Φ (q.1 + z.1) q.2 - Φ q.1 q.2 -
      z.1 • X (Φ q.1 q.2)) =o[𝓝 0] (fun z => z) := by
    simpa [Function.comp_def, Φ] using!
      (ht.comp_tendsto (continuous_fst.tendsto (0 : ℝ × E))).trans_isBigO
      ((ContinuousLinearMap.fst ℝ ℝ E).isBigO_id (𝓝 0))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  convert! hs.add ht' using 1
  ext z
  change Φ (q.1 + z.1) (q.2 + z.2) - Φ q.1 q.2 -
      (z.1 • X (Φ q.1 q.2) + A q.1 q.2 z.2) = _
  abel

/-- The global flow is jointly C¹ in time and initial position. -/
theorem contDiff_one_globalFlow_uncurry
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) :
    ContDiff ℝ 1 (fun q : ℝ × E => globalFlow X hX hM q.1 q.2) := by
  have hd := hasFDerivAt_globalFlow_uncurry hX hM hX1
  have hf : Continuous (fun q : ℝ × E => globalFlow X hX hM q.1 q.2) :=
    continuous_iff_continuousAt.mpr fun q => (hd q).continuousAt
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun q => (hd q).differentiableAt, ?_⟩
  have heq := funext fun q => (hd q).fderiv
  rw [heq]
  exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × E) E
      (ContinuousLinearMap.fst ℝ ℝ E)).continuous).comp (hX.continuous.comp hf)).add
    ((continuous_variationalMatrix hX hM hX1).clm_comp continuous_const)

/-- A C¹ flow box on any linear complement of the flow direction. -/
theorem exists_contDiff_flowBox [FiniteDimensional ℝ E]
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X)
    (p : E) (hp : X p ≠ 0) (H : Submodule ℝ E) (hH : IsCompl H (ℝ ∙ X p)) :
    ∃ e : OpenPartialHomeomorph (H × ℝ) E,
      ((0 : H), (0 : ℝ)) ∈ e.source ∧
      ⇑e = (fun q : H × ℝ => globalFlow X hX hM q.2 (p + (q.1 : E))) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ q ∈ e.source, HasDerivAt
        (fun s => globalFlow X hX hM s (p + (q.1 : E)))
        (X (globalFlow X hX hM q.2 (p + (q.1 : E)))) q.2 := by
  let Ψ : H × ℝ → E := fun q => globalFlow X hX hM q.2 (p + (q.1 : E))
  let B : (H × ℝ) ≃L[ℝ] E :=
    (((LinearEquiv.refl ℝ H).prodCongr
      (LinearEquiv.toSpanNonzeroSingleton ℝ E (X p) hp)).trans
        (H.prodEquivOfIsCompl (ℝ ∙ X p) hH)).toContinuousLinearEquiv
  have hB (q : H × ℝ) : B q = (q.1 : E) + q.2 • X p := rfl
  have hΨ : ContDiff ℝ 1 Ψ :=
    (contDiff_one_globalFlow_uncurry hX hM hX1).comp
      (contDiff_snd.prodMk (contDiff_const.add (H.subtypeL.contDiff.comp contDiff_fst)))
  have hg : HasFDerivAt (fun q : H × ℝ => (q.2, p + (q.1 : E)))
      ((ContinuousLinearMap.snd ℝ H ℝ).prod
        (H.subtypeL.comp (ContinuousLinearMap.fst ℝ H ℝ))) (0, 0) :=
    hasFDerivAt_snd.prodMk
      ((H.subtypeL.hasFDerivAt.comp (0, 0) hasFDerivAt_fst).const_add p)
  have hd : HasFDerivAt Ψ (B : (H × ℝ) →L[ℝ] E) (0, 0) := by
    convert! (hasFDerivAt_globalFlow_uncurry hX hM hX1
      (0, p + ((0 : H) : E))).comp (0, 0) hg using 1
    apply ContinuousLinearMap.ext
    intro q
    change B q = q.2 • X (globalFlow X hX hM 0 (p + ((0 : H) : E))) +
      variationalMatrix X hX hM hX1 0 (p + ((0 : H) : E)) (q.1 : E)
    rw [hB]
    simp [add_comm]
  let e := hΨ.contDiffAt.toOpenPartialHomeomorph Ψ hd one_ne_zero
  have h0 : ((0 : H), (0 : ℝ)) ∈ e.source :=
    hΨ.contDiffAt.mem_toOpenPartialHomeomorph_source hd one_ne_zero
  have hi : ContDiffAt ℝ 1 e.symm (Ψ (0, 0)) :=
    hΨ.contDiffAt.to_localInverse hd one_ne_zero
  -- Restrict the target to an open neighborhood where the local inverse is C¹.
  obtain ⟨u, hu, hpu, hcu⟩ := hi.contDiffOn' le_rfl (by simp)
  have hcu' : ContDiffOn ℝ 1 e.symm u := by simpa using hcu
  refine ⟨(e.symm.restrOpen u hu).symm, ?_, rfl, ?_, ?_, ?_⟩
  · exact ⟨h0, hpu⟩
  · exact hΨ.contDiffOn
  · exact hcu'.mono inter_subset_right
  · intro q _
    exact hasDerivAt_globalFlow hX hM (p + (q.1 : E)) q.2

-- BEGIN cor:flow-manifold

section LocalFlow

variable [FiniteDimensional ℝ E] {U K : Set E}

omit [CompleteSpace E] in
/-- `cor:flow-manifold`, C¹ Euclidean version: localize a C¹ field near a compact
set in its open domain. C¹ is pending the user's wording decision on C¹ versus
smooth. The localized field admits the joint C¹ flow and flow box of
`contDiff_one_globalFlow_uncurry` and `exists_contDiff_flowBox`. -/
theorem exists_compactSupport_eq_near (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ Y : E → E, ContDiff ℝ 1 Y ∧ HasCompactSupport Y ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn Y X V := by
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨A, hAo, hKA, hAU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hWo).mem_nhdsSet.mpr (subset_inter hKU hKW))
  obtain ⟨V, hVo, hKV, hVA⟩ := hK.exists_isOpen_closure_subset (hAo.mem_nhdsSet.mpr hKA)
  obtain ⟨f, hfs, hf, hf01⟩ := hAo.exists_contDiff_support_eq (n := 1)
  obtain ⟨g, hgs, hg, hg01⟩ := isClosed_closure.isOpen_compl.exists_contDiff_support_eq
    (n := 1) (s := (closure V)ᶜ)
  have hpos (x : E) : 0 < f x + g x := by
    have hf0 := (hf01 (mem_range_self x)).1
    have hg0 := (hg01 (mem_range_self x)).1
    by_cases hx : x ∈ A
    · have hn : f x ≠ 0 := by simpa only [← hfs, Function.mem_support] using hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm hn)) hg0
    · have hn : g x ≠ 0 := by
        rw [← Function.mem_support, hgs]
        exact fun h => hx (hVA h)
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm hn))
  let ρ : E → ℝ := fun x => f x / (f x + g x)
  have hρ : ContDiff ℝ 1 ρ := hf.div (hf.add hg) (fun x => (hpos x).ne')
  have hρs : Function.support ρ ⊆ A := by
    intro x hx
    apply hfs.subset
    contrapose! hx
    simp [ρ, Function.mem_support] at *
    simp [hx]
  have hρc : HasCompactSupport ρ :=
    hWc.of_isClosed_subset isClosed_closure
      ((closure_mono hρs).trans (hAU.trans inter_subset_right |>.trans subset_closure))
  refine ⟨fun x => ρ x • X x, ?_, hρc.smul_right, V, hVo, hKV,
    (subset_closure.trans hVA).trans (subset_closure.trans (hAU.trans inter_subset_left)), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure A
    · exact hρ.contDiffAt.smul ((hX x ((hAU hx).1)).contDiffAt (hU.mem_nhds (hAU hx).1))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      have hyρ : ρ y = 0 := by
        by_contra hn
        exact hy (subset_closure (hρs hn))
      simp [hyρ]
  · intro x hx
    have hgx : g x = 0 := by
      rw [← Function.notMem_support, hgs]
      exact not_not.mpr (subset_closure hx)
    have hfx : f x ≠ 0 := by
      rw [← Function.mem_support, hfs]
      exact hVA (subset_closure hx)
    simp [ρ, hgx, hfx]

omit [CompleteSpace E] in
/-- `cor:flow-manifold` for open subsets of a finite-dimensional real space at
C¹ regularity: integral curves with one common value agree on any order-connected
time set, including open intervals. C¹ is pending the user's wording decision
on C¹ versus smooth. -/
theorem integralCurve_unique_of_contDiffOn (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    {I : Set ℝ} (hI : OrdConnected I) {γ₁ γ₂ : ℝ → E} {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h₁ : ∀ t ∈ I, γ₁ t ∈ U ∧ HasDerivAt γ₁ (X (γ₁ t)) t)
    (h₂ : ∀ t ∈ I, γ₂ t ∈ U ∧ HasDerivAt γ₂ (X (γ₂ t)) t)
    (heq : γ₁ t₀ = γ₂ t₀) : EqOn γ₁ γ₂ I := by
  intro t ht
  have hJ : uIcc t₀ t ⊆ I := hI.uIcc_subset ht₀ ht
  have hc₁ : ContinuousOn γ₁ (uIcc t₀ t) :=
    fun s hs => ((h₁ s (hJ hs)).2.continuousAt).continuousWithinAt
  have hc₂ : ContinuousOn γ₂ (uIcc t₀ t) :=
    fun s hs => ((h₂ s (hJ hs)).2.continuousAt).continuousWithinAt
  have hKU : γ₁ '' uIcc t₀ t ∪ γ₂ '' uIcc t₀ t ⊆ U := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact (h₁ s (hJ hs)).1
    · exact (h₂ s (hJ hs)).1
  obtain ⟨Y, hY, hYc, V, _, hKV, _, hYX⟩ := exists_compactSupport_eq_near hU hX
    ((isCompact_uIcc.image_of_continuousOn hc₁).union
      (isCompact_uIcc.image_of_continuousOn hc₂)) hKU
  obtain ⟨L, M, hL, _⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  have hd₁ (s : ℝ) (hs : s ∈ uIcc t₀ t) : HasDerivAt γ₁ (Y (γ₁ s)) s := by
    rw [hYX (hKV (Or.inl (mem_image_of_mem γ₁ hs)))]
    exact (h₁ s (hJ hs)).2
  have hd₂ (s : ℝ) (hs : s ∈ uIcc t₀ t) : HasDerivAt γ₂ (Y (γ₂ s)) s := by
    rw [hYX (hKV (Or.inr (mem_image_of_mem γ₂ hs)))]
    exact (h₂ s (hJ hs)).2
  rcases le_total t₀ t with htt | htt
  · rw [uIcc_of_le htt] at hc₁ hc₂ hd₁ hd₂
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => Y) (s := fun _ => univ)
      (fun _ _ => hL.lipschitzOnWith) hc₁
      (fun s hs => (hd₁ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hc₂
      (fun s hs => (hd₂ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) heq ⟨htt, le_rfl⟩
  · rw [uIcc_of_ge htt] at hc₁ hc₂ hd₁ hd₂
    exact ODE_solution_unique_of_mem_Icc_left
      (v := fun _ => Y) (s := fun _ => univ)
      (fun _ _ => hL.lipschitzOnWith) hc₁
      (fun s hs => (hd₁ s (Ioc_subset_Icc_self hs)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hc₂
      (fun s hs => (hd₂ s (Ioc_subset_Icc_self hs)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) heq ⟨le_rfl, htt⟩

omit [CompleteSpace E] in
/-- `cor:flow-manifold` for open subsets of a finite-dimensional real space at
C¹ regularity: a compact set of initial points has a common positive existence
time. C¹ is pending the user's wording decision on C¹ versus smooth. Joint C¹
regularity and flow boxes are supplied by `contDiff_one_globalFlow_uncurry` and
`exists_contDiff_flowBox` applied to the localized field. -/
theorem exists_integralCurve_local (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t := by
  obtain ⟨Y, hY, hYc, V, hVo, hKV, hVU, hYX⟩ :=
    exists_compactSupport_eq_near hU hX hK hKU
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  have hc := (contDiff_one_globalFlow_uncurry hL hM hY).continuous
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ K, globalFlow Y hL hM t x ∈ V := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hc.continuousAt.eventually (hVo.mem_nhds (by simpa using hKV hx))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨ε, hε, fun x hx => ⟨fun t => globalFlow Y hL hM t x,
    globalFlow_zero hL hM x, fun t ht => ?_⟩⟩
  have htV := he (by simpa [Real.dist_eq] using abs_lt.mpr ht) x hx
  refine ⟨hVU htV, ?_⟩
  rw [← hYX htV]
  exact hasDerivAt_globalFlow hL hM x t

omit [CompleteSpace E] in
/-- `cor:flow-manifold` for open subsets of a finite-dimensional real space at
C¹ regularity: a curve confined to a compact subset of the domain extends past
its finite right endpoint. C¹ is pending the user's wording decision on C¹
versus smooth. The extension is a trajectory of a localized C¹ field. -/
theorem integralCurve_extend_of_mem_compact (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact K) (hKU : K ⊆ U) {a b : ℝ} (hab : a < b) {γ : ℝ → E}
    (hγ : ∀ t ∈ Ico a b, γ t ∈ K ∧ HasDerivAt γ (X (γ t)) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ' : ℝ → E, EqOn γ' γ (Ico a b) ∧
      ∀ t ∈ Ioo a (b + δ), γ' t ∈ U ∧ HasDerivAt γ' (X (γ' t)) t := by
  obtain ⟨Y, hY, hYc, V, hVo, hKV, hVU, hYX⟩ :=
    exists_compactSupport_eq_near hU hX hK hKU
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  let γ' : ℝ → E := fun t => globalFlow Y hL hM (t - a) (γ a)
  have hd (t : ℝ) : HasDerivAt γ' (Y (γ' t)) t :=
    HasDerivAt.comp_sub_const t a (hasDerivAt_globalFlow hL hM (γ a) (t - a))
  have hc : Continuous γ' := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have heq : EqOn γ' γ (Ico a b) := by
    apply integralCurve_unique_of_contDiffOn isOpen_univ hY.contDiffOn ordConnected_Ico
      (t₀ := a) ⟨le_rfl, hab⟩
    · exact fun t _ => ⟨mem_univ _, hd t⟩
    · intro t ht
      refine ⟨mem_univ _, ?_⟩
      rw [hYX (hKV (hγ t ht).1)]
      exact (hγ t ht).2
    · simp [γ']
  have hmaps : MapsTo γ' (Ico a b) K := by
    intro t ht
    rw [heq ht]
    exact (hγ t ht).1
  have hbK : γ' b ∈ K := by
    apply hmaps.closure_left hc hK.isClosed
    rw [closure_Ico hab.ne]
    exact ⟨hab.le, le_rfl⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff.mp
    (hc.continuousAt.eventually (hVo.mem_nhds (hKV hbK)))
  refine ⟨δ, hδ, γ', heq, fun t ht => ?_⟩
  have htV : γ' t ∈ V := by
    by_cases htb : t < b
    · exact hKV (hmaps ⟨ht.1.le, htb⟩)
    · apply hδV
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt htb))]
      linarith [ht.2]
  refine ⟨hVU htV, ?_⟩
  rw [← hYX htV]
  exact hd t

omit [CompleteSpace E] in
/-- `cor:flow-manifold` for open subsets of a finite-dimensional real space at
C¹ regularity: a curve confined to a compact subset extends past its finite
left endpoint. C¹ is pending the user's wording decision on C¹ versus smooth.
This is the time reversal of `integralCurve_extend_of_mem_compact`. -/
theorem integralCurve_extend_backward_of_mem_compact
    (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) (hK : IsCompact K) (hKU : K ⊆ U)
    {a b : ℝ} (hab : a < b) {γ : ℝ → E}
    (hγ : ∀ t ∈ Ioc a b, γ t ∈ K ∧ HasDerivAt γ (X (γ t)) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ' : ℝ → E, EqOn γ' γ (Ioc a b) ∧
      ∀ t ∈ Ioo (a - δ) b, γ' t ∈ U ∧ HasDerivAt γ' (X (γ' t)) t := by
  have hr : ∀ t ∈ Ico (-b) (-a), γ (-t) ∈ K ∧
      HasDerivAt (fun s => γ (-s)) ((-X) (γ (-t))) t := by
    intro t ht
    have ht' : -t ∈ Ioc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨(hγ (-t) ht').1, ?_⟩
    simpa only [zero_sub, Pi.neg_apply] using HasDerivAt.comp_const_sub (0 : ℝ) t
      (by simpa using (hγ (-t) ht').2)
  obtain ⟨δ, hδ, η, heq, hη⟩ := integralCurve_extend_of_mem_compact hU hX.neg hK hKU
    (neg_lt_neg hab) hr
  refine ⟨δ, hδ, fun t => η (-t), ?_, ?_⟩
  · intro t ht
    have ht' : -t ∈ Ico (-b) (-a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa using heq ht'
  · intro t ht
    have ht' : -t ∈ Ioo (-b) (-a + δ) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨(hη (-t) ht').1, ?_⟩
    have hd : HasDerivAt η (-(X (η (-t)))) (-t) := (hη (-t) ht').2
    have hd' := HasDerivAt.comp_const_sub (f' := -(X (η (-t)))) (0 : ℝ) t
      (by simpa only [zero_sub] using hd)
    simpa only [zero_sub, neg_neg] using hd'

end LocalFlow

-- END cor:flow-manifold

end LiquidDrop
