import NoCompromise.Flow.FlowLocalCk

/-!
# Flow boxes of class `C^k`

Flow boxes for `1 ≤ k ≤ ∞`, with a product source, the vector-field identity,
and integral curves staying in the original open domain.
-/

open Set Filter
open scoped NNReal Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {X : E → E} {L : ℝ≥0} {M : ℝ}

/-- A `C^k` flow box on any linear complement of the nonzero flow direction,
including `k = ∞`. -/
theorem exists_contDiff_flowBox_of_le [FiniteDimensional ℝ E]
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) {k : ℕ∞} (hk : 1 ≤ k) (hXk : ContDiff ℝ k X)
    (p : E) (hp : X p ≠ 0) (H : Submodule ℝ E) (hH : IsCompl H (ℝ ∙ X p)) :
    ∃ e : OpenPartialHomeomorph (H × ℝ) E,
      ((0 : H), (0 : ℝ)) ∈ e.source ∧
      ⇑e = (fun q : H × ℝ => globalFlow X hX hM q.2 (p + (q.1 : E))) ∧
      ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target ∧
      ∀ q ∈ e.source, HasDerivAt
        (fun s => globalFlow X hX hM s (p + (q.1 : E)))
        (X (globalFlow X hX hM q.2 (p + (q.1 : E)))) q.2 := by
  have hk' : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  have hX1 : ContDiff ℝ 1 X := hXk.of_le hk'
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hk')
  let Ψ : H × ℝ → E := fun q => globalFlow X hX hM q.2 (p + (q.1 : E))
  let B : (H × ℝ) ≃L[ℝ] E :=
    (((LinearEquiv.refl ℝ H).prodCongr
      (LinearEquiv.toSpanNonzeroSingleton ℝ E (X p) hp)).trans
        (H.prodEquivOfIsCompl (ℝ ∙ X p) hH)).toContinuousLinearEquiv
  have hB (q : H × ℝ) : B q = (q.1 : E) + q.2 • X p := rfl
  have hΨ : ContDiff ℝ k Ψ :=
    (contDiff_globalFlow_uncurry hX hM hk hXk).comp
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
  let e := hΨ.contDiffAt.toOpenPartialHomeomorph Ψ hd hk0
  have h0 : ((0 : H), (0 : ℝ)) ∈ e.source :=
    hΨ.contDiffAt.mem_toOpenPartialHomeomorph_source hd hk0
  let W : Set (H × ℝ) := (fderiv ℝ Ψ) ⁻¹'
    Set.range (fun A : (H × ℝ) ≃L[ℝ] E => (A : (H × ℝ) →L[ℝ] E))
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage
    ((contDiff_one_iff_fderiv.mp (hΨ.of_le hk')).2)
  have h0W : ((0 : H), (0 : ℝ)) ∈ W := ⟨B, hd.fderiv.symm⟩
  let f := e.restrOpen W hW
  refine ⟨f, ⟨h0, h0W⟩, rfl, hΨ.contDiffOn, ?_, ?_⟩
  · intro y hy
    obtain ⟨A, hA⟩ := (f.map_target hy).2
    have hdA : HasFDerivAt f (A : (H × ℝ) →L[ℝ] E) (f.symm y) := by
      change (A : (H × ℝ) →L[ℝ] E) = fderiv ℝ Ψ (f.symm y) at hA
      rw [hA]
      exact ((hΨ.of_le hk').differentiable one_ne_zero _).hasFDerivAt
    exact (f.contDiffAt_symm hy hdA hΨ.contDiffAt).contDiffWithinAt
  · intro q _
    exact hasDerivAt_globalFlow hX hM (p + (q.1 : E)) q.2

/-- `thm:flow-box` on an open domain: a product chart of class `C^k`, with
`X = ∂/∂t` and integral curves staying in the domain for the whole time segment. -/
theorem exists_contDiff_flowBox_local [FiniteDimensional ℝ E]
    {k : ℕ∞} (hk : 1 ≤ k) {U : Set E} (hU : IsOpen U)
    (hXk : ContDiffOn ℝ k X U) (p : E) (hpU : p ∈ U) (hp : X p ≠ 0)
    (H : Submodule ℝ E) (hH : IsCompl H (ℝ ∙ X p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧
      ∃ e : OpenPartialHomeomorph (H × ℝ) E,
        e.source = Metric.ball (0 : H) r ×ˢ Ioo (-ε) ε ∧
        e (0, 0) = p ∧ e.target ⊆ U ∧
        ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target ∧
        (∀ q ∈ e.source, HasDerivAt (fun s => e (q.1, s)) (X (e q)) q.2) ∧
        (∀ q ∈ e.source, ∃ γ : ℝ → E,
          γ 0 = p + (q.1 : E) ∧ γ q.2 = e q ∧
          ∀ t ∈ uIcc 0 q.2, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t) := by
  have hk' : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  obtain ⟨Y, hY, hYc, V, hV, hpV, hVU, hYX⟩ :=
    exists_compactSupport_eq_near_contDiff hU hXk (isCompact_singleton (x := p))
      (singleton_subset_iff.mpr hpU)
  have hpV' : p ∈ V := hpV (mem_singleton p)
  have hYp : Y p = X p := hYX hpV'
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport (hY.of_le hk') hYc
  obtain ⟨e, h0, he, hce, hci, _⟩ := exists_contDiff_flowBox_of_le hL hM hk hY p
    (by simpa only [hYp] using hp) H (by simpa only [hYp] using hH)
  have he0 : e (0, 0) = p := by simp [he]
  let eV := (e.symm.restrOpen V hV).symm
  have h0V : ((0 : H), (0 : ℝ)) ∈ eV.source := ⟨h0, by change e (0, 0) ∈ V; rwa [he0]⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (eV.open_source.mem_nhds h0V)
  have hprod : Metric.ball (0 : H) r ×ˢ Ioo (-r) r ⊆ eV.source := by
    convert hsub using 1
    ext q
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff, mem_prod, mem_Ioo]
    simp [abs_lt]
  let f := eV.restrOpen (Metric.ball (0 : H) r ×ˢ Ioo (-r) r)
    (Metric.isOpen_ball.prod isOpen_Ioo)
  have hfs : f.source = Metric.ball (0 : H) r ×ˢ Ioo (-r) r :=
    inter_eq_right.mpr hprod
  have hf (q : H × ℝ) : f q = globalFlow Y hL hM q.2 (p + (q.1 : E)) :=
    congrFun he q
  have hfV {q : H × ℝ} (hq : q ∈ f.source) : f q ∈ V := (f.map_source hq).1.2
  refine ⟨r, hr, r, hr, f, hfs, he0, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hVU hy.1.2
  · exact hce.mono (fun q hq => hq.1.1)
  · exact hci.mono (fun y hy => hy.1.1)
  · intro q hq
    rw [← hYX (hfV hq)]
    simpa only [hf] using hasDerivAt_globalFlow hL hM (p + (q.1 : E)) q.2
  · intro q hq
    refine ⟨fun t => globalFlow Y hL hM t (p + (q.1 : E)),
      globalFlow_zero hL hM _, (hf q).symm, ?_⟩
    intro t ht
    have hqt : (q.1, t) ∈ f.source := by
      rw [hfs] at hq ⊢
      exact ⟨hq.1, ordConnected_Ioo.uIcc_subset ⟨by linarith, hr⟩ hq.2 ht⟩
    have htV : globalFlow Y hL hM t (p + (q.1 : E)) ∈ V := by
      simpa only [hf] using hfV hqt
    exact ⟨hVU htV, by
      rw [← hYX htV]
      exact hasDerivAt_globalFlow hL hM (p + (q.1 : E)) t⟩

/-- Smooth specialization of the local flow-box theorem. -/
theorem exists_smooth_flowBox_local [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hXs : ContDiffOn ℝ (⊤ : ℕ∞) X U)
    (p : E) (hpU : p ∈ U) (hp : X p ≠ 0)
    (H : Submodule ℝ E) (hH : IsCompl H (ℝ ∙ X p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧
      ∃ e : OpenPartialHomeomorph (H × ℝ) E,
        e.source = Metric.ball (0 : H) r ×ˢ Ioo (-ε) ε ∧
        e (0, 0) = p ∧ e.target ⊆ U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
        (∀ q ∈ e.source, HasDerivAt (fun s => e (q.1, s)) (X (e q)) q.2) ∧
        (∀ q ∈ e.source, ∃ γ : ℝ → E,
          γ 0 = p + (q.1 : E) ∧ γ q.2 = e q ∧
          ∀ t ∈ uIcc 0 q.2, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t) :=
  exists_contDiff_flowBox_local le_top hU hXs p hpU hp H hH

end LiquidDrop
