import NoCompromise.Surface.Morse

/-!
# Local arcs of regular levels

Part of `lem:merge-disjoint` (chapter 14): `h` is constant along integral curves of the rotated
tangential gradient `levelTangentField`, and near a regular point the level set of `h` on the
surface is covered by the integral curve through that point on any short time interval.
-/

noncomputable section
open Set Function InnerProductSpace Filter
open scoped Topology Gradient
namespace LiquidDrop

/-- `h` is constant along an integral curve of `levelTangentField` (lem:one-manifold, last
clause). -/
theorem height_levelTangentField_curve {n : E₃ → E₃} {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {γ : ℝ → E₃} (hγ : ∀ t, HasDerivAt γ (levelTangentField n h (γ t)) t) (t : ℝ) :
    h (γ t) = h (γ 0) := by
  have hd : ∀ s, HasDerivAt (fun u => h (γ u)) 0 s := fun s => by
    have := ((hh.differentiable one_ne_zero (γ s)).hasFDerivAt).comp_hasDerivAt s (hγ s)
    rwa [fderiv_levelTangentField_eq_zero] at this
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

/-- A vector orthogonal to three nonzero pairwise orthogonal vectors of `E₃` vanishes. -/
private lemma eq_zero_of_orthogonal_three {a b c w : E₃} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (hwa : inner ℝ w a = 0) (hwb : inner ℝ w b = 0) (hwc : inner ℝ w c = 0) : w = 0 := by
  let f : Fin 3 → E₃ := ![a, b, c]
  have hli : LinearIndependent ℝ f := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i; fin_cases i <;> simpa [f]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f, real_inner_comm]
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker (innerSL ℝ w).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simpa [f]
  have hw : w ∈ LinearMap.ker (innerSL ℝ w).toLinearMap := hle (hspan ▸ Submodule.mem_top)
  simpa using hw

/-- Local arc lemma: near a regular point `q` of `h` on `S`, the level set `S ∩ {h = h q}` is
covered by the integral curve of `levelTangentField` through `q` on any short time interval. -/
theorem levelSet_subset_integralCurve {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {q : E₃}
    (hq : q ∈ S) (hreg : ¬ IsSurfaceCriticalPoint S h q) {γ : ℝ → E₃} (hγ0 : γ 0 = q)
    (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E₃, IsOpen V ∧ q ∈ V ∧ ∀ y ∈ V ∩ S, h y = h q → ∃ t ∈ Set.Ioo (-ε) ε, γ t = y := by
  obtain ⟨U, φ, hU, hqU, hφ, hzero, hreg'⟩ := hS q hq
  set g := surfaceGradient n h q with hg
  have hg0 : g ≠ 0 := fun h0 =>
    hreg ((isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hq).mpr h0)
  set v := levelTangentField n h q with hv
  have hν : ‖n q‖ = 1 := (hn.2 q hq).1
  have hn0 : n q ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hν
    exact zero_ne_one hν
  have hv0 : v ≠ 0 := by
    rw [← norm_ne_zero_iff, hv, norm_levelTangentField hn hq]
    exact norm_ne_zero_iff.mpr hg0
  have hng : inner ℝ (n q) g = 0 := by
    simp only [hg, surfaceGradient, tangentialProj, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hν]
    ring
  have hnv : inner ℝ (n q) v = 0 := inner_left_cross3 _ _
  have hgv : inner ℝ g v = 0 := inner_right_cross3 _ _
  -- the local chart `F = (φ, h, ⟪v, ·⟫)`
  let τ : E₃ →L[ℝ] ℝ := innerSL ℝ v
  let F : E₃ → ℝ × ℝ × ℝ := fun x => (φ x, h x, τ x)
  let D : E₃ →L[ℝ] ℝ × ℝ × ℝ := (fderiv ℝ φ q).prod ((fderiv ℝ h q).prod τ)
  have hFD : HasStrictFDerivAt F D q :=
    (hφ.contDiffAt.hasStrictFDerivAt (by simp)).prodMk
      ((hh.contDiffAt.hasStrictFDerivAt (by simp)).prodMk τ.hasStrictFDerivAt)
  have hDinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : fderiv ℝ φ q w = 0 := congrArg Prod.fst hw
    have h2 : fderiv ℝ h q w = 0 := congrArg (fun p => p.2.1) hw
    have h3 : inner ℝ v w = 0 := congrArg (fun p => p.2.2) hw
    have hT := tangentPlane_eq hU hqU (hφ.contDiffAt.of_le (by simp)) hzero hq
      (hreg' q ⟨hq, hqU⟩)
    have hwT : w ∈ tangentPlane S q := by
      rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
      exact h1
    have hnw : inner ℝ (n q) w = 0 := (hn.2 q hq).2 w hwT
    have hsplit : gradient h q = g + inner ℝ (n q) (gradient h q) • n q := by
      simp only [hg, surfaceGradient, tangentialProj]
      abel
    have hgw : inner ℝ g w = 0 := by
      rw [← inner_gradient_left, hsplit, inner_add_left, real_inner_smul_left, hnw,
        mul_zero, add_zero] at h2
      exact h2
    exact eq_zero_of_orthogonal_three hn0 hg0 hv0 hng hnv hgv
      (by rw [real_inner_comm]; exact hnw) (by rw [real_inner_comm]; exact hgw)
      (by rw [real_inner_comm]; exact h3)
  have hDsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D.toLinearMap)
      (by simp)).mp hDinj
  let De : E₃ ≃L[ℝ] ℝ × ℝ × ℝ :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hDinj, hDsurj⟩).toContinuousLinearEquiv
  have hFD' : HasStrictFDerivAt F (De : E₃ →L[ℝ] ℝ × ℝ × ℝ) q := by
    convert hFD using 1
    exact ContinuousLinearMap.ext fun w => rfl
  let P := hFD'.toOpenPartialHomeomorph F
  set W := P.source ∩ U with hW
  have hWo : IsOpen W := P.open_source.inter hU
  have hqW : q ∈ W := ⟨hFD'.mem_toOpenPartialHomeomorph_source, hqU⟩
  have hFinj : InjOn F W := P.injOn.mono inter_subset_left
  -- the height function `τ ∘ γ` along the curve
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).2.continuousAt
  let f : ℝ → ℝ := fun t => τ (γ t)
  have hfd : HasDerivAt f (τ v) 0 := by
    have := τ.hasFDerivAt.comp_hasDerivAt 0 (hγ 0).2
    rw [hγ0, ← hv] at this
    exact this
  have hτv : 0 < τ v := by
    have : τ v = inner ℝ v v := rfl
    rw [this, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hv0) 2
  have hslope : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope f 0 t :=
    (hasDerivAt_iff_tendsto_slope.mp hfd).eventually (lt_mem_nhds hτv)
  have hW' : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W :=
    hγc.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hWo.mem_nhds hqW)
  obtain ⟨δ1, hδ1, hball⟩ := Metric.eventually_nhds_iff.mp
    ((eventually_nhdsWithin_iff.mp hslope).and hW')
  set δ := min (δ1 / 2) (ε / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1' : δ < δ1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmem : ∀ t, |t| < δ1 → dist t 0 < δ1 := fun t ht => by simpa [Real.dist_eq] using ht
  have hfδ : f 0 < f δ := by
    have hs := (hball (hmem δ (by rw [abs_of_pos hδ]; exact hδ1'))).1 (ne_of_gt hδ)
    rw [slope_def_field, sub_zero] at hs
    have := (div_pos_iff_of_pos_right hδ).mp hs
    linarith
  have hfmδ : f (-δ) < f 0 := by
    have hs := (hball (hmem (-δ) (by rw [abs_neg, abs_of_pos hδ]; exact hδ1'))).1
      (by simp only [mem_compl_iff, mem_singleton_iff, neg_eq_zero]; exact ne_of_gt hδ)
    rw [slope_def_field, sub_zero] at hs
    have hmul : (f (-δ) - f 0) / -δ * -δ = f (-δ) - f 0 :=
      div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_gt hδ))
    nlinarith
  have hf0 : f 0 = τ q := by simp only [f, hγ0]
  refine ⟨W ∩ τ ⁻¹' Ioo (f (-δ)) (f δ), hWo.inter (isOpen_Ioo.preimage τ.continuous),
    ⟨hqW, ?_⟩, ?_⟩
  · change τ q ∈ Ioo (f (-δ)) (f δ)
    rw [← hf0]
    exact ⟨hfmδ, hfδ⟩
  · rintro y ⟨⟨hyW, hyτ⟩, hyS⟩ hyh
    have hfc : ContinuousOn f (Icc (-δ) δ) := (τ.continuous.comp hγc).continuousOn
    obtain ⟨t, ht, hft⟩ : τ y ∈ f '' Icc (-δ) δ :=
      intermediate_value_Icc (by linarith) hfc ⟨hyτ.1.le, hyτ.2.le⟩
    have htIoo : t ∈ Ioo (-δ) δ := by
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · rintro rfl
        exact (lt_irrefl _ (hft ▸ hyτ.1))
      · rintro rfl
        exact (lt_irrefl _ (hft ▸ hyτ.2))
    have hγtW : γ t ∈ W := (hball (hmem t (abs_lt.mpr ⟨by linarith [htIoo.1],
      by linarith [htIoo.2]⟩))).2
    refine ⟨t, ⟨by linarith [htIoo.1], by linarith [htIoo.2]⟩, hFinj hγtW hyW ?_⟩
    have hφt : φ (γ t) = 0 := by
      have : γ t ∈ S ∩ U := ⟨(hγ t).1, hγtW.2⟩
      rw [hzero] at this
      exact this.2
    have hφy : φ y = 0 := by
      have : y ∈ S ∩ U := ⟨hyS, hyW.2⟩
      rw [hzero] at this
      exact this.2
    have hht : h (γ t) = h y := by
      rw [height_levelTangentField_curve (hh.of_le (by simp)) (fun s => (hγ s).2) t, hγ0, hyh]
    change (φ (γ t), h (γ t), τ (γ t)) = (φ y, h y, τ y)
    rw [hφt, hφy, hht]
    exact congrArg (fun r => ((0 : ℝ), h y, r)) hft

end LiquidDrop
