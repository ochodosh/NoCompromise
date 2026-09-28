import NoCompromise.Stationary.BootstrapGlobal

/-!
# Chart data for `prop:bootstrap-C3`

Blueprint `prop:bootstrap-C3`: in a boundary chart whose height is `C²`, the forcing term
`λ - v_Ω` of the graph equation is `C^{1,a}` (from `lem:potential-C1beta`), and the weak
graph equation rescales from any disk to the unit disk.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `prop:bootstrap-C3`: rigid placements are `C^k` for every `k`. -/
lemma contDiff_rigidPlacement_all (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {k : WithTop ℕ∞} :
    ContDiff ℝ k a := by
  have heq : (a : AmbientSpace → AmbientSpace) =
      fun x => a.linearIsometryEquiv x + a 0 := by
    funext x
    simpa using a.map_vadd (0 : AmbientSpace) x
  rw [heq]
  exact a.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const

/-- Blueprint `prop:bootstrap-C3`: a globally Hölder map with values bounded on a set has a
finite Hölder norm there. -/
lemma bootstrap_holder_of_global {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {a C M : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hM : 0 ≤ M) {f : E → F} {U : Set E}
    (hH : ∀ x z : E, ‖f x - f z‖ ≤ C * ‖x - z‖ ^ a) (hb : ∀ x ∈ U, ‖f x‖ ≤ M) :
    HasFiniteHolderNormOn a f U := by
  apply HasFiniteHolderNormOn.of_bounds hM hC hb
  intro x _ y _
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, norm_zero, Real.zero_rpow ha.ne', div_zero]
    exact hC
  · have hpos : 0 < ‖x - y‖ ^ a :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) a
    exact (div_le_iff₀ hpos).mpr (hH x y)

/-- Blueprint `prop:bootstrap-C3`: in a boundary chart whose height is `C²` on a disk, the
forcing term `λ - v_Ω` of the graph equation, read through the chart, is `C^{1,a}` on the
concentric half disk (`lem:potential-C1beta`). -/
theorem chart_forcing_c1Holder {Ω : Set AmbientSpace} (hΩ : Bornology.IsBounded Ω)
    (lam : ℝ) (c : C1BoundaryChart) {y1 : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ 2 c.height (ball y1 ρ)) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    HasC1HolderOn a
      (fun y => lam - (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal)
      (ball y1 (ρ / 2)) := by
  set v : AmbientSpace → ℝ := fun x => (coulombPotential Ω x).toReal with hvdef
  set Ψ : EuclideanSpace ℝ (Fin 2) → AmbientSpace :=
    fun y => c.placement (graphMapN c.height y) with hΨdef
  obtain ⟨hv, C, hC, hH⟩ := coulombPotential_contDiff_one_and_holder ha ha1 hΩ
  have hΨ2 : ContDiffOn ℝ 2 Ψ (ball y1 ρ) :=
    (contDiff_rigidPlacement_all c.placement).comp_contDiffOn
      ((graphBaseN 2).contDiff.contDiffOn.add (hf.smul contDiffOn_const))
  have hsub : closedBall y1 (ρ / 2) ⊆ ball y1 ρ := closedBall_subset_ball (by linarith)
  have hΨ1 : ContDiff ℝ 1 Ψ :=
    (contDiff_rigidPlacement c.placement).comp
      ((graphBaseN 2).contDiff.add (c.height_contDiff.smul contDiff_const))
  have hG1 : ContDiff ℝ 1 (fun y => lam - v (Ψ y)) := contDiff_const.sub (hv.comp hΨ1)
  have h0 := bootstrap_holder_of_contDiffOn_closedBall ha ha1 y1 (ρ / 2) hG1.contDiffOn
  -- the derivative formula
  have hd : ∀ y ∈ ball y1 (ρ / 2), fderiv ℝ (fun y => lam - v (Ψ y)) y =
      -((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) AmbientSpace ℝ)
        (fderiv ℝ v (Ψ y)) (fderiv ℝ Ψ y)) := by
    intro y _
    have hΨd : DifferentiableAt ℝ Ψ y := (hΨ1.differentiable one_ne_zero) y
    have hvd : DifferentiableAt ℝ v (Ψ y) := (hv.differentiable one_ne_zero) _
    rw [fderiv_const_sub, fderiv_fun_comp y hvd hΨd]
    rfl
  -- Hölder continuity of `Dv ∘ Ψ`
  have hK : IsCompact (Ψ '' closedBall y1 (ρ / 2)) :=
    (isCompact_closedBall y1 (ρ / 2)).image_of_continuousOn
      (hΨ2.continuousOn.mono hsub)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hv.continuous_fderiv one_ne_zero).continuousOn
  have hHd : ∀ x z : AmbientSpace, ‖fderiv ℝ v x - fderiv ℝ v z‖ ≤ C * ‖x - z‖ ^ a := by
    intro x z
    have hx : fderiv ℝ v x = toDual ℝ AmbientSpace (gradient v x) := by
      simp [gradient]
    have hz : fderiv ℝ v z = toDual ℝ AmbientSpace (gradient v z) := by
      simp [gradient]
    rw [hx, hz, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hH x z
  have hvK : HasFiniteHolderNormOn a (fderiv ℝ v) (Ψ '' closedBall y1 (ρ / 2)) :=
    bootstrap_holder_of_global ha hC (le_max_left 0 M) hHd
      (fun x hx => (hM x hx).trans (le_max_right _ _))
  obtain ⟨L, hL⟩ := ((hΨ2.of_le (by norm_num)).mono hsub).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall y1 (ρ / 2)) (isCompact_closedBall y1 (ρ / 2))
  have hlip : ∀ x ∈ ball y1 (ρ / 2), ∀ y ∈ ball y1 (ρ / 2),
      ‖Ψ x - Ψ y‖ ≤ max 1 (L : ℝ) * ‖x - y‖ := by
    intro x hx y hy
    have := hL.dist_le_mul x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have h1 : HasFiniteHolderNormOn a (fun y => fderiv ℝ v (Ψ y)) (ball y1 (ρ / 2)) :=
    (nondiv_holder_comp_expansion ha.le ha1.le (le_max_left 1 (L : ℝ)) hvK
      (fun y hy => mem_image_of_mem Ψ (ball_subset_closedBall hy)) hlip).1
  -- Hölder continuity of `DΨ`
  have hDΨ : ContDiffOn ℝ 1 (fderiv ℝ Ψ) (ball y1 ρ) :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp hΨ2).2.2
  have h2 : HasFiniteHolderNormOn a (fderiv ℝ Ψ) (ball y1 (ρ / 2)) :=
    bootstrap_holder_of_contDiffOn_closedBall ha ha1 y1 (ρ / 2) (hDΨ.mono hsub)
  have h12 := (nondiv_holder_bilinear h1 h2
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) AmbientSpace ℝ)).1
  have hneg := (nondiv_holder_comp_clm h12
    (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))).1
  refine ⟨hG1.contDiffOn, h0, (nondiv_holder_congr hd).1.mpr ?_⟩
  simpa only [neg_apply, ContinuousLinearMap.id_apply] using hneg

/-- Blueprint `prop:bootstrap-C3`: the weak prescribed-mean-curvature equation on a disk
`B(y₀, ρ)` rescales to the unit disk, for `f_ρ(z) = ρ⁻¹ f(y₀ + ρ z)` and
`G_ρ(z) = ρ G(y₀ + ρ z)`. -/
lemma mc_weak_rescale {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (y0 : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ 1 f (ball y0 ρ))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball y0 ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) :
    ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient (fun z => ρ⁻¹ • f (y0 + ρ • z)) y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient (fun z => ρ⁻¹ • f (y0 + ρ • z)) y‖ ^ 2)) =
        ∫ y, (fun z => ρ * G (y0 + ρ • z)) y * φ y := by
  let e := frozenBallScaling y0 hρ
  let fρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => ρ⁻¹ • f (e z)
  let Gρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => ρ * G (e z)
  change ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient fρ y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient fρ y‖ ^ 2)) = ∫ y, Gρ y * φ y
  have hm : MapsTo e (ball 0 1) (ball y0 ρ) := quasilinear_ballScaling_maps_unit y0 hρ
  have hg (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      gradient fρ x = gradient f (e x) := by
    have hd := bootstrap_fderiv_affine y0 x ρ ρ⁻¹
      ((hf.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero)
    simp only [inv_mul_cancel₀ hρ.ne', one_smul] at hd
    change (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
      (fderiv ℝ (fun z => ρ⁻¹ • f (y0 + ρ • z)) x) =
      (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm (fderiv ℝ f (y0 + ρ • x))
    rw [hd]
  intro φ hφ hcφ hsφ
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply hφ.comp
    change ContDiff ℝ (⊤ : ℕ∞) (frozenBallScaling y0 hρ).symm
    rw [frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul ρ⁻¹
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm
  have hsψ : tsupport ψ ⊆ ball y0 ρ := by
    rw [tsupport_comp_eq_preimage φ e.symm]
    intro x hx
    simpa only [e.apply_symm_apply] using hm (hsφ hx)
  have hgp (x) : gradient ψ (e x) = ρ⁻¹ • gradient φ x := by
    have hh := frozen_gradient_comp_ballScaling_symm y0 hρ (hφ.differentiable (by simp)) (e x)
    change gradient ψ (e x) = ρ⁻¹ • gradient φ (e.symm (e x)) at hh
    simpa only [e.symm_apply_apply] using hh
  have hi (x) : inner ℝ (gradient fρ x) (gradient φ x) /
      Real.sqrt (1 + ‖gradient fρ x‖ ^ 2) =
      ρ * (inner ℝ (gradient f (e x)) (gradient ψ (e x)) /
        Real.sqrt (1 + ‖gradient f (e x)‖ ^ 2)) := by
    rw [hgp, real_inner_smul_right]
    by_cases hx : x ∈ tsupport φ
    · rw [hg x (hsφ hx)]
      field_simp
    · rw [gradient_eq_zero_of_notMem_tsupport hx]
      simp
  have hright (x) : Gρ x * φ x = ρ * (G (e x) * ψ (e x)) := by
    simp only [Gρ, ψ, Function.comp_apply, e.symm_apply_apply]
    ring
  simp_rw [hi, hright]
  rw [integral_const_mul, integral_const_mul,
    frozen_integral_comp_ballScaling
      (fun y => inner ℝ (gradient f y) (gradient ψ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) y0 hρ,
    frozen_integral_comp_ballScaling (fun y => G y * ψ y) y0 hρ,
    he ψ hψ hcψ hsψ]

end LiquidDrop
