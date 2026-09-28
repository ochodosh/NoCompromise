import NoCompromise.Stationary.BootstrapC2
import NoCompromise.Stationary.EulerLagrange
import NoCompromise.Energy.PotentialHolder
import NoCompromise.Elliptic.NondivSchauderScalingInverse

/-! Blueprint `prop:bootstrap-C2`: scaling and local regularity in boundary charts. -/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `prop:bootstrap-C2`: affine pullback preserves finite Hölder norms. -/
lemma bootstrap_holder_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {f : E → F} {U W : Set E} (hf : HasFiniteHolderNormOn a f U)
    (c : E) (r : ℝ) (hm : MapsTo (fun x => c + r • x) W U) :
    HasFiniteHolderNormOn a (fun x => f (c + r • x)) W := by
  apply (nondiv_holder_comp_expansion ha ha1 (le_max_left 1 ‖r‖) hf hm ?_).1
  intro x hx y hy
  have he : c + r • x - (c + r • y) = r • (x - y) := by module
  rw [he, norm_smul]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- Blueprint `prop:bootstrap-C2`: derivative of a scaled affine pullback. -/
lemma bootstrap_fderiv_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (c x : E) (r b : ℝ) (hf : DifferentiableAt ℝ f (c + r • x)) :
    fderiv ℝ (fun z => b • f (c + r • z)) x = (b * r) • fderiv ℝ f (c + r • x) := by
  have hd := ((hf.hasFDerivAt.comp x
    (((hasFDerivAt_id x).const_smul r).const_add c)).const_smul b).fderiv
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul,
    Pi.smul_apply, Function.comp_apply, id_eq] using! hd

/-- Blueprint `prop:bootstrap-C2`: scaled affine pullback preserves C¹,α. -/
lemma bootstrap_c1Holder_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {f : E → F} {U W : Set E} (hU : IsOpen U) (hf : HasC1HolderOn a f U)
    (c : E) (r b : ℝ) (hm : MapsTo (fun x => c + r • x) W U) :
    HasC1HolderOn a (fun x => b • f (c + r • x)) W := by
  have he : ContDiff ℝ 1 (fun x : E => c + r • x) :=
    contDiff_const.add (contDiff_id.const_smul r)
  refine ⟨(hf.contDiff.comp he.contDiffOn hm).const_smul b,
    (nondiv_holder_const_smul (bootstrap_holder_affine ha ha1 hf.function_holder c r hm) b).1,
    ?_⟩
  apply (nondiv_holder_congr (g := fun x => (b * r) • fderiv ℝ f (c + r • x)) ?_).1.mpr
  · exact (nondiv_holder_const_smul
      (bootstrap_holder_affine ha ha1 hf.derivative_holder c r hm) (b * r)).1
  · intro x hx
    exact bootstrap_fderiv_affine c x r b
      ((hf.contDiff.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt one_ne_zero)

/-- Blueprint `prop:bootstrap-C2`: scaled affine pullback preserves C²,α. -/
lemma bootstrap_c2Holder_affine {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U W : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hW : IsOpen W) (hf : HasC2HolderOn a f U)
    (c : EuclideanSpace ℝ (Fin n)) (r b : ℝ)
    (hm : MapsTo (fun x => c + r • x) W U) :
    HasC2HolderOn a (fun x => b • f (c + r • x)) W := by
  have he : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => c + r • x) :=
    contDiff_const.add (contDiff_id.const_smul r)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf.contDiff |>.2.2
  have hd (x) (hx : x ∈ W) :
      fderiv ℝ (fun z => b • f (c + r • z)) x = (b * r) • fderiv ℝ f (c + r • x) :=
    bootstrap_fderiv_affine c x r b
      ((hf.contDiff.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt (by norm_num))
  have hdd (x) (hx : x ∈ W) :
      fderiv ℝ (fderiv ℝ (fun z => b • f (c + r • z))) x =
        (b * r * r) • fderiv ℝ (fderiv ℝ f) (c + r • x) := by
    have heq : fderiv ℝ (fun z => b • f (c + r • z)) =ᶠ[𝓝 x]
        (fun z => (b * r) • fderiv ℝ f (c + r • z)) := by
      filter_upwards [hW.mem_nhds hx] with z hz
      exact hd z hz
    rw [heq.fderiv_eq]
    exact bootstrap_fderiv_affine c x r (b * r)
      ((hDf.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt one_ne_zero)
  refine ⟨(hf.contDiff.comp he.contDiffOn hm).const_smul b,
    (nondiv_holder_const_smul (bootstrap_holder_affine ha ha1 hf.function_holder c r hm) b).1,
    (nondiv_holder_congr hd).1.mpr ?_, (nondiv_holder_congr hdd).1.mpr ?_⟩
  · exact (nondiv_holder_const_smul
      (bootstrap_holder_affine ha ha1 hf.derivative_holder c r hm) (b * r)).1
  · exact (nondiv_holder_const_smul
      (bootstrap_holder_affine ha ha1 hf.hessian_holder c r hm) (b * r * r)).1


/-- Blueprint `prop:bootstrap-C2`: the weak prescribed-mean-curvature bootstrap
on a disk of arbitrary positive radius. -/
theorem mc_graph_C2_holder_ball {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (y0 : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : HasC1HolderOn a f (ball y0 ρ))
    (hG : HasFiniteHolderNormOn a G (ball y0 ρ))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball y0 ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) :
    HasC2HolderOn a f (ball y0 (ρ / 2)) := by
  let e := frozenBallScaling y0 hρ
  let fρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => ρ⁻¹ • f (e z)
  let Gρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => ρ * G (e z)
  have hm : MapsTo e (ball 0 1) (ball y0 ρ) := quasilinear_ballScaling_maps_unit y0 hρ
  have hfρ : HasC1HolderOn a fρ (ball 0 1) :=
    bootstrap_c1Holder_affine ha.le ha1.le isOpen_ball hf y0 ρ ρ⁻¹ hm
  have hGρ : HasFiniteHolderNormOn a Gρ (ball 0 1) :=
    (nondiv_holder_const_smul (bootstrap_holder_affine ha.le ha1.le hG y0 ρ hm) ρ).1
  have hg (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      gradient fρ x = gradient f (e x) := by
    have hd := bootstrap_fderiv_affine y0 x ρ ρ⁻¹
      ((hf.contDiff.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero)
    simp only [inv_mul_cancel₀ hρ.ne', one_smul] at hd
    change (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
      (fderiv ℝ (fun z => ρ⁻¹ • f (y0 + ρ • z)) x) =
      (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm (fderiv ℝ f (y0 + ρ • x))
    rw [hd]
  have hscaled : HasC2HolderOn a fρ (ball 0 (1 / 2)) := by
    apply mc_graph_C2_holder_unit ha ha1 hfρ hGρ
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
  have hmback : MapsTo (fun x => -(ρ⁻¹ • y0) + ρ⁻¹ • x)
      (ball y0 (ρ / 2)) (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) := by
    have heq : (fun x => -(ρ⁻¹ • y0) + ρ⁻¹ • x) = e.symm := by
      funext x
      rw [frozenBallScaling_symm_apply]
      module
    rw [heq]
    exact nondiv_ballScaling_symm_maps_half y0 hρ
  have hback := bootstrap_c2Holder_affine ha.le ha1.le isOpen_ball isOpen_ball
    hscaled (-(ρ⁻¹ • y0)) ρ⁻¹ ρ hmback
  have hbackeq : (fun x => ρ • fρ (-(ρ⁻¹ • y0) + ρ⁻¹ • x)) = f := by
    funext x
    have heq : -(ρ⁻¹ • y0) + ρ⁻¹ • x = e.symm x := by
      rw [frozenBallScaling_symm_apply]
      module
    simp only [heq, fρ, e.apply_symm_apply, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  rwa [hbackeq] at hback


/-- Blueprint `prop:bootstrap-C2`: C¹ regularity on a closed disk supplies the
finite Hölder norm on its interior, for every exponent strictly between zero and one. -/
lemma bootstrap_holder_of_contDiffOn_closedBall {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : EuclideanSpace ℝ (Fin n) → F} (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hf : ContDiffOn ℝ 1 f (closedBall c r)) :
    HasFiniteHolderNormOn a f (ball c r) := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall c r) (isCompact_closedBall c r)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hf.continuousOn
  have hv (x) (hx : x ∈ ball c r) : ‖f x‖ ≤ max 0 M :=
    (hM x (ball_subset_closedBall hx)).trans (le_max_right _ _)
  have hl (x) (hx : x ∈ ball c r) (y) (hy : y ∈ ball c r) :
      ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using
      hK.dist_le_mul x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  apply HasFiniteHolderNormOn.of_bounds (le_max_left 0 M)
    (show 0 ≤ (K : ℝ) + 2 * max 0 M by positivity) hv
  intro x hx y hy
  simpa only [Real.one_rpow, mul_one, div_one] using
    holderInterpolation_quotient_le ha ha1 (show (0 : ℝ) < 1 by norm_num)
      (le_max_left 0 M) K.coe_nonneg hv hl hx hy

set_option maxHeartbeats 800000 in
-- The chart/slab construction needs extra elaboration for the composed coordinate maps.
/-- Blueprint `prop:bootstrap-C2`: at a boundary point of a minimiser, a C¹,α
chart height becomes C²,α on a smaller disk. -/
theorem MinimizerRep.height_C2_holder_near {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC1HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∃ ρ > 0, HasC2HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  let y1 := graphProjectionN 2 (c.placement.symm p)
  have hy1 : c.placement (graphMapN c.height y1) = p := by
    have hmem : p ∈ c.graphSurface ∩ c.region := by
      rw [← hc.frontier_inter_eq]
      exact ⟨hp, hpc⟩
    obtain ⟨⟨w, ⟨y, hy⟩, hw⟩, _⟩ := hmem
    have hpy : c.placement (graphMapN c.height y) = p := by rw [hy]; exact hw
    have hy0 : y1 = y := by
      dsimp [y1]
      rw [← hpy, c.placement.symm_apply_apply]
      exact graphProjectionN_append y (c.height y)
    rwa [hy0]
  obtain ⟨ρ₀, hρ₀, hf⟩ := hf
  let Φ : (EuclideanSpace ℝ (Fin 2)) × ℝ → AmbientSpace := fun q =>
    c.placement (graphBaseN 2 q.1 + q.2 • EuclideanSpace.single (Fin.last 2) (1 : ℝ))
  have hΦ : Continuous Φ :=
    c.placement.continuous.comp (((graphBaseN 2).continuous.comp continuous_fst).add
      (continuous_snd.smul continuous_const))
  have hΦp : Φ (y1, c.height y1) = p := hy1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (c.isOpen_region.preimage hΦ)
    (y1, c.height y1)
    (by change Φ (y1, c.height y1) ∈ c.region; rw [hΦp]; exact hpc)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp
    (c.height_contDiff.continuous.continuousAt (x := y1)) (ε / 2) (half_pos hε)
  let R := min ρ₀ (min r ε)
  have hR : 0 < R := lt_min hρ₀ (lt_min hr hε)
  have hRr : R ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : R ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hslab : ∀ ζ : EuclideanSpace ℝ (Fin 2) → ℝ,
      tsupport ζ ⊆ ball y1 R → ∀ y ∈ tsupport ζ, ∀ t : ℝ,
      |t - c.height y| ≤ ε / 2 →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈ c.region := by
    intro ζ hζ y hy t ht
    have hyr : dist y y1 < r := lt_of_lt_of_le (hζ hy) hRr
    have hyε : dist y y1 < ε := lt_of_lt_of_le (hζ hy) hRε
    have hfy := hfr hyr
    rw [Real.dist_eq] at hfy
    have htε : dist t (c.height y1) < ε := by
      rw [Real.dist_eq]
      calc
        |t - c.height y1| ≤ |t - c.height y| + |c.height y - c.height y1| := abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : (y, t) ∈ ball (y1, c.height y1) ε := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt hyε htε
    have hΦmem : Φ (y, t) ∈ c.region := hball hmem
    exact hΦmem
  let G : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
    minimizerMultiplier V Ω - (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal
  have hG : ContDiff ℝ 1 G := by
    have hv := (coulombPotential_contDiff_one_and_holder ha ha1 h.bounded).1
    have hg : ContDiff ℝ 1 (graphMapN c.height) :=
      (graphBaseN 2).contDiff.add (c.height_contDiff.smul contDiff_const)
    exact contDiff_const.sub (hv.comp ((contDiff_rigidPlacement c.placement).comp hg))
  refine ⟨R / 2, half_pos hR, ?_⟩
  apply mc_graph_C2_holder_ball ha ha1 y1 hR
    ((hf.mono (ball_subset_ball (min_le_left _ _))).1)
    (bootstrap_holder_of_contDiffOn_closedBall ha ha1 y1 R hG.contDiffOn)
  intro ζ hζ hcζ hsζ
  exact h.graph_prescribed_mean_curvature c hc hζ hcζ (half_pos hε) (hslab ζ hsζ)


/-- Blueprint `prop:bootstrap-C2`: C² regularity on a disk gives C¹,β on the
concentric half disk for every exponent strictly between zero and one. -/
lemma bootstrap_c1Holder_of_contDiffOn_two {n : ℕ} {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ 2 f (ball c r)) :
    HasC1HolderOn β f (ball c (r / 2)) := by
  have hsub : closedBall c (r / 2) ⊆ ball c r :=
    closedBall_subset_ball (by linarith)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) (ball c r) :=
    (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.2.2
  have hf1 : ContDiffOn ℝ 1 f (closedBall c (r / 2)) :=
    (hf.of_le (by norm_num)).mono hsub
  exact ⟨hf1.mono ball_subset_closedBall,
    bootstrap_holder_of_contDiffOn_closedBall hβ hβ1 c (r / 2) hf1,
    bootstrap_holder_of_contDiffOn_closedBall hβ hβ1 c (r / 2) (hDf.mono hsub)⟩

/-- Blueprint `prop:bootstrap-C2`: one C¹,α input at a boundary point of a
minimiser yields C²,β nearby for every β strictly between zero and one. -/
theorem MinimizerRep.height_C2_holder_all {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC1HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨r, hr, hC2⟩ := h.height_C2_holder_near hc hp hpc ha ha1 hf
  intro β hβ hβ1
  apply h.height_C2_holder_near hc hp hpc hβ hβ1
  exact ⟨r / 2, half_pos hr,
    bootstrap_c1Holder_of_contDiffOn_two hβ hβ1 _ hr hC2.contDiff⟩

end LiquidDrop
