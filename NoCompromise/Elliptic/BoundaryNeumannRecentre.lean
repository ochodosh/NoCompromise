module

public import NoCompromise.Elliptic.BoundaryNeumannC2HolderData
public import NoCompromise.Elliptic.BoundaryC2aLocal
public import NoCompromise.Elliptic.BoundaryHolderSimilarity
public import NoCompromise.Elliptic.QuasilinearCampanatoPullback

@[expose] public section

/-!
# Recentring the flat inhomogeneous Neumann identity (`thm:boundary-neumann`)

For a flat point `p = (p', 0)` and `0 < r` with `‖p'‖ + r ≤ 1`, the weak conormal identity
on the unit half ball for `(A, F, f, h)` gives the same identity on the unit half ball for
the recentred data `A (p + r •)`, `r • F (p + r •)`, `r² f (p + r •)` and `r h (p' + r •)`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_recentre_norm_emb (y : EuclideanSpace ℝ (Fin 2)) :
    ‖graphBaseEmbedding y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_succ]

lemma boundary_neumann_recentre_emb_last (y : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding y (Fin.last 2) = 0 :=
  graphBaseEmbedding_apply_two y

lemma boundary_neumann_recentre_measurableSet_upper :
    MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)} :=
  measurableSet_lt measurable_const (EuclideanSpace.proj (Fin.last 2)).continuous.measurable

/-- Change of variables `x = c + r • y` on the upper half space, for `c` on the face. -/
lemma boundary_neumann_recentre_upper_integral (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    {c : EuclideanSpace ℝ (Fin 3)} (hc : c (Fin.last 2) = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, g x) =
      r ^ 3 * ∫ y in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, g (c + r • y) := by
  set H := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hH : MeasurableSet H := boundary_neumann_recentre_measurableSet_upper
  rw [← integral_indicator hH, ← integral_indicator hH]
  have hind : H.indicator (fun y => g (c + r • y)) =
      fun y => H.indicator g (c + r • y) := by
    funext y
    have hmem : c + r • y ∈ H ↔ y ∈ H := by
      simp only [H, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hc, zero_add]
      exact ⟨fun h => pos_of_mul_pos_right h hr.le, fun h => mul_pos hr h⟩
    by_cases hy : y ∈ H
    · rw [indicator_of_mem hy, indicator_of_mem (hmem.mpr hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hmem.mp h))]
  rw [hind]
  have h1 := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (fun w => H.indicator g (c + w)) r
  simp only [finrank_euclideanSpace_fin] at h1
  rw [h1, integral_add_left_eq_self (fun w => H.indicator g w) c, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hr 3)), ← mul_assoc, mul_inv_cancel₀ (pow_pos hr 3).ne',
    one_mul]

/-- Change of variables `y = p' + r • w` on the plane. -/
lemma boundary_neumann_recentre_plane_integral (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    (∫ y, g y) = r ^ 2 * ∫ w, g (p' + r • w) := by
  have h1 := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun w => g (p' + w)) r
  simp only [finrank_euclideanSpace_fin] at h1
  rw [h1, integral_add_left_eq_self (fun w => g w) p', smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hr 2)), ← mul_assoc, mul_inv_cancel₀ (pow_pos hr 2).ne',
    one_mul]

/-- A set integral over the unit half ball equals the one over the upper half space when
the integrand vanishes off the unit ball. -/
lemma boundary_neumann_recentre_halfBall_eq_upper (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ∀ x, x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 → g x = 0) :
    (∫ x in boundaryHalfBall 1, g x) =
      ∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, g x := by
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    boundary_neumann_recentre_measurableSet_upper inter_subset_right ?_).symm
  intro x hx
  exact hg x (fun h => hx.2 ⟨h, hx.1⟩)

/-- A set integral over the unit disk equals the full integral when the integrand vanishes
off the disk. -/
lemma boundary_neumann_recentre_disk_eq (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : ∀ y, y ∉ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 → g y = 0) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, g y) = ∫ y, g y :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hg

/-- **Recentring the flat Neumann identity.** For a flat centre `p = (p', 0)` and a radius
`0 < r` with `‖p'‖ + r ≤ 1`, the weak conormal identity for `(A, F, f, h)` on the unit half
ball gives the weak conormal identity on the unit half ball for the recentred data. -/
theorem boundary_neumann_weak_recentre
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1,
          inner ℝ (A (graphBaseEmbedding p' + r • x) (r • F (graphBaseEmbedding p' + r • x)))
            (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, (r ^ 2 * f (graphBaseEmbedding p' + r • x)) * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            (r * h (p' + r • y)) * φ (graphBaseEmbedding y) := by
  intro φ hφ hcφ hsφ
  set c : EuclideanSpace ℝ (Fin 3) := graphBaseEmbedding p' with hc_def
  have hc3 : c (Fin.last 2) = 0 := boundary_neumann_recentre_emb_last p'
  have hcn : ‖c‖ = ‖p'‖ := boundary_neumann_recentre_norm_emb p'
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  set e := frozenBallScaling (-(r⁻¹ • c)) hri with he_def
  have he : ∀ x, e x = r⁻¹ • (x - c) := by
    intro x
    rw [he_def, frozenBallScaling_apply, smul_sub]
    abel
  set ψ : EuclideanSpace ℝ (Fin 3) → ℝ := φ ∘ e with hψ_def
  have hψ : ContDiff ℝ 1 ψ := by
    have : (⇑e) = fun x => r⁻¹ • (x - c) := funext he
    rw [hψ_def, this]
    exact hφ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e
  have hsupp : ∀ x, e x ∈ tsupport φ → ‖x‖ < 1 := by
    intro x hx
    have h1 : ‖e x‖ < 1 := mem_ball_zero_iff.mp (hsφ hx)
    have hx' : x = c + r • e x := by
      rw [he, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [hx']
    calc ‖c + r • e x‖ ≤ ‖c‖ + r * ‖e x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hr.le]
      _ < ‖p'‖ + r * 1 := by
          rw [hcn]
          gcongr
      _ ≤ 1 := by linarith
  have hsψ : tsupport ψ ⊆ ball 0 1 := by
    intro x hx
    rw [hψ_def, tsupport_comp_eq_preimage] at hx
    exact mem_ball_zero_iff.mpr (hsupp x hx)
  have hgrad : ∀ x, gradient ψ x = r⁻¹ • gradient φ (e x) := by
    intro x
    exact nondiv_gradient_comp_ballScaling _ x hri
      ((hφ.differentiable one_ne_zero) (e x))
  have hφ0 : ∀ y, y ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 → φ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun h => hy (hsφ h))
  have hgφ0 : ∀ y, y ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 → gradient φ y = 0 := by
    intro y hy
    rw [gradient, fderiv_of_notMem_tsupport ℝ (fun h => hy (hsφ h)), map_zero]
  have hψ0 : ∀ x, x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 → ψ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h))
  have hgψ0 : ∀ x, x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 → gradient ψ x = 0 := by
    intro x hx
    rw [gradient, fderiv_of_notMem_tsupport ℝ (fun h => hx (hsψ h)), map_zero]
  have heinv : ∀ y, e (c + r • y) = y := by
    intro y
    rw [he, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hw := hweak ψ hψ hcψ hsψ
  -- the gradient term
  have hL : (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient ψ x)) =
      r ^ 2 * ∫ y in boundaryHalfBall 1,
        inner ℝ (A (c + r • y) (F (c + r • y))) (gradient φ y) := by
    rw [boundary_neumann_recentre_halfBall_eq_upper _
        (fun x hx => by rw [hgψ0 x hx, inner_zero_right]),
      boundary_neumann_recentre_upper_integral _ hc3 hr,
      boundary_neumann_recentre_halfBall_eq_upper _
        (fun y hy => by rw [hgφ0 y hy, inner_zero_right])]
    simp_rw [hgrad, heinv, real_inner_smul_right]
    rw [integral_const_mul, ← mul_assoc]
    congr 1
    field_simp
  -- the volume source term
  have hF : (∫ x in boundaryHalfBall 1, f x * ψ x) =
      r ^ 3 * ∫ y in boundaryHalfBall 1, f (c + r • y) * φ y := by
    rw [boundary_neumann_recentre_halfBall_eq_upper _ (fun x hx => by rw [hψ0 x hx, mul_zero]),
      boundary_neumann_recentre_upper_integral _ hc3 hr,
      boundary_neumann_recentre_halfBall_eq_upper _ (fun y hy => by rw [hφ0 y hy, mul_zero])]
    simp only [hψ_def, Function.comp_apply, heinv]
  -- the boundary term
  have hemb : ∀ w : EuclideanSpace ℝ (Fin 2),
      e (graphBaseEmbedding (p' + r • w)) = graphBaseEmbedding w := by
    intro w
    rw [map_add, map_smul, ← hc_def, heinv]
  have hB : (∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * ψ (graphBaseEmbedding y)) =
      r ^ 2 * ∫ w in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        h (p' + r • w) * φ (graphBaseEmbedding w) := by
    have hz1 : ∀ y, y ∉ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        h y * ψ (graphBaseEmbedding y) = 0 := by
      intro y hy
      rw [hψ0 _ (fun h => hy (by
        rw [mem_ball_zero_iff, ← boundary_neumann_recentre_norm_emb]
        exact mem_ball_zero_iff.mp h)), mul_zero]
    have hz2 : ∀ w, w ∉ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        h (p' + r • w) * φ (graphBaseEmbedding w) = 0 := by
      intro w hw
      rw [hφ0 _ (fun h => hw (by
        rw [mem_ball_zero_iff, ← boundary_neumann_recentre_norm_emb]
        exact mem_ball_zero_iff.mp h)), mul_zero]
    rw [boundary_neumann_recentre_disk_eq _ hz1, boundary_neumann_recentre_disk_eq _ hz2,
      boundary_neumann_recentre_plane_integral _ p' hr]
    simp only [hψ_def, Function.comp_apply, hemb]
  rw [hL, hF, hB] at hw
  -- divide by `r`
  have hlhs : (∫ x in boundaryHalfBall 1,
      inner ℝ (A (c + r • x) (r • F (c + r • x))) (gradient φ x)) =
      r * ∫ y in boundaryHalfBall 1, inner ℝ (A (c + r • y) (F (c + r • y))) (gradient φ y) := by
    simp_rw [map_smul, real_inner_smul_left]
    exact integral_const_mul _ _
  have hf2 : (∫ x in boundaryHalfBall 1, (r ^ 2 * f (c + r • x)) * φ x) =
      r ^ 2 * ∫ y in boundaryHalfBall 1, f (c + r • y) * φ y := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hh2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      (r * h (p' + r • y)) * φ (graphBaseEmbedding y)) =
      r * ∫ w in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        h (p' + r • w) * φ (graphBaseEmbedding w) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hlhs, hf2, hh2]
  have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
  have key : r * (r ^ 2 * ∫ y in boundaryHalfBall 1,
      inner ℝ (A (c + r • y) (F (c + r • y))) (gradient φ y)) =
      r * (-(r ^ 3 * ∫ y in boundaryHalfBall 1, f (c + r • y) * φ y) -
        r ^ 2 * ∫ w in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
          h (p' + r • w) * φ (graphBaseEmbedding w)) := by rw [hw]
  apply mul_left_cancel₀ hr2
  linear_combination key

lemma boundary_neumann_recentre_norm_le (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖frozenBallScaling (graphBaseEmbedding p') hr x‖ ≤ ‖p'‖ + r * ‖x‖ := by
  rw [frozenBallScaling_apply]
  refine (norm_add_le _ _).trans ?_
  rw [boundary_neumann_recentre_norm_emb, norm_smul, Real.norm_of_nonneg hr.le]

lemma boundary_neumann_recentre_last (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 3)) :
    frozenBallScaling (graphBaseEmbedding p') hr x (Fin.last 2) = r * x (Fin.last 2) := by
  rw [frozenBallScaling_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    boundary_neumann_recentre_emb_last, zero_add]

lemma boundary_neumann_recentre_mapsTo_closedBall (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1) :
    MapsTo (frozenBallScaling (graphBaseEmbedding p') hr) (closedBall 0 1) (closedBall 0 1) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx ⊢
  have := boundary_neumann_recentre_norm_le p' hr x
  nlinarith

lemma boundary_neumann_recentre_mapsTo_halfBall (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1) :
    MapsTo (frozenBallScaling (graphBaseEmbedding p') hr) (boundaryHalfBall 1)
      (boundaryHalfBall 1) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [mem_ball_zero_iff] at hx1
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff]
    have := boundary_neumann_recentre_norm_le p' hr x
    nlinarith
  · change 0 < frozenBallScaling (graphBaseEmbedding p') hr x (Fin.last 2)
    rw [boundary_neumann_recentre_last]
    exact mul_pos hr hx2

lemma boundary_neumann_recentre_mapsTo_closure (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1) :
    MapsTo (frozenBallScaling (graphBaseEmbedding p') hr) (closure (boundaryHalfBall 1))
      (closure (boundaryHalfBall 1)) :=
  (boundary_neumann_recentre_mapsTo_halfBall p' hr hpr).closure
    (frozenBallScaling (graphBaseEmbedding p') hr).continuous

lemma boundary_neumann_recentre_mapsTo_disk (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1) :
    MapsTo (frozenBallScaling p' hr) (closedBall 0 1) (closedBall 0 1) := by
  intro y hy
  rw [mem_closedBall_zero_iff] at hy ⊢
  rw [frozenBallScaling_apply]
  have h1 : ‖p' + r • y‖ ≤ ‖p'‖ + r * ‖y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  nlinarith

lemma boundary_neumann_recentre_emb_comp (p' y : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) :
    frozenBallScaling (graphBaseEmbedding p') hr (graphBaseEmbedding y) =
      graphBaseEmbedding (frozenBallScaling p' hr y) := by
  rw [frozenBallScaling_apply, frozenBallScaling_apply, map_add, map_smul]

/-- The energy of the recentred gradient. -/
lemma boundary_neumann_recentre_energy {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (p' : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hpr : ‖p'‖ + r ≤ 1)
    (hF : IntegrableOn (fun x => ‖F x‖ ^ 2) (boundaryHalfBall 1)) :
    (∫ x in boundaryHalfBall 1, ‖r • F (frozenBallScaling (graphBaseEmbedding p') hr x)‖ ^ 2) ≤
      r⁻¹ * ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
  set c := graphBaseEmbedding p'
  set e := frozenBallScaling c hr
  set H := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hH : MeasurableSet H := boundary_neumann_recentre_measurableSet_upper
  have hB : MeasurableSet (boundaryHalfBall 1) := (isOpen_boundaryHalfBall 1).measurableSet
  set g := (boundaryHalfBall 1).indicator (fun x => ‖F x‖ ^ 2)
  have hg : Integrable g := (integrable_indicator_iff hB).mpr hF
  have hge : Integrable (fun y => g (c + r • y)) :=
    (hg.comp_add_left c).comp_smul hr.ne'
  have hgn : ∀ x, 0 ≤ g x := fun x => indicator_nonneg (fun _ _ => by positivity) x
  have hmap := boundary_neumann_recentre_mapsTo_halfBall p' hr hpr
  have h1 : (∫ x in boundaryHalfBall 1, ‖r • F (e x)‖ ^ 2) =
      r ^ 2 * ∫ x in boundaryHalfBall 1, g (c + r • x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hB fun x hx => ?_
    change ‖r • F (e x)‖ ^ 2 = r ^ 2 * (boundaryHalfBall 1).indicator (fun x => ‖F x‖ ^ 2) (e x)
    rw [indicator_of_mem (hmap hx), norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
  have h2 : (∫ x in boundaryHalfBall 1, g (c + r • x)) ≤ ∫ x in H, g (c + r • x) :=
    setIntegral_mono_set hge.integrableOn (Eventually.of_forall fun x => hgn _)
      (Eventually.of_forall inter_subset_right)
  have h3 : (∫ x in H, g x) = ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
    rw [setIntegral_indicator hB]
    congr 2
    exact inter_eq_right.mpr inter_subset_right
  have h4 := boundary_neumann_recentre_upper_integral g
    (boundary_neumann_recentre_emb_last p') hr
  rw [h3] at h4
  rw [h1]
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  have h5 : (∫ x in H, g (c + r • x)) = (r ^ 3)⁻¹ * ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
    rw [h4, ← mul_assoc, inv_mul_cancel₀ hr3.ne', one_mul]
  calc r ^ 2 * ∫ x in boundaryHalfBall 1, g (c + r • x)
      ≤ r ^ 2 * ∫ x in H, g (c + r • x) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = r⁻¹ * ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2 := by
        rw [h5, ← mul_assoc]
        congr 1
        field_simp

/-- **Boundary Neumann C²,α estimate at every flat point.** Under the hypotheses of
`boundary_neumann_c2_holder_inhom_holder_data` on the unit half ball, for a radius `0 < r ≤ 1`
fixed before the data and every flat centre `p = (p', 0)` with `‖p'‖ + r ≤ 1`, the solution
has a representative which is C² on `p + r • B⁺_{3/32}` with bounded, α-Hölder second
derivatives; the constant depends only on `α`, `λ`, `K`, `M` and `r`. -/
theorem boundary_neumann_c2_holder_recentred {α lam K M r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (O : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen O → closedBall 0 1 ⊆ O → ContDiffOn ℝ 2 A O →
        HasC1HolderOn α A (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ A) (closedBall 0 1) →
        nondivC1HolderNorm α A (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ A) (closedBall 0 1) ≤ K →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
          ∀ i : Fin 3, i ≠ Fin.last 2 →
            A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
            A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        IsOpen U → closedBall 0 1 ⊆ U →
        (∀ y ∈ U, lam ≤ boundaryNeumannNormalCoefficient A y) →
        ContDiffOn ℝ 2 h U →
        HasC1HolderOn α h (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ h) (closedBall 0 1) →
        nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ h) (closedBall 0 1) ≤ K →
        ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
        nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
        HasH1GradientOn z F (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
            -(∫ x in boundaryHalfBall 1, f x * φ x) -
              ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                h y * φ (graphBaseEmbedding y)) →
        ∀ p' : EuclideanSpace ℝ (Fin 2), ‖p'‖ + r ≤ 1 →
        ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 2 u (frozenBallScaling (graphBaseEmbedding p') hr ''
            boundaryHalfBall (1 / 4 * (3 / 8))) ∧
          z =ᵐ[volume.restrict (frozenBallScaling (graphBaseEmbedding p') hr ''
            boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
          ∀ i j : Fin 3,
            (∀ x ∈ frozenBallScaling (graphBaseEmbedding p') hr ''
                boundaryHalfBall (1 / 4 * (3 / 8)),
              |boundaryNeumannC2Entry u x i j| ≤ Cb) ∧
            ∀ x ∈ frozenBallScaling (graphBaseEmbedding p') hr ''
                boundaryHalfBall (1 / 4 * (3 / 8)),
              ∀ y ∈ frozenBallScaling (graphBaseEmbedding p') hr ''
                boundaryHalfBall (1 / 4 * (3 / 8)),
                |boundaryNeumannC2Entry u x i j - boundaryNeumannC2Entry u y i j| ≤
                  Cb * dist x y ^ α := by
  obtain ⟨Cb₀, hCb₀, hbase⟩ :=
    boundary_neumann_c2_holder_inhom_holder_data (M := r⁻¹ * M) hα hα1 hlam hK (by positivity)
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hri1 : 1 ≤ r⁻¹ := one_le_inv₀ hr |>.mpr hr1
  have hriα : 1 ≤ r⁻¹ ^ α := Real.one_le_rpow hri1 hα.le
  refine ⟨r⁻¹ ^ 2 * Cb₀ * r⁻¹ ^ α, by positivity, ?_⟩
  intro A F z f h O U hO hOb hAO hA hdA hAK hdAK hell hcross hU hUb hnorm hhU hh hdh hhK hdhK
    hfO hf hfK hH1 hE hweak p' hpr
  set c : EuclideanSpace ℝ (Fin 3) := graphBaseEmbedding p' with hc_def
  set e := frozenBallScaling c hr with he_def
  set e2 := frozenBallScaling p' hr with he2_def
  have hmB := boundary_neumann_recentre_mapsTo_closedBall p' hr hpr
  have hmCl := boundary_neumann_recentre_mapsTo_closure p' hr hpr
  have hmH := boundary_neumann_recentre_mapsTo_halfBall p' hr hpr
  have hmD := boundary_neumann_recentre_mapsTo_disk p' hr hpr
  have hec : ContDiff ℝ 2 (⇑e) := contDiff_const.add (contDiff_id.const_smul r)
  have he2c : ContDiff ℝ 2 (⇑e2) := contDiff_const.add (contDiff_id.const_smul r)
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
  -- coefficient
  obtain ⟨hA', hA'n⟩ := boundary_c2a_c1Holder_comp_scaling hα.le c hr hr1 hA hmB
  have hdAe : fderiv ℝ (A ∘ e) = fun x => r • (fderiv ℝ A ∘ e) x := by
    funext x
    exact boundary_c2a_fderiv_comp_scaling c x hr A
  obtain ⟨hdA₁, hdA₁n⟩ := boundary_c2a_c1Holder_comp_scaling hα.le c hr hr1 hdA hmB
  obtain ⟨hdA', hdA'n⟩ := boundary_c2a_c1Holder_const_smul hdA₁ hr.le hr1
  -- boundary datum
  set hp : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => r • (h ∘ e2) y with hhp_def
  obtain ⟨hh₁, hh₁n⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p' hr hr1 hh hmD
  obtain ⟨hh', hh'n⟩ := boundary_c2a_c1Holder_const_smul hh₁ hr.le hr1
  have hdhe : fderiv ℝ hp = fun y => r • (r • (fderiv ℝ h ∘ e2) y) := by
    funext y
    rw [hhp_def, show (fun y => r • (h ∘ e2) y) = r • (h ∘ e2) from rfl,
      fderiv_const_smul_field (𝕜 := ℝ) (f := h ∘ e2) r, Pi.smul_apply,
      boundary_c2a_fderiv_comp_scaling p' y hr h]
    rfl
  obtain ⟨hdh₁, hdh₁n⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p' hr hr1 hdh hmD
  obtain ⟨hdh₂, hdh₂n⟩ := boundary_c2a_c1Holder_const_smul hdh₁ hr.le hr1
  obtain ⟨hdh', hdh'n⟩ := boundary_c2a_c1Holder_const_smul hdh₂ hr.le hr1
  -- volume source
  obtain ⟨hf₁, hf₁n⟩ := boundary_c2a_c1Holder_comp_scaling hα.le c hr hr1 hf hmB
  obtain ⟨hf', hf'n⟩ := boundary_c2a_c1Holder_const_smul hf₁ (by positivity) hr2
  -- H¹ and energy
  have hH1' : HasH1GradientOn (z ∘ e) (fun x => r • F (e x)) (boundaryHalfBall 1) := by
    have hchain := (hH1.comp_homeomorph_on (isOpen_boundaryHalfBall 1)
      (isOpen_boundaryHalfBall 1) e (quasilinear_ballScaling_lipschitz c hr)
      (quasilinear_ballScaling_symm_lipschitz c hr) hmH).1
    have hd (x) : (fderiv ℝ (⇑e) x).adjoint = r • ContinuousLinearMap.id ℝ _ := by
      rw [he_def, frozenBallScaling_fderiv]
      simp only [map_smul, ContinuousLinearMap.adjoint_id]
    simpa only [hd, smul_apply, ContinuousLinearMap.id_apply] using hchain
  have hFi : IntegrableOn (fun x => ‖F x‖ ^ 2) (boundaryHalfBall 1) :=
    (hH1.memLp_gradient.integrable_norm_pow two_ne_zero)
  have hE' : (∫ x in boundaryHalfBall 1, ‖r • F (e x)‖ ^ 2) ≤ r⁻¹ * M :=
    (boundary_neumann_recentre_energy p' hr hpr hFi).trans
      (mul_le_mul_of_nonneg_left hE hri.le)
  have hweak' := boundary_neumann_weak_recentre p' hr hpr hweak
  have key := hbase (A ∘ e) (fun x => r • F (e x)) (z ∘ e) (fun y => (r ^ 2) • (f ∘ e) y) hp
    (e ⁻¹' O) (e2 ⁻¹' U) (hO.preimage e.continuous) (fun x hx => hOb (hmB hx))
    (hAO.comp hec.contDiffOn (mapsTo_preimage _ _)) hA'
    (by rw [hdAe]; exact hdA') (hA'n.trans hAK)
    (by rw [hdAe]; exact hdA'n.trans (hdA₁n.trans hdAK))
    (fun x hx ξ => hell (e x) (hmCl hx) ξ)
    (fun x hx hx3 i hi => hcross (e x) (hmCl hx)
      (by rw [he_def, boundary_neumann_recentre_last, hx3, mul_zero]) i hi)
    (hU.preimage e2.continuous) (fun y hy => hUb (hmD hy))
    (fun y hy => by
      have := hnorm (e2 y) hy
      have h2 := boundary_neumann_recentre_emb_comp p' y hr
      rw [← hc_def] at h2
      unfold boundaryNeumannNormalCoefficient at this ⊢
      rw [Function.comp_apply, he_def, h2]
      exact this)
    ((hhU.comp he2c.contDiffOn (mapsTo_preimage _ _)).const_smul r) hh'
    (by rw [hdhe]; exact hdh') (hh'n.trans (hh₁n.trans hhK))
    (by rw [hdhe]; exact hdh'n.trans (hdh₂n.trans (hdh₁n.trans hdhK)))
    ((hfO.comp (hec.of_le (by norm_num)).contDiffOn (mapsTo_preimage _ _)).const_smul (r ^ 2))
    hf' (hf'n.trans (hf₁n.trans hfK)) hH1' hE'
    (fun φ hφ hcφ hsφ => by
      have := hweak' φ hφ hcφ hsφ
      simpa only [hhp_def, Function.comp_apply, smul_eq_mul, he_def, he2_def,
        frozenBallScaling_apply] using this)
  obtain ⟨u₀, -, hu2, hzu, -, hent, -⟩ := key
  set S := boundaryHalfBall (1 / 4 * (3 / 8) : ℝ)
  have hSo : IsOpen S := isOpen_boundaryHalfBall _
  refine ⟨u₀ ∘ e.symm, boundary_c2a_contDiffOn_comp_scaling_symm c hr hu2, ?_, ?_⟩
  · -- almost-everywhere equality transported by the similarity
    have hSm : MeasurableSet (e '' S) := (e.isOpenMap S hSo).measurableSet
    have hh0 := (boundary_ballScaling_symm_quasiMeasurePreserving c hr).ae
      ((ae_restrict_iff' hSo.measurableSet).mp hzu)
    filter_upwards [ae_restrict_of_ae hh0, ae_restrict_mem hSm] with x hx hxS
    obtain ⟨y, hy, rfl⟩ := hxS
    have hs : (frozenBallScaling c hr).symm (e y) = y := e.symm_apply_apply y
    have := hx (by rw [hs]; exact hy)
    rw [hs] at this
    change z (e y) = u₀ (e.symm (e y))
    rw [e.symm_apply_apply]
    exact this
  · intro i j
    obtain ⟨D, hDeq, -, hDb, hDh⟩ := hent i j
    have hent' : ∀ y ∈ S, boundaryNeumannC2Entry (u₀ ∘ e.symm) (e y) i j =
        r⁻¹ ^ 2 * D y := by
      intro y hy
      rw [boundary_c2a_entry_comp_scaling c y hr u₀ i j, hDeq hy]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [hent' y hy, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r⁻¹ ^ 2)]
      calc r⁻¹ ^ 2 * |D y| ≤ r⁻¹ ^ 2 * Cb₀ :=
            mul_le_mul_of_nonneg_left (hDb y (subset_closure hy)) (by positivity)
        _ ≤ r⁻¹ ^ 2 * Cb₀ * r⁻¹ ^ α := le_mul_of_one_le_right (by positivity) hriα
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      rw [hent' y hy, hent' y' hy', ← mul_sub, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < r⁻¹ ^ 2)]
      have hd : dist y y' = r⁻¹ * dist (e y) (e y') := by
        rw [he_def, quasilinear_ballScaling_dist c y y' hr, ← mul_assoc,
          inv_mul_cancel₀ hr.ne', one_mul]
      have hH := hDh y (subset_closure hy) y' (subset_closure hy')
      rw [hd, Real.mul_rpow hri.le dist_nonneg] at hH
      calc r⁻¹ ^ 2 * |D y - D y'| ≤ r⁻¹ ^ 2 * (Cb₀ * (r⁻¹ ^ α * dist (e y) (e y') ^ α)) :=
            mul_le_mul_of_nonneg_left hH (by positivity)
        _ = r⁻¹ ^ 2 * Cb₀ * r⁻¹ ^ α * dist (e y) (e y') ^ α := by ring

/-- Second-derivative entries only depend on the germ of the function. -/
lemma boundary_neumann_recentre_entry_congr {u w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (h : u =ᶠ[𝓝 x] w) (i j : Fin 3) :
    boundaryNeumannC2Entry u x i j = boundaryNeumannC2Entry w x i j := by
  unfold boundaryNeumannC2Entry
  have h1 : (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) :=
    (h.fderiv (𝕜 := ℝ)).mono fun y hy => by simp only [hy]
  rw [h1.fderiv_eq]

/-- **Gluing local C²,α pieces.** If every point of an open set `L` has a neighbourhood piece
`P x` containing all points of `L` at distance `< ρ`, with C² representatives of `z` whose
second derivatives are bounded by `Cb` and `α`-Hölder with constant `Cb` on the piece, then one
representative of `z` is C² on `L` with second derivatives bounded and `α`-Hölder on `L`. -/
theorem boundary_neumann_layer_glue {α Cb ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hCb : 0 ≤ Cb)
    {z : EuclideanSpace ℝ (Fin 3) → ℝ} {L : Set (EuclideanSpace ℝ (Fin 3))} (hL : IsOpen L)
    (P : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hPo : ∀ x ∈ L, IsOpen (P x)) (hmem : ∀ x ∈ L, ∀ y ∈ L, dist x y < ρ → y ∈ P x)
    (hu2 : ∀ x ∈ L, ContDiffOn ℝ 2 (u x) (P x))
    (hzu : ∀ x ∈ L, z =ᵐ[volume.restrict (P x)] u x)
    (hb : ∀ x ∈ L, ∀ i j : Fin 3, ∀ y ∈ P x, |boundaryNeumannC2Entry (u x) y i j| ≤ Cb)
    (hh : ∀ x ∈ L, ∀ i j : Fin 3, ∀ y ∈ P x, ∀ y' ∈ P x,
      |boundaryNeumannC2Entry (u x) y i j - boundaryNeumannC2Entry (u x) y' i j| ≤
        Cb * dist y y' ^ α) :
    ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 v L ∧ z =ᵐ[volume.restrict L] v ∧
      ∀ i j : Fin 3, (∀ x ∈ L, |boundaryNeumannC2Entry v x i j| ≤ Cb) ∧
        ∀ x ∈ L, ∀ y ∈ L, |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
          (2 * Cb * ρ⁻¹ ^ α + Cb) * dist x y ^ α := by
  refine ⟨fun x => u x x, ?_⟩
  have hself : ∀ x ∈ L, x ∈ P x := fun x hx => hmem x hx x hx (by rw [dist_self]; exact hρ)
  -- two pieces agree on their overlap
  have hagree : ∀ x ∈ L, ∀ y ∈ L, EqOn (u x) (u y) (P x ∩ P y) := by
    intro x hx y hy
    have ho : IsOpen (P x ∩ P y) := (hPo x hx).inter (hPo y hy)
    have h1 : z =ᵐ[volume.restrict (P x ∩ P y)] u x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hzu x hx)
    have h2 : z =ᵐ[volume.restrict (P x ∩ P y)] u y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hzu y hy)
    have hae : u x =ᵐ[volume.restrict (P x ∩ P y)] u y := h1.symm.trans h2
    exact Measure.eqOn_open_of_ae_eq hae ho
      (((hu2 x hx).continuousOn).mono inter_subset_left)
      (((hu2 y hy).continuousOn).mono inter_subset_right)
  have hloc : ∀ x ∈ L, EqOn (fun y => u y y) (u x) (P x ∩ L) := by
    intro x hx y hy
    exact (hagree x hx y hy.2 ⟨hy.1, hself y hy.2⟩).symm
  have hnhds : ∀ x ∈ L, ∀ y ∈ P x ∩ L, (fun y => u y y) =ᶠ[𝓝 y] u x := by
    intro x hx y hy
    filter_upwards [((hPo x hx).inter hL).mem_nhds hy] with w hw using hloc x hx hw
  have hentry : ∀ x ∈ L, ∀ y ∈ P x ∩ L, ∀ i j : Fin 3,
      boundaryNeumannC2Entry (fun y => u y y) y i j = boundaryNeumannC2Entry (u x) y i j :=
    fun x hx y hy i j => boundary_neumann_recentre_entry_congr (hnhds x hx y hy) i j
  refine ⟨?_, ?_, fun i j => ⟨?_, ?_⟩⟩
  · intro x hx
    have hc : ContDiffAt ℝ 2 (u x) x :=
      (hu2 x hx).contDiffAt ((hPo x hx).mem_nhds (hself x hx))
    exact (hc.congr_of_eventuallyEq (hnhds x hx x ⟨hself x hx, hx⟩)).contDiffWithinAt
  · -- countable subcover
    obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : L => P x ∩ L) (fun x => (hPo x x.2).inter hL)
    have hcov : L = ⋃ x ∈ T, P (x : EuclideanSpace ℝ (Fin 3)) ∩ L := by
      rw [hTU]
      ext y
      simp only [mem_iUnion, mem_inter_iff]
      exact ⟨fun hy => ⟨⟨y, hy⟩, hself y hy, hy⟩, fun ⟨_, _, hy⟩ => hy⟩
    rw [hcov]
    refine (ae_restrict_biUnion_iff _ hT _).mpr fun x _ => ?_
    have h1 : z =ᵐ[volume.restrict (P x ∩ L)] u x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hzu x x.2)
    filter_upwards [h1, ae_restrict_mem (((hPo x x.2).inter hL).measurableSet)] with y hy hyP
    rw [hy]
    exact (hloc x x.2 hyP).symm
  · intro x hx
    rw [hentry x hx x ⟨hself x hx, hx⟩]
    exact hb x hx i j x (hself x hx)
  · intro x hx y hy
    have hd0 : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg α
    by_cases hxy : dist x y < ρ
    · have hyP : y ∈ P x ∩ L := ⟨hmem x hx y hy hxy, hy⟩
      rw [hentry x hx x ⟨hself x hx, hx⟩, hentry x hx y hyP]
      refine (hh x hx i j x (hself x hx) y hyP.1).trans ?_
      have : 0 ≤ 2 * Cb * ρ⁻¹ ^ α * dist x y ^ α := by positivity
      nlinarith
    · push Not at hxy
      have h1 := hb x hx i j x (hself x hx)
      have h2 := hb y hy i j y (hself y hy)
      rw [← hentry x hx x ⟨hself x hx, hx⟩] at h1
      rw [← hentry y hy y ⟨hself y hy, hy⟩] at h2
      have hge : 1 ≤ ρ⁻¹ ^ α * dist x y ^ α := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hρ.le) dist_nonneg]
        apply Real.one_le_rpow _ hα.le
        rw [inv_mul_eq_div, le_div_iff₀ hρ, one_mul]
        exact hxy
      calc |boundaryNeumannC2Entry (fun y => u y y) x i j -
            boundaryNeumannC2Entry (fun y => u y y) y i j|
          ≤ |boundaryNeumannC2Entry (fun y => u y y) x i j| +
            |boundaryNeumannC2Entry (fun y => u y y) y i j| := abs_sub _ _
        _ ≤ 2 * Cb := by linarith
        _ ≤ 2 * Cb * (ρ⁻¹ ^ α * dist x y ^ α) := le_mul_of_one_le_right (by positivity) hge
        _ ≤ (2 * Cb * ρ⁻¹ ^ α + Cb) * dist x y ^ α := by nlinarith

lemma boundary_neumann_layer_decomp (x : EuclideanSpace ℝ (Fin 3)) :
    x = graphBaseEmbedding (graphProjectionN 2 x) +
      x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp [Fin.last]

lemma boundary_neumann_layer_proj_norm_le (x : EuclideanSpace ℝ (Fin 3)) :
    ‖graphProjectionN 2 x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    Fin.sum_univ_three]
  simp only [graphProjectionN_apply]
  have : (0 : ℝ) ≤ x 2 ^ 2 := sq_nonneg _
  simp only [Fin.castSucc_zero, Fin.castSucc_one]
  linarith

lemma boundary_neumann_layer_dist_foot (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x - graphBaseEmbedding (graphProjectionN 2 x)‖ = |x (Fin.last 2)| := by
  have hx : x - graphBaseEmbedding (graphProjectionN 2 x) =
      x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) (1 : ℝ) := by
    nth_rewrite 1 [boundary_neumann_layer_decomp x]
    rw [add_sub_cancel_left]
  rw [hx, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- A point at distance `< 3/64` from the flat foot `(p', 0)` in the upper half space lies in
the recentred piece `p + (1/2) • B⁺_{3/32}`. -/
lemma boundary_neumann_layer_mem_piece (p' : EuclideanSpace ℝ (Fin 2))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : ‖y - graphBaseEmbedding p'‖ < 3 / 64)
    (hy3 : 0 < y (Fin.last 2)) :
    y ∈ frozenBallScaling (graphBaseEmbedding p') (by norm_num : (0 : ℝ) < 1 / 2) ''
      boundaryHalfBall (1 / 4 * (3 / 8)) := by
  refine ⟨(2 : ℝ) • (y - graphBaseEmbedding p'), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · change 0 < ((2 : ℝ) • (y - graphBaseEmbedding p')) (Fin.last 2)
    rw [PiLp.smul_apply, PiLp.sub_apply, boundary_neumann_recentre_emb_last, sub_zero,
      smul_eq_mul]
    positivity
  · rw [frozenBallScaling_apply, smul_smul]
    norm_num

/-- **Boundary Neumann C²,α up to the flat face `Γ_{1/2}`.** Under the hypotheses of
`boundary_neumann_c2_holder_inhom_holder_data` (the TeX data classes `A ∈ C^{2,α}`,
`f ∈ C^{1,α}`, `h ∈ C^{2,α}`, ellipticity, vanishing cross coefficients on the face, energy
bound), one representative of `z` is C² on the boundary layer
`B⁺_{1/2} ∩ {x₃ < 3/128}` of the flat face `Γ_{1/2}`, with second derivatives bounded and
`α`-Hölder on the whole layer, by a constant depending only on `α`, `λ`, `K`, `M`. -/
theorem boundary_neumann_c2_holder_layer {α lam K M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (O : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen O → closedBall 0 1 ⊆ O → ContDiffOn ℝ 2 A O →
        HasC1HolderOn α A (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ A) (closedBall 0 1) →
        nondivC1HolderNorm α A (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ A) (closedBall 0 1) ≤ K →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
          ∀ i : Fin 3, i ≠ Fin.last 2 →
            A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
            A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        IsOpen U → closedBall 0 1 ⊆ U →
        (∀ y ∈ U, lam ≤ boundaryNeumannNormalCoefficient A y) →
        ContDiffOn ℝ 2 h U →
        HasC1HolderOn α h (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ h) (closedBall 0 1) →
        nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ h) (closedBall 0 1) ≤ K →
        ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
        nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
        HasH1GradientOn z F (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
            -(∫ x in boundaryHalfBall 1, f x * φ x) -
              ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                h y * φ (graphBaseEmbedding y)) →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 2 v (boundaryHalfBall (1 / 2) ∩ {x | x (Fin.last 2) < 3 / 128}) ∧
          z =ᵐ[volume.restrict (boundaryHalfBall (1 / 2) ∩ {x | x (Fin.last 2) < 3 / 128})] v ∧
          ∀ i j : Fin 3,
            (∀ x ∈ boundaryHalfBall (1 / 2) ∩ {x | x (Fin.last 2) < 3 / 128},
              |boundaryNeumannC2Entry v x i j| ≤ C) ∧
            ∀ x ∈ boundaryHalfBall (1 / 2) ∩ {x | x (Fin.last 2) < 3 / 128},
              ∀ y ∈ boundaryHalfBall (1 / 2) ∩ {x | x (Fin.last 2) < 3 / 128},
                |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
                  C * dist x y ^ α := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨Cb, hCb, hrec⟩ :=
    boundary_neumann_c2_holder_recentred hα hα1 hlam hK hM hr (by norm_num)
  refine ⟨2 * Cb * (3 / 128 : ℝ)⁻¹ ^ α + Cb, by positivity, ?_⟩
  intro A F z f h O U hO hOb hAO hA hdA hAK hdAK hell hcross hU hUb hnorm hhU hh hdh hhK hdhK
    hfO hf hfK hH1 hE hweak
  have hp := hrec A F z f h O U hO hOb hAO hA hdA hAK hdAK hell hcross hU hUb hnorm hhU hh hdh
    hhK hdhK hfO hf hfK hH1 hE hweak
  set L := boundaryHalfBall (1 / 2) ∩ {x : EuclideanSpace ℝ (Fin 3) | x (Fin.last 2) < 3 / 128}
  have hLo : IsOpen L := (isOpen_boundaryHalfBall _).inter
    (isOpen_lt (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const)
  have hfoot : ∀ x ∈ L, ‖graphProjectionN 2 x‖ + 1 / 2 ≤ 1 := by
    intro x hx
    have h1 := boundary_neumann_layer_proj_norm_le x
    have h2 : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx.1.1
    linarith
  set P : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)) := fun x =>
    frozenBallScaling (graphBaseEmbedding (graphProjectionN 2 x)) hr ''
      boundaryHalfBall (1 / 4 * (3 / 8))
  set u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    if hx : ‖graphProjectionN 2 x‖ + 1 / 2 ≤ 1 then
      Classical.choose (hp (graphProjectionN 2 x) hx) else 0
  have hspec : ∀ x ∈ L, ContDiffOn ℝ 2 (u x) (P x) ∧ z =ᵐ[volume.restrict (P x)] u x ∧
      ∀ i j : Fin 3, (∀ y ∈ P x, |boundaryNeumannC2Entry (u x) y i j| ≤ Cb) ∧
        ∀ y ∈ P x, ∀ y' ∈ P x,
          |boundaryNeumannC2Entry (u x) y i j - boundaryNeumannC2Entry (u x) y' i j| ≤
            Cb * dist y y' ^ α := by
    intro x hx
    have hc := Classical.choose_spec (hp (graphProjectionN 2 x) (hfoot x hx))
    have hux : u x = Classical.choose (hp (graphProjectionN 2 x) (hfoot x hx)) := by
      simp only [u, dite_eq_left (hfoot x hx)]
    rw [hux]
    exact hc
  obtain ⟨v, hv2, hzv, hvent⟩ := boundary_neumann_layer_glue hα (by norm_num : (0 : ℝ) < 3 / 128)
    hCb.le hLo P u
    (fun x _ => ((frozenBallScaling _ hr).isOpenMap _ (isOpen_boundaryHalfBall _)))
    (fun x hx y hy hxy => by
      apply boundary_neumann_layer_mem_piece
      · have h1 := boundary_neumann_layer_dist_foot x
        rw [abs_of_pos hx.1.2] at h1
        have h2 : ‖y - graphBaseEmbedding (graphProjectionN 2 x)‖ ≤
            ‖y - x‖ + ‖x - graphBaseEmbedding (graphProjectionN 2 x)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        have h3 : ‖y - x‖ = dist x y := by rw [dist_comm, dist_eq_norm]
        have h4 : x (Fin.last 2) < 3 / 128 := hx.2
        linarith
      · exact hy.1.2)
    (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2.1)
    (fun x hx i j => ((hspec x hx).2.2 i j).1) (fun x hx i j => ((hspec x hx).2.2 i j).2)
  refine ⟨v, hv2, hzv, fun i j => ⟨fun x hx => ((hvent i j).1 x hx).trans ?_, (hvent i j).2⟩⟩
  have : 0 ≤ 2 * Cb * (3 / 128 : ℝ)⁻¹ ^ α := by positivity
  linarith

end LiquidDrop
