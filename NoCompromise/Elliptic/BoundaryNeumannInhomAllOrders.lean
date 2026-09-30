module

public import NoCompromise.Elliptic.BoundaryNeumannCkLevel
public import NoCompromise.Elliptic.BoundaryNeumannC2InhomSmooth
public import NoCompromise.Elliptic.BoundaryNeumannSmoothChain
public import NoCompromise.Elliptic.BoundaryNeumannCkIterate

@[expose] public section

/-!
# The flat inhomogeneous Neumann problem with smooth data: regularity of every order

For smooth coefficient, volume forcing and boundary datum (the hypotheses of
`boundary_neumann_c2_inhom_smooth`), the weak solution of the flat inhomogeneous conormal
problem agrees near the origin with a `Cᵏ` function on a full ball, for every `k`. The
reduction to the homogeneous problem is the one of `boundary_neumann_c2_inhom_smooth_fixed`:
`w = u - q` with the smooth lift `q` of the boundary datum and the smooth datum
`H = boundaryNeumannInhomDatum A f h`, and `w` is C^{1,α} on a neighbourhood of the closed half
ball of radius `1/4`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A C¹ function on an open `U ⊇ K` with finite C^{1,α} norm on `K` is `C^{1,α}` on `K` in the
sense of `HasCkHolderOn`. -/
theorem HasC1HolderOn.hasCkHolderOn_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf1 : ContDiffOn ℝ 1 f U) (hf : HasC1HolderOn α f K) :
    HasCkHolderOn 1 α f U K := by
  refine (HasCkHolderOn.succ_iff (k := 0) hU).2 ⟨hf1.differentiableOn one_ne_zero,
    ⟨holderUniformNorm f K, fun x hx =>
      norm_le_holderUniformNorm hf.function_holder.uniform_bounded hx⟩, ?_⟩
  refine hasCkHolderOn_zero_iff.2 ⟨hf1.continuousOn_fderiv_of_isOpen hU le_rfl,
    ⟨holderUniformNorm (fderiv ℝ f) K, fun x hx =>
      norm_le_holderUniformNorm hf.derivative_holder.uniform_bounded hx⟩,
    holderSeminorm α (fderiv ℝ f) K, fun x hx y hy => ?_⟩
  rw [dist_eq_norm]
  exact hf.derivative_holder.nondiv_norm_sub_le hx hy

/-- **Flat inhomogeneous Neumann problem, regularity of every order** (`thm:boundary-neumann`,
smooth iteration, from the levels). Under the hypotheses of `boundary_neumann_c2_inhom_smooth`
(smooth coefficient, forcing and boundary datum, vanishing cross coefficients on the face),
given all the levels `BoundaryNeumannCkLevel k`, for every `k` the weak solution agrees a.e. on a
half ball `B⁺_ρ` with a `C^{k+1}` function `v` on the full ball `ball 0 ρ`, whose gradient is `F`
a.e. there, and which satisfies the classical conormal condition on the face. -/
theorem boundary_neumann_inhom_all_orders_of_levels (hlev : ∀ k, BoundaryNeumannCkLevel k)
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ (k + 1) v (ball 0 ρ) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall ρ)] v ∧
      F =ᵐ[volume.restrict (boundaryHalfBall ρ)] gradient v ∧
      ∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 ρ →
        A (graphBaseEmbedding y) (gradient v (graphBaseEmbedding y)) (Fin.last 2) = h y := by
  intro k
  obtain ⟨cap, HA, B, hcap, hHA, hB, d⟩ :=
    boundary_neumann_c2_inhom_smooth_exists_data hα hα1 hO hsub hA hf hh hell hcross hpos
  let E := max (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) 0
  obtain ⟨C, hC, hreg⟩ := boundary_neumann_c1_holder_conormal
    hα hα1 hlam hcap hHA hB (le_max_right _ _ : 0 ≤ E)
  obtain ⟨u, hu, hzu, hFu, hbu, hhu, hface⟩ := hreg A F z f h
    d.continuous_coefficient d.bound_coefficient d.elliptic d.holder_coefficient d.cross_face
    d.normal_neighborhood d.bound_datum d.bound_normal d.bound_gradient_datum
    d.bound_gradient_normal d.holder_gradient_datum d.holder_gradient_normal
    d.continuous_forcing d.bound_forcing d.holder_forcing hz (le_max_left _ _) hweak
  let q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)
  let H := boundaryNeumannInhomDatum A f h
  let w := fun x => u x - q x
  obtain ⟨hqs, hHs⟩ := boundary_neumann_c2_inhom_smooth_lift_datum
    hlam hO hsub hA hf hh hpos
  let S := closure (boundaryHalfBall (1 / 4 : ℝ))
  have hSc : IsCompact S :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall (1 / 4 : ℝ) ⊆
      ball 0 (1 / 4 : ℝ))).isCompact_closure
  have hSconv : Convex ℝ S := (convex_boundaryHalfBall (1 / 4 : ℝ)).closure
  have hSclosed : S ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4 : ℝ) :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hSsmall : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSone : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSunit : S ⊆ closure (boundaryHalfBall 1) :=
    closure_mono (boundaryHalfBall_mono (by norm_num))
  have hqH : HasC1HolderOn α q S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv isOpen_ball hSone hqs
  have huH : HasC1HolderOn α u S := boundary_neumann_c2_inhom_holder_of_gradient
    hα.le hα1.le hC.le hSc hSconv isOpen_ball hSsmall hu
    (fun x hx => hbu x (hSsmall hx))
    (fun x hx y hy => hhu x (hSsmall hx) y (hSsmall hy))
  have hud (x) (hx : x ∈ S) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (isOpen_ball.mem_nhds (hSsmall hx))).differentiableAt one_ne_zero
  have hqd (x) (hx : x ∈ S) : DifferentiableAt ℝ q x :=
    (hqs.contDiffAt (isOpen_ball.mem_nhds (hSone hx))).differentiableAt (by simp)
  have hwH : HasC1HolderOn α w S :=
    boundary_neumann_c2_inhom_holder_sub huH hqH hud hqd
  have hgrad (x) (hx : x ∈ S) : gradient w x = gradient u x - gradient q x :=
    boundary_neumann_c2_inhom_gradient_sub (hud x hx) (hqd x hx)
  obtain ⟨V, hV, hVs, hhV, hbV, hposV⟩ := d.normal_neighborhood
  have hproj (x) (hx : x ∈ S) : graphProjectionN 2 x ∈ V :=
    hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall (hSone hx)))
  have hhd (x) (hx : x ∈ S) : DifferentiableAt ℝ h (graphProjectionN 2 x) :=
    (hhV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hbd (x) (hx : x ∈ S) :
      DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) (graphProjectionN 2 x) :=
    (hbV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hH0 : ∀ x ∈ S, x (Fin.last 2) = 0 → H x (Fin.last 2) = 0 :=
    fun x hx hx0 => boundaryNeumannInhomDatum_flat_of_elliptic hlam f hx0
      (hell x (hSunit hx)) (hhd x hx) (hbd x hx)
  have hw0 : ∀ x ∈ S, x (Fin.last 2) = 0 → gradient w x (Fin.last 2) = 0 := by
    intro x hx hx0
    have he : graphBaseEmbedding (graphProjectionN 2 x) = x := by
      rw [boundary_neumann_graphBase_eq_append, ← hx0, graphAppendN_projection]
    have hnon : boundaryNeumannNormalCoefficient A (graphProjectionN 2 x) ≠ 0 :=
      (hlam.trans_le (hposV _ (hproj x hx))).ne'
    have hqc := boundaryNeumannLift_conormal (hhd x hx) (hbd x hx) hnon
    rw [he] at hqc
    have huc := hface (graphProjectionN 2 x) (by rw [he]; exact hSsmall hx)
    rw [he] at huc
    apply boundary_neumann_c2_inhom_normal_zero
      (fun i hi => (hcross x (hSunit hx) hx0 i hi).1)
    · have hn := hnon
      rwa [boundaryNeumannNormalCoefficient_eq, he] at hn
    · rw [hgrad x hx, map_sub, PiLp.sub_apply]
      exact sub_eq_zero.mpr (huc.trans hqc.symm)
  have hred : IsBoundaryNeumannEquationOn A (fun x => F x - gradient q x) H 1 :=
    boundary_neumann_inhomogeneous_weak_reduction hα hα1.le hB hB
      d.continuous_coefficient d.bound_coefficient hz.memLp_gradient d.continuous_forcing
      d.bound_forcing d.holder_forcing hh.continuous.continuousOn hweak
  have hFsmall : F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4))] gradient u :=
    ae_restrict_of_ae_restrict_of_subset (boundaryHalfBall_mono (by norm_num)) hFu
  have heq : IsBoundaryNeumannEquationOn A (gradient w) H (1 / 4) :=
    boundary_neumann_c2_inhom_equation_congr
      (boundary_neumann_c2_inhom_equation_mono (by norm_num : (1 / 4 : ℝ) ≤ 1) hred) (by
        filter_upwards [hFsmall,
          ae_restrict_mem (isOpen_boundaryHalfBall (1 / 4 : ℝ)).measurableSet]
          with x hx hxs
        rw [hgrad x (subset_closure hxs), hx])
  -- the homogeneous problem on the neighbourhood `ball 0 (1/2)` of `S`
  have hq1 : ContDiffOn ℝ 1 q (ball 0 (1 / 2 : ℝ)) :=
    (hqs.of_le (by simp)).mono (ball_subset_ball (by norm_num))
  have hw1 : ContDiffOn ℝ 1 w (ball 0 (1 / 2 : ℝ)) := hu.sub hq1
  have hwk : HasCkHolderOn 1 α w (ball 0 (1 / 2 : ℝ)) S :=
    hwH.hasCkHolderOn_one isOpen_ball hw1
  have hAU : ContDiffOn ℝ (⊤ : ℕ∞) A (ball 0 (1 / 2 : ℝ)) :=
    hA.mono ((ball_subset_ball (by norm_num)).trans (ball_subset_closedBall.trans hsub))
  have hHU : ContDiffOn ℝ (⊤ : ℕ∞) H (ball 0 (1 / 2 : ℝ)) :=
    hHs.mono (ball_subset_ball (by norm_num))
  have hSU : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := hSsmall
  obtain ⟨ρ, hρ, v', hv'w, hv'⟩ := boundary_neumann_smooth_of_levels hlev hα hα1 hlam
    (R := 1 / 4) (by norm_num) (by norm_num) isOpen_ball hSU hAU hHU hwk
    (fun x hx => d.bound_coefficient x (hSunit hx)) (fun x hx => hell x (hSunit hx))
    (fun x hx => hcross x (hSunit hx)) hH0 hw0 heq (k + 1)
  set ρ' := min ρ (1 / 4 : ℝ) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'4 : ρ' ≤ 1 / 4 := min_le_right _ _
  have hball2 : ball (0 : EuclideanSpace ℝ (Fin 3)) ρ' ⊆ ball 0 (1 / 2) :=
    ball_subset_ball (by linarith)
  have hvC : ContDiffOn ℝ (k + 1 : ℕ) (fun x => v' x + q x) (ball 0 ρ') :=
    (hv'.mono (ball_subset_ball hρ'ρ)).add
      ((contDiffOn_infty.mp hqs (k + 1)).mono (hball2.trans (ball_subset_ball (by norm_num))))
  have hEq : EqOn (fun x => v' x + q x) u (boundaryHalfBall ρ') := fun x hx => by
    have h1 := hv'w (boundaryHalfBall_mono hρ'ρ hx)
    simp only [h1, w, sub_add_cancel]
  have hsub' : boundaryHalfBall ρ' ⊆ boundaryHalfBall (1 / 2) :=
    boundaryHalfBall_mono (by linarith)
  have hgradEq : EqOn (gradient fun x => v' x + q x) (gradient u) (boundaryHalfBall ρ') := by
    intro x hx
    have hev : (fun x => v' x + q x) =ᶠ[𝓝 x] u :=
      Filter.eventually_of_mem ((isOpen_boundaryHalfBall ρ').mem_nhds hx) hEq
    simp only [gradient, hev.fderiv_eq]
  refine ⟨ρ', hρ'0, fun x => v' x + q x, hvC, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' hzu,
      ae_restrict_mem (isOpen_boundaryHalfBall ρ').measurableSet] with x hx hxs
    rw [hx]
    exact (hEq hxs).symm
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' hFu,
      ae_restrict_mem (isOpen_boundaryHalfBall ρ').measurableSet] with x hx hxs
    rw [hx, hgradEq hxs]
  · intro y hy
    have hk1 : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_add_left 1 k
    have hv1 : ContDiffOn ℝ 1 (fun x => v' x + q x) (ball 0 ρ') := hvC.of_le hk1
    have hu1 : ContDiffOn ℝ 1 u (ball 0 ρ') := hu.mono hball2
    have hcv : ContinuousOn (gradient fun x => v' x + q x) (ball 0 ρ') :=
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
        (hv1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
    have hcu : ContinuousOn (gradient u) (ball 0 ρ') :=
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
        (hu1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
    have hmem : graphBaseEmbedding y ∈ closure (boundaryHalfBall ρ') :=
      boundary_neumann_reflect_mem_closure hy (by simp)
    have hgy : gradient (fun x => v' x + q x) (graphBaseEmbedding y) =
        gradient u (graphBaseEmbedding y) := by
      refine hgradEq.of_subset_closure (hcv.mono inter_subset_left) (hcu.mono inter_subset_left)
        (s := boundaryHalfBall ρ') (t := ball 0 ρ' ∩ closure (boundaryHalfBall ρ'))
        (fun x hx => ⟨hx.1, subset_closure hx⟩) (fun x hx => hx.2) ⟨hy, hmem⟩
    rw [hgy]
    exact hface y (hball2 hy)

/-- **`thm:boundary-neumann`, smooth iteration on the flat half ball (homogeneous form).** For a
smooth coefficient `A` and datum `H` near the closed half ball of radius `R ≤ 1`, and `w`
C^{1,α} there solving the homogeneous conormal problem (vanishing cross coefficients,
`H₃ = 0` and `∂₃w = 0` on the face), for every `k` there is a `Cᵏ` function on a full ball
`ball 0 ρ` agreeing with `w` on `B⁺_ρ`. -/
theorem boundary_neumann_smooth_all_orders
    {α lam cap R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hR : 0 < R) (hR1 : R ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (hw : HasCkHolderOn 1 α w U (closure (boundaryHalfBall R)))
    (hcap : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H R) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      EqOn v w (boundaryHalfBall ρ) ∧ ContDiffOn ℝ k v (ball 0 ρ) :=
  boundary_neumann_smooth_of_levels boundaryNeumannCkLevel_holds hα hα1 hlam hR hR1 hU hUc
    hA hH hw hcap hell hcross hH0 hw0 he

/-- **`thm:boundary-neumann`, smooth iteration for the flat inhomogeneous problem.** Under the
hypotheses of `boundary_neumann_c2_inhom_smooth` (smooth coefficient, volume forcing and
boundary datum), for every `k` the weak solution agrees a.e. on a half ball `B⁺_ρ` with a
`C^{k+1}` function on the full ball `ball 0 ρ` whose gradient is `F` a.e. there and which
satisfies the classical conormal condition on the face. -/
theorem boundary_neumann_inhom_all_orders
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ (k + 1) v (ball 0 ρ) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall ρ)] v ∧
      F =ᵐ[volume.restrict (boundaryHalfBall ρ)] gradient v ∧
      ∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 ρ →
        A (graphBaseEmbedding y) (gradient v (graphBaseEmbedding y)) (Fin.last 2) = h y :=
  boundary_neumann_inhom_all_orders_of_levels boundaryNeumannCkLevel_holds hα hα1 hlam hO hsub
    hA hf hh hell hcross hpos hz hweak

end LiquidDrop
