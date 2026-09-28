import NoCompromise.Elliptic.BoundaryNeumannInhomAllOrders
import NoCompromise.Elliptic.NeumannChartC2Ambient

/-!
# Ambient regularity of every order up to the boundary in a smooth chart

Smooth data in a regular normal chart satisfy the hypotheses of
`boundary_neumann_inhom_all_orders`, so for every `k` the localized weak solution agrees near
the origin with a `C^{k+1}` function on a full ball, with the exact flat conormal condition on
the face (`neumannChartSmooth_flat_representative`). Pushing this representative forward by the
smooth inverse of the normal chart gives, for every `k`, an open neighbourhood of the boundary
point on which the weak solution agrees a.e. in the domain with a `C^{k+1}` function whose
derivative along the outward normal is the boundary datum
(`IsWeakNeumannSolution.exists_boundary_all_orders_conormal`).
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- Smooth chart data and the localized weak equation give, for every `k`, a `C^{k+1}`
representative on a full ball around the origin satisfying the exact conormal condition on the
flat face. -/
theorem neumannChartSmooth_flat_representative
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f₀)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {z : AmbientSpace → ℝ} {F : AmbientSpace → AmbientSpace}
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ y in boundaryHalfBall 1,
        inner ℝ (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y (F y))
          (gradient φ y)) =
        -(∫ y in boundaryHalfBall 1,
          neumannChartC1Forcing (neumannLocalizeMap c a ρ) f₀ y * φ y) -
          ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            neumannChartC1BoundaryDatum c a ρ h₀ t * φ (graphBaseEmbedding t)) :
    ∀ k : ℕ, ∃ r > 0, ∃ u : AmbientSpace → ℝ,
      ContDiffOn ℝ (k + 1 : ℕ) u (ball 0 r) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall r)] u ∧
      ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 r →
        neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
          (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
            -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
              Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) := by
  intro k
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨lam, cap, HA, K, hlam, -, -, -, hd⟩ :=
    neumannChartC1_exists_data c hψ a hρ hreg hf hh hα hα1
  obtain ⟨U, hU, hsub, -, -, hpos⟩ := hd.normal_neighborhood
  obtain ⟨r, hr, u, hu, hzu, -, hcon⟩ := boundary_neumann_inhom_all_orders hα hα1 hlam
    isOpen_ball (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
    (smoothOn_neumannLocalizeCoefficient_ball c hψ a ρ hreg)
    (smoothOn_neumannChartC1Forcing (smooth_neumannLocalizeMap c hψ a ρ) hf hreg)
    (smooth_neumannChartC1BoundaryDatum c hψ a ρ hh)
    hd.elliptic hd.cross_face ⟨U, hU, hsub, hpos⟩ hz hweak k
  refine ⟨r, hr, u, ?_, hzu, hcon⟩
  exact_mod_cast hu

/-- Push a flat `C^{k+1}` representative into ambient coordinates: on the image of a small ball
it is `C^{k+1}`, agrees a.e. in the domain with the weak solution, and its derivative along the
chart's outward normal is the boundary datum on the boundary. -/
theorem neumannChartSmooth_pushforward_representative
    {D : Set AmbientSpace} (hD : IsOpen D) (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) {p : AmbientSpace}
    (h0 : neumannLocalizeMap c a ρ 0 = p)
    (E : AmbientSpace ≃ₜ AmbientSpace) {C : ℝ≥0} (hE : LipschitzWith C E)
    (hEq : EqOn (neumannLocalizeMap c a ρ) E (ball 0 2))
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    (hregion : neumannLocalizeMap c a ρ '' ball 0 2 ⊆ c.region)
    (hupper : neumannLocalizeMap c a ρ '' boundaryHalfBall 2 ⊆ D)
    (hlower : Disjoint (neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D))
    (hface : neumannLocalizeMap c a ρ ''
      (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D)
    {z u h₀ : AmbientSpace → ℝ} {k : ℕ} {r : ℝ} (hr : 0 < r)
    (hu : ContDiffOn ℝ (k + 1 : ℕ) u (ball 0 r))
    (hzu : (fun y => z (neumannLocalizeMap c a ρ y))
      =ᵐ[volume.restrict (boundaryHalfBall r)] u)
    (hcon : ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 r →
      neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
        (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
          -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
            Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ c.region ∧ ContDiffOn ℝ (k + 1 : ℕ) v V ∧
      z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  let Θ := neumannLocalizeMap c a ρ
  let s := min r 1
  have hs : 0 < s := lt_min hr one_pos
  let V := Θ '' ball 0 s
  let v := u ∘ E.symm
  have hk : ((k + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hΘ : ContDiff ℝ (k + 1 : ℕ) Θ :=
    contDiff_infty.mp (smooth_neumannLocalizeMap c hψ a ρ) (k + 1)
  have hΘ1 : ContDiff ℝ 1 Θ :=
    (smooth_neumannLocalizeMap c hψ a ρ).of_le (by simp)
  have hr2 : ball (0 : AmbientSpace) s ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hsmall : ball (0 : AmbientSpace) s ⊆ ball 0 2 :=
    ball_subset_ball ((min_le_right _ _).trans (by norm_num))
  have hVE : V = E '' ball 0 s := image_congr (fun y hy => hEq (hsmall hy))
  have hV : IsOpen V := by
    rw [hVE]
    exact E.isOpenMap _ isOpen_ball
  have hinv (x : AmbientSpace) (hx : x ∈ V) : E.symm x ∈ ball 0 s := by
    rw [hVE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [E.symm_apply_apply] using hy
  have hsymm (x : AmbientSpace) (hx : E.symm x ∈ ball 0 2) :
      ContDiffAt ℝ (k + 1 : ℕ) E.symm x := by
    have hnear : Θ =ᶠ[𝓝 (E.symm x)] E :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => hEq hy)
    obtain ⟨L, hL⟩ := hreg _ hx
    have hd : HasFDerivAt E (L : AmbientSpace →L[ℝ] AmbientSpace) (E.symm x) := by
      rw [hL]
      exact (hΘ1.differentiable one_ne_zero _).hasFDerivAt.congr_of_eventuallyEq hnear.symm
    exact E.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) hd
      (hΘ.contDiffAt.congr_of_eventuallyEq hnear.symm)
  have huat (y : AmbientSpace) (hy : y ∈ ball (0 : AmbientSpace) r) :
      ContDiffAt ℝ (k + 1 : ℕ) u y :=
    hu.contDiffAt (isOpen_ball.mem_nhds hy)
  have hv : ContDiffOn ℝ (k + 1 : ℕ) v V := fun x hx =>
    ((huat _ (hr2 (hinv x hx))).comp x (hsymm x (hsmall (hinv x hx)))).contDiffWithinAt
  have hcomp : EqOn (v ∘ Θ) u (ball 0 s) := by
    intro y hy
    change u (E.symm (neumannLocalizeMap c a ρ y)) = u y
    rw [hEq (hsmall hy), E.symm_apply_apply]
  have hmaps : MapsTo E.symm (D ∩ V) (boundaryHalfBall s) := by
    intro x hx
    refine ⟨hinv x hx.2, ?_⟩
    apply (neumannLocalize_mem_domain_iff hD hupper hlower hface
      (hsmall (hinv x hx.2))).mp
    rw [hEq (hsmall (hinv x hx.2)), E.apply_symm_apply]
    exact hx.1
  -- The a.e. identification.
  have hzus : (fun y => z (neumannLocalizeMap c a ρ y))
      =ᵐ[volume.restrict (boundaryHalfBall s)] u :=
    ae_restrict_of_ae_restrict_of_subset (boundaryHalfBall_mono (min_le_left _ _)) hzu
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse
    (hD.inter hV).measurableSet E.symm.continuous.continuousOn hE.lipschitzOnWith
    hmaps (fun x _ => E.apply_symm_apply x)
  have hq : Measure.QuasiMeasurePreserving E.symm (volume.restrict (D ∩ V))
      (volume.restrict (boundaryHalfBall s)) :=
    ⟨E.symm.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  refine ⟨V, v, hV, ⟨0, mem_ball_self hs, h0⟩, (image_mono hsmall).trans hregion, hv, ?_, ?_⟩
  · filter_upwards [hq.ae hzus, ae_restrict_mem (hD.inter hV).measurableSet] with x hx hxV
    change z (neumannLocalizeMap c a ρ (E.symm x)) = u (E.symm x) at hx
    rwa [hEq (hsmall (hinv x hxV.2)), E.apply_symm_apply] at hx
  · intro x hx
    let y := E.symm x
    have hy : y ∈ ball 0 s := hinv x hx.2
    have hxy : neumannLocalizeMap c a ρ y = x :=
      (hEq (hsmall hy)).trans (E.apply_symm_apply x)
    have hy0 : y (Fin.last 2) = 0 :=
      neumannLocalize_face_of_mem_frontier hD hupper hlower (hsmall hy) (hxy.symm ▸ hx.1)
    have hybase : graphBaseEmbedding (graphProjectionN 2 y) = y := by
      rw [boundary_neumann_graphBase_eq_append, ← hy0, graphAppendN_projection]
    have hnear : v ∘ Θ =ᶠ[𝓝 y] u :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) (fun w hw => hcomp hw)
    have hvx : DifferentiableAt ℝ v (Θ y) := by
      dsimp only [Θ]
      rw [hxy]
      exact (hv.contDiffAt (hV.mem_nhds hx.2)).differentiableAt hk
    have hd : gradient u y (Fin.last 2) =
        -(ρ * Real.sqrt (1 + ‖gradient c.height (a + ρ • graphProjectionN 2 y)‖ ^ 2)) *
          fderiv ℝ v x (c.outwardNormal x) := by
      rw [gradient_apply_eq_fderiv_single, ← hnear.fderiv_eq,
        fderiv_comp y hvx (hΘ1.differentiable one_ne_zero y),
        ContinuousLinearMap.comp_apply]
      dsimp only [Θ]
      have hn := neumannChartC1_normal_derivative c hψ a (graphProjectionN 2 y) ρ
      rw [hybase] at hn
      rw [hn, hxy, map_smul, smul_eq_mul]
    have hc := hcon (graphProjectionN 2 y) (by rw [hybase]; exact hr2 hy)
    rw [neumannChartC1_coefficient_face c hψ a _ hρ, hybase, hxy, hd] at hc
    have hn : ρ ^ 2 *
        Real.sqrt (1 + ‖gradient c.height (a + ρ • graphProjectionN 2 y)‖ ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos (sq_pos_of_pos hρ) (Real.sqrt_pos.mpr (by positivity)))
    apply mul_left_cancel₀ hn
    nlinarith only [hc]

/-- Local ambient regularity of every order up to the boundary at a point of a specified smooth
boundary chart: for every `k` the weak solution agrees a.e. in the domain, near the point, with
a `C^{k+1}` function whose derivative along the chart's outward unit normal is the boundary
datum on the boundary. -/
theorem IsWeakNeumannSolution.exists_boundary_chart_all_orders_conormal
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∀ k : ℕ, ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ c.region ∧ ContDiffOn ℝ (k + 1 : ℕ) v V ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  intro k
  obtain ⟨ρ, hρ, h0, -, -, hreg, hregion, hupper, hlower, hface, -, E, C, K,
    hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap hψ hp hpc
  have hH1 := neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
    ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  have hweak := fun φ hφ hcφ hsφ =>
    hz.normal_chart_test_eq hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      (φ := φ) hφ hcφ hsφ
  obtain ⟨r, hr, u, hu, hzu, hcon⟩ :=
    neumannChartSmooth_flat_representative c hψ _ hρ hreg hfs hhs hH1 hweak k
  exact neumannChartSmooth_pushforward_representative hD c hψ _ hρ h0 E hE hEq hreg
    hregion hupper hlower hface hr hu hzu hcon

/-- Local ambient regularity of every order up to the boundary with the chart-independent
outward normal of the given smooth domain. The weak equation still uses its original Lipschitz
boundary witness. -/
theorem IsWeakNeumannSolution.exists_boundary_all_orders_conormal
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (hGs : HasSmoothBoundary D)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {p : AmbientSpace} (hp : p ∈ frontier D) :
    ∀ k : ℕ, ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ (k + 1 : ℕ) v V ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V,
        fderiv ℝ v x (hGs.hasC1Boundary.outwardNormal x) = h₀ x := by
  intro k
  obtain ⟨c, hc, hpc, hψ⟩ := hGs p hp
  obtain ⟨V, v, hV, hpV, hVc, hv, hzv, hn⟩ :=
    hz.exists_boundary_chart_all_orders_conormal hf hh hfs hhs hc hψ hp hpc k
  refine ⟨V, v, hV, hpV, hv, hzv, fun x hx => ?_⟩
  rw [hGs.hasC1Boundary.outwardNormal_eq_chart hc hx.1 (hVc hx.2)]
  exact hn x hx

end LiquidDrop
