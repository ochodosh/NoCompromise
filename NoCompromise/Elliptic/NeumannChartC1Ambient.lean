module

public import NoCompromise.Elliptic.NeumannChartC1Flat
public import NoCompromise.Elliptic.NeumannChartC1Geometry
public import NoCompromise.BV.SmoothApproxBoundary

@[expose] public section

/-!
# Ambient C¹ regularity and the classical outward Neumann condition

The inverse of the global homeomorphism is used only on the image of the
regular chart. There the inverse function theorem gives its C¹ regularity.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- Push a flat representative into the ambient coordinates. The Lipschitz
bound on the homeomorphism transfers the exceptional null set forward. -/
theorem neumannChartC1_pushforward_representative
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
    {z u h₀ : AmbientSpace → ℝ} (hu : ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)))
    (hzu : (fun y => z (neumannLocalizeMap c a ρ y))
      =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u)
    (hcon : ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
      neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
        (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
          -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
            Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ c.region ∧ ContDiffOn ℝ 1 v V ∧
      z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  let Θ := neumannLocalizeMap c a ρ
  let V := Θ '' ball 0 (1 / 2 : ℝ)
  let v := u ∘ E.symm
  have hΘ : ContDiff ℝ 1 Θ := contDiff_neumannLocalizeMap c hψ a ρ
  have hsmall : ball (0 : AmbientSpace) (1 / 2 : ℝ) ⊆ ball 0 2 :=
    ball_subset_ball (by norm_num)
  have hVE : V = E '' ball 0 (1 / 2 : ℝ) :=
    image_congr (fun y hy => hEq (hsmall hy))
  have hV : IsOpen V := by
    rw [hVE]
    exact E.isOpenMap _ isOpen_ball
  have hinv (x : AmbientSpace) (hx : x ∈ V) : E.symm x ∈ ball 0 (1 / 2 : ℝ) := by
    rw [hVE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [E.symm_apply_apply] using hy
  have hi : ContDiffOn ℝ 1 E.symm V := by
    intro x hx
    have hy := hsmall (hinv x hx)
    have hnear : Θ =ᶠ[𝓝 (E.symm x)] E :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) (fun y hy => hEq hy)
    obtain ⟨L, hL⟩ := hreg _ hy
    have hd : HasFDerivAt E (L : AmbientSpace →L[ℝ] AmbientSpace) (E.symm x) := by
      rw [hL]
      exact (hΘ.differentiable one_ne_zero _).hasFDerivAt.congr_of_eventuallyEq hnear.symm
    exact (E.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) hd
      (hΘ.contDiffAt.congr_of_eventuallyEq hnear.symm)).contDiffWithinAt
  have hv : ContDiffOn ℝ 1 v V := hu.comp hi (fun x hx => hinv x hx)
  have hcomp : EqOn (v ∘ Θ) u (ball 0 (1 / 2 : ℝ)) := by
    intro y hy
    change u (E.symm (neumannLocalizeMap c a ρ y)) = u y
    rw [hEq (hsmall hy), E.symm_apply_apply]
  have hmaps : MapsTo E.symm (D ∩ V) (boundaryHalfBall (1 / 2)) := by
    intro x hx
    refine ⟨hinv x hx.2, ?_⟩
    apply (neumannLocalize_mem_domain_iff hD hupper hlower hface
      (hsmall (hinv x hx.2))).mp
    rw [hEq (hsmall (hinv x hx.2)), E.apply_symm_apply]
    exact hx.1
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse
    (hD.inter hV).measurableSet E.symm.continuous.continuousOn hE.lipschitzOnWith
    hmaps (fun x _ => E.apply_symm_apply x)
  have hq : Measure.QuasiMeasurePreserving E.symm (volume.restrict (D ∩ V))
      (volume.restrict (boundaryHalfBall (1 / 2))) :=
    ⟨E.symm.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  refine ⟨V, v, hV, ⟨0, mem_ball_self (by norm_num), h0⟩,
    (image_mono hsmall).trans hregion, hv, ?_, ?_⟩
  · filter_upwards [hq.ae hzu, ae_restrict_mem (hD.inter hV).measurableSet] with x hx hxV
    change z (neumannLocalizeMap c a ρ (E.symm x)) = u (E.symm x) at hx
    rwa [hEq (hsmall (hinv x hxV.2)), E.apply_symm_apply] at hx
  · intro x hx
    let y := E.symm x
    have hy : y ∈ ball 0 (1 / 2 : ℝ) := hinv x hx.2
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
      exact (hv.contDiffAt (hV.mem_nhds hx.2)).differentiableAt one_ne_zero
    have hd : gradient u y (Fin.last 2) =
        -(ρ * Real.sqrt (1 + ‖gradient c.height (a + ρ • graphProjectionN 2 y)‖ ^ 2)) *
          fderiv ℝ v x (c.outwardNormal x) := by
      rw [gradient_apply_eq_fderiv_single, ← hnear.fderiv_eq,
        fderiv_comp y hvx (hΘ.differentiable one_ne_zero y),
        ContinuousLinearMap.comp_apply]
      dsimp only [Θ]
      have hn := neumannChartC1_normal_derivative c hψ a (graphProjectionN 2 y) ρ
      rw [hybase] at hn
      rw [hn, hxy, map_smul, smul_eq_mul]
    have hc := hcon (graphProjectionN 2 y) (by rwa [hybase])
    rw [neumannChartC1_coefficient_face c hψ a _ hρ, hybase, hxy, hd] at hc
    have hn : ρ ^ 2 *
        Real.sqrt (1 + ‖gradient c.height (a + ρ • graphProjectionN 2 y)‖ ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos (sq_pos_of_pos hρ) (Real.sqrt_pos.mpr (by positivity)))
    apply mul_left_cancel₀ hn
    nlinarith only [hc]

/-- Local ambient regularity at a point of a specified smooth boundary chart,
with the chart's classical outward unit normal. -/
theorem IsWeakNeumannSolution.exists_boundary_chart_c1_conormal
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
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ c.region ∧ ContDiffOn ℝ 1 v V ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  obtain ⟨ρ, hρ, h0, -, -, hreg, hregion, hupper, hlower, hface, -, E, C, K,
    hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap hψ hp hpc
  have hH1 := neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
    ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  have hweak := fun φ hφ hcφ hsφ =>
    hz.normal_chart_test_eq hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      (φ := φ) hφ hcφ hsφ
  obtain ⟨u, hu, hzu, -, -, hcon⟩ := neumannChartC1_flat_representative c hψ _ hρ hreg
    hfs hhs (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hH1 hweak
  exact neumannChartC1_pushforward_representative hD c hψ _ hρ h0 E hE hEq hreg
    hregion hupper hlower hface hu hzu hcon

/-- Local C¹ regularity with the chart-independent outward normal of the
given smooth domain. The weak equation still uses its original Lipschitz
boundary witness; no equality of boundary witnesses is assumed. -/
theorem IsWeakNeumannSolution.exists_boundary_c1_conormal
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (hGs : HasSmoothBoundary D)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {p : AmbientSpace} (hp : p ∈ frontier D) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 v V ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ x ∈ frontier D ∩ V,
        fderiv ℝ v x (hGs.hasC1Boundary.outwardNormal x) = h₀ x := by
  obtain ⟨c, hc, hpc, hψ⟩ := hGs p hp
  obtain ⟨V, v, hV, hpV, hVc, hv, hzv, hn⟩ :=
    hz.exists_boundary_chart_c1_conormal hf hh hfs hhs hc hψ hp hpc
  refine ⟨V, v, hV, hpV, hv, hzv, fun x hx => ?_⟩
  rw [hGs.hasC1Boundary.outwardNormal_eq_chart hc hx.1 (hVc hx.2)]
  exact hn x hx

end LiquidDrop
