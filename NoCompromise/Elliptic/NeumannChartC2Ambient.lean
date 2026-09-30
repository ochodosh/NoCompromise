module

public import NoCompromise.Elliptic.NeumannChartC1Ambient
public import NoCompromise.Elliptic.NeumannChartC2Flat

@[expose] public section

/-!
# Ambient C² regularity up to the boundary in a smooth chart

The flat C² representative is pushed forward by the smooth inverse of the
normal chart. The ambient Hessian is expressed by the chain rule through the
flat Hessian, whose continuous extension is assembled from the continuous
extensions of its entries.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- The norm topology on bilinear forms has continuous addition (instance
search does not find it through the strong-topology instances). -/
lemma neumannChartC2_continuousAdd :
    ContinuousAdd (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) :=
  (@SeminormedAddCommGroup.toIsTopologicalAddGroup
    (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) _).toContinuousAdd

/-- The bilinear form with prescribed coordinate matrix. -/
def neumannChartC2BilinOfEntries (M : Fin 3 → Fin 3 → ℝ) :
    AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ :=
  ∑ i, ∑ j, M i j • (EuclideanSpace.proj i : AmbientSpace →L[ℝ] ℝ).smulRight
    (EuclideanSpace.proj j : AmbientSpace →L[ℝ] ℝ)

lemma neumannChartC2BilinOfEntries_single (M : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    neumannChartC2BilinOfEntries M (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = M i j := by
  simp [neumannChartC2BilinOfEntries]

lemma neumannChartC2_bilin_eq_ofEntries (L : AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) :
    L = neumannChartC2BilinOfEntries
      (fun i j => L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  rw [neumannChartC2BilinOfEntries_single]

lemma continuousOn_neumannChartC2BilinOfEntries {X : Type*} [TopologicalSpace X]
    {M : Fin 3 → Fin 3 → X → ℝ} {s : Set X} (hM : ∀ i j, ContinuousOn (M i j) s) :
    ContinuousOn (fun x => neumannChartC2BilinOfEntries (fun i j => M i j x)) s := by
  have := neumannChartC2_continuousAdd
  unfold neumannChartC2BilinOfEntries
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact (hM i j).smul continuousOn_const

/-- Push a flat C² representative into ambient coordinates. On the part of
the image inside the domain the pushforward is C², and its Hessian extends
continuously to the closure: the chain rule writes it through the flat Hessian,
whose extension is assembled from the extensions of its entries. -/
theorem neumannChartC2_pushforward_representative
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
    (hu2 : ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))))
    (hzu : (fun y => z (neumannLocalizeMap c a ρ y))
      =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u)
    (hent : ∀ i j : Fin 3, ∃ Dij : AmbientSpace → ℝ,
      ContinuousOn Dij (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
      EqOn Dij (fun x => boundaryNeumannC2Entry u x i j)
        (boundaryHalfBall (1 / 4 * (3 / 8))))
    (hcon : ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
      neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
        (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
          -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
            Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ c.region ∧ ContDiffOn ℝ 1 v V ∧
      ContDiffOn ℝ 2 v (D ∩ V) ∧
      z =ᵐ[volume.restrict (D ∩ V)] v ∧
      (∃ Q : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ,
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  let Θ := neumannLocalizeMap c a ρ
  let V := Θ '' ball 0 (1 / 4 * (3 / 8) : ℝ)
  let v := u ∘ E.symm
  have hΘ : ContDiff ℝ 2 Θ :=
    (smooth_neumannLocalizeMap c hψ a ρ).of_le
      (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  have hr2 : ball (0 : AmbientSpace) (1 / 4 * (3 / 8) : ℝ) ⊆ ball 0 (1 / 2) :=
    ball_subset_ball (by norm_num)
  have hsmall : ball (0 : AmbientSpace) (1 / 4 * (3 / 8) : ℝ) ⊆ ball 0 2 :=
    ball_subset_ball (by norm_num)
  have hVE : V = E '' ball 0 (1 / 4 * (3 / 8) : ℝ) :=
    image_congr (fun y hy => hEq (hsmall hy))
  have hV : IsOpen V := by
    rw [hVE]
    exact E.isOpenMap _ isOpen_ball
  have hinv (x : AmbientSpace) (hx : x ∈ V) : E.symm x ∈ ball 0 (1 / 4 * (3 / 8) : ℝ) := by
    rw [hVE] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [E.symm_apply_apply] using hy
  have hsymm (x : AmbientSpace) (hx : E.symm x ∈ ball 0 2) : ContDiffAt ℝ 2 E.symm x := by
    have hnear : Θ =ᶠ[𝓝 (E.symm x)] E :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => hEq hy)
    obtain ⟨L, hL⟩ := hreg _ hx
    have hd : HasFDerivAt E (L : AmbientSpace →L[ℝ] AmbientSpace) (E.symm x) := by
      rw [hL]
      exact (hΘ1.differentiable one_ne_zero _).hasFDerivAt.congr_of_eventuallyEq hnear.symm
    exact E.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) hd
      (hΘ.contDiffAt.congr_of_eventuallyEq hnear.symm)
  have hu1at (y : AmbientSpace) (hy : y ∈ ball (0 : AmbientSpace) (1 / 2 : ℝ)) :
      ContDiffAt ℝ 1 u y :=
    hu.contDiffAt (isOpen_ball.mem_nhds hy)
  have hv : ContDiffOn ℝ 1 v V := fun x hx =>
    ((hu1at _ (hr2 (hinv x hx))).comp x
      ((hsymm x (hsmall (hinv x hx))).of_le (by norm_num))).contDiffWithinAt
  have hcomp : EqOn (v ∘ Θ) u (ball 0 (1 / 4 * (3 / 8) : ℝ)) := by
    intro y hy
    change u (E.symm (neumannLocalizeMap c a ρ y)) = u y
    rw [hEq (hsmall hy), E.symm_apply_apply]
  have hmaps : MapsTo E.symm (D ∩ V) (boundaryHalfBall (1 / 4 * (3 / 8))) := by
    intro x hx
    refine ⟨hinv x hx.2, ?_⟩
    apply (neumannLocalize_mem_domain_iff hD hupper hlower hface
      (hsmall (hinv x hx.2))).mp
    rw [hEq (hsmall (hinv x hx.2)), E.apply_symm_apply]
    exact hx.1
  have hu2at (y : AmbientSpace) (hy : y ∈ boundaryHalfBall (1 / 4 * (3 / 8))) :
      ContDiffAt ℝ 2 u y :=
    hu2.contDiffAt ((isOpen_boundaryHalfBall _).mem_nhds hy)
  have hv2 : ContDiffOn ℝ 2 v (D ∩ V) := fun x hx =>
    ((hu2at _ (hmaps hx)).comp x (hsymm x (hsmall (hinv x hx.2)))).contDiffWithinAt
  -- The Hessian and its continuous extension.
  choose Dij hDc hDe using hent
  have hPtil (y : AmbientSpace) (hy : y ∈ boundaryHalfBall (1 / 4 * (3 / 8))) :
      fderiv ℝ (fderiv ℝ u) y = neumannChartC2BilinOfEntries (fun i j => Dij i j y) := by
    have hPd : DifferentiableAt ℝ (fderiv ℝ u) y :=
      ((hu2at y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    refine (neumannChartC2_bilin_eq_ofEntries _).trans ?_
    congr 1
    funext i j
    rw [hDe i j hy]
    simp only [boundaryNeumannC2Entry]
    rw [fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ => EuclideanSpace.single j 1) hPd
      (differentiableAt_const _)]
    simp
  let Q : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ := fun x =>
    (ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ (fderiv ℝ u (E.symm x))).comp
        (fderiv ℝ (fderiv ℝ E.symm) x) +
      ((ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ).flip
        (fderiv ℝ E.symm x)).comp
        ((neumannChartC2BilinOfEntries (fun i j => Dij i j (E.symm x))).comp
          (fderiv ℝ E.symm x))
  have hQeq : EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V) := by
    intro x hx
    have hev : fderiv ℝ v =ᶠ[𝓝 x]
        fun x' => (fderiv ℝ u (E.symm x')).comp (fderiv ℝ E.symm x') := by
      filter_upwards [hV.mem_nhds hx.2] with x' hx'
      exact fderiv_comp x' ((hu1at _ (hr2 (hinv x' hx'))).differentiableAt one_ne_zero)
        ((hsymm x' (hsmall (hinv x' hx'))).differentiableAt (by norm_num))
    have hy := hmaps hx
    have hs := hsymm x (hsmall (hinv x hx.2))
    have hPd : DifferentiableAt ℝ (fderiv ℝ u) (E.symm x) :=
      ((hu2at _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hgd : DifferentiableAt ℝ (fderiv ℝ E.symm) x :=
      (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hsd : DifferentiableAt ℝ E.symm x := hs.differentiableAt (by norm_num)
    have hcd : DifferentiableAt ℝ (fun x' => fderiv ℝ u (E.symm x')) x := hPd.comp x hsd
    have hcomp' : fderiv ℝ (fun x' => fderiv ℝ u (E.symm x')) x =
        (fderiv ℝ (fderiv ℝ u) (E.symm x)).comp (fderiv ℝ E.symm x) :=
      fderiv_comp x hPd hsd
    change Q x = fderiv ℝ (fderiv ℝ v) x
    rw [hev.fderiv_eq, fderiv_clm_comp hcd hgd, hcomp', hPtil _ hy]
  -- Continuity on the closure.
  have hsubE : D ∩ V ⊆ E '' boundaryHalfBall (1 / 4 * (3 / 8)) := fun x hx =>
    ⟨E.symm x, hmaps hx, E.apply_symm_apply x⟩
  have hcl : MapsTo E.symm (closure (D ∩ V)) (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) := by
    intro x hx
    have hx' := closure_mono hsubE hx
    rw [← E.image_closure] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa only [E.symm_apply_apply] using hy
  have hcl2 (x : AmbientSpace) (hx : x ∈ closure (D ∩ V)) :
      E.symm x ∈ ball (0 : AmbientSpace) (1 / 2 : ℝ) :=
    closedBall_subset_ball (by norm_num : (1 / 4 * (3 / 8) : ℝ) < 1 / 2)
      ((closure_mono inter_subset_left).trans closure_ball_subset_closedBall (hcl hx))
  have hPc : ContinuousOn (fun x => fderiv ℝ u (E.symm x)) (closure (D ∩ V)) := fun x hx =>
    (((hu1at _ (hcl2 x hx)).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
      E.symm.continuous.continuousAt).continuousWithinAt
  have hgc : ContinuousOn (fderiv ℝ E.symm) (closure (D ∩ V)) := fun x hx =>
    ((hsymm x ((ball_subset_ball (by norm_num) (hcl2 x hx)))).fderiv_right (m := 1)
      (by norm_num)).continuousAt.continuousWithinAt
  have hggc : ContinuousOn (fderiv ℝ (fderiv ℝ E.symm)) (closure (D ∩ V)) := fun x hx =>
    (((hsymm x ((ball_subset_ball (by norm_num) (hcl2 x hx)))).fderiv_right (m := 1)
      (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hPt : ContinuousOn (fun x => neumannChartC2BilinOfEntries (fun i j => Dij i j (E.symm x)))
      (closure (D ∩ V)) :=
    (continuousOn_neumannChartC2BilinOfEntries (M := Dij) hDc).comp
      E.symm.continuous.continuousOn hcl
  have hQ : ContinuousOn Q (closure (D ∩ V)) := by
    have := neumannChartC2_continuousAdd
    change ContinuousOn (fun x => _ + _) _
    refine ContinuousOn.add (f := fun x =>
      (ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ (fderiv ℝ u (E.symm x))).comp
        (fderiv ℝ (fderiv ℝ E.symm) x)) (g := fun x =>
      ((ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ).flip
        (fderiv ℝ E.symm x)).comp
        ((neumannChartC2BilinOfEntries (fun i j => Dij i j (E.symm x))).comp
          (fderiv ℝ E.symm x))) ?_ ?_
    · exact ((ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ).continuous
        |>.comp_continuousOn hPc).clm_comp hggc
    · exact ((ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ).flip.continuous
        |>.comp_continuousOn hgc).clm_comp (hPt.clm_comp hgc)
  -- The a.e. identification.
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse
    (hD.inter hV).measurableSet E.symm.continuous.continuousOn hE.lipschitzOnWith
    hmaps (fun x _ => E.apply_symm_apply x)
  have hq : Measure.QuasiMeasurePreserving E.symm (volume.restrict (D ∩ V))
      (volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))) :=
    ⟨E.symm.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  refine ⟨V, v, hV, ⟨0, mem_ball_self (by norm_num), h0⟩,
    (image_mono hsmall).trans hregion, hv, hv2, ?_, ⟨Q, hQ, hQeq⟩, ?_⟩
  · filter_upwards [hq.ae hzu, ae_restrict_mem (hD.inter hV).measurableSet] with x hx hxV
    change z (neumannLocalizeMap c a ρ (E.symm x)) = u (E.symm x) at hx
    rwa [hEq (hsmall (hinv x hxV.2)), E.apply_symm_apply] at hx
  · intro x hx
    let y := E.symm x
    have hy : y ∈ ball 0 (1 / 4 * (3 / 8) : ℝ) := hinv x hx.2
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

/-- Local ambient C² regularity up to the boundary at a point of a specified
smooth boundary chart: the representative is C¹ near the point, C² on the part
inside the domain, its Hessian extends continuously to the closure of that
part, and the classical Neumann condition holds with the chart's outward unit
normal. -/
theorem IsWeakNeumannSolution.exists_boundary_chart_c2_conormal
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
      ContDiffOn ℝ 2 v (D ∩ V) ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      (∃ Q : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ,
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  obtain ⟨ρ, hρ, h0, -, -, hreg, hregion, hupper, hlower, hface, -, E, C, K,
    hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap hψ hp hpc
  have hH1 := neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
    ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  have hweak := fun φ hφ hcφ hsφ =>
    hz.normal_chart_test_eq hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      (φ := φ) hφ hcφ hsφ
  obtain ⟨u, hu, hu2, hzu, -, hent, hcon⟩ :=
    neumannChartC2_flat_representative c hψ _ hρ hreg hfs hhs hH1 hweak
  exact neumannChartC2_pushforward_representative hD c hψ _ hρ h0 E hE hEq hreg
    hregion hupper hlower hface hu hu2 hzu hent hcon

/-- Local ambient C² regularity up to the boundary with the chart-independent
outward normal of the given smooth domain. The weak equation still uses its
original Lipschitz boundary witness. -/
theorem IsWeakNeumannSolution.exists_boundary_c2_conormal
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (hGs : HasSmoothBoundary D)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {p : AmbientSpace} (hp : p ∈ frontier D) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 v V ∧ ContDiffOn ℝ 2 v (D ∩ V) ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      (∃ Q : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ,
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V,
        fderiv ℝ v x (hGs.hasC1Boundary.outwardNormal x) = h₀ x := by
  obtain ⟨c, hc, hpc, hψ⟩ := hGs p hp
  obtain ⟨V, v, hV, hpV, hVc, hv, hv2, hzv, hQ, hn⟩ :=
    hz.exists_boundary_chart_c2_conormal hf hh hfs hhs hc hψ hp hpc
  refine ⟨V, v, hV, hpV, hv, hv2, hzv, hQ, fun x hx => ?_⟩
  rw [hGs.hasC1Boundary.outwardNormal_eq_chart hc hx.1 (hVc hx.2)]
  exact hn x hx

end LiquidDrop
