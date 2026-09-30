module

public import NoCompromise.Elliptic.NeumannChartC2Ambient
public import NoCompromise.Elliptic.NeumannChartC2Holder
public import NoCompromise.Elliptic.BoundaryC2aCoverNorm
public import NoCompromise.Elliptic.BoundaryNeumannC2InhomFinite
public import NoCompromise.Elliptic.BoundaryNeumannC2HolderAlgebra

@[expose] public section

/-!
# Hölder bounds for the ambient Hessian in a smooth chart (`thm:boundary-neumann`)

The flat C²,α representative is pushed forward by the smooth inverse of the normal chart.
On `D ∩ B(p, δ)`, for a small ball around the boundary point, the chain-rule expression of the
ambient Hessian is a sum of bilinear combinations of α-Hölder factors: the flat gradient and
Hessian composed with the Lipschitz inverse chart, and the first and second derivatives of the
inverse chart. Hence the ambient Hessian is bounded and α-Hölder there.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Pointwise bounds give a finite Hölder norm. -/
lemma neumannAmbient_holder_of_pointwise {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α A B : ℝ} {f : E → F} {U : Set E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ U, ‖f x‖ ≤ A) (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ α) :
    HasFiniteHolderNormOn α f U := by
  refine HasFiniteHolderNormOn.of_bounds hA hB hf fun x hx y hy => ?_
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, norm_zero, zero_div]
    exact hB
  · have hpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [div_le_iff₀ hpos]
    exact hh x hx y hy

lemma neumannAmbient_bilinOfEntries_apply (M : Fin 3 → Fin 3 → ℝ) (x y : AmbientSpace) :
    neumannChartC2BilinOfEntries M x y = ∑ i, ∑ j, M i j * (x i * y j) := by
  simp [neumannChartC2BilinOfEntries, smul_eq_mul]

lemma neumannAmbient_bilinOfEntries_norm_le (M : Fin 3 → Fin 3 → ℝ) :
    ‖neumannChartC2BilinOfEntries M‖ ≤ ∑ i, ∑ j, |M i j| := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) fun x y => ?_
  rw [neumannAmbient_bilinOfEntries_apply, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hx : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hy : |y j| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j
  rw [abs_mul, abs_mul]
  have := abs_nonneg (M i j)
  have := abs_nonneg (x i)
  have := abs_nonneg (y j)
  calc |M i j| * (|x i| * |y j|) ≤ |M i j| * (‖x‖ * ‖y‖) := by gcongr
    _ = |M i j| * ‖x‖ * ‖y‖ := by ring

lemma neumannAmbient_bilinOfEntries_sub (M N : Fin 3 → Fin 3 → ℝ) :
    neumannChartC2BilinOfEntries M - neumannChartC2BilinOfEntries N =
      neumannChartC2BilinOfEntries (fun i j => M i j - N i j) := by
  rw [neumannChartC2_bilin_eq_ofEntries
    (neumannChartC2BilinOfEntries M - neumannChartC2BilinOfEntries N)]
  congr 1
  funext i j
  rw [sub_apply, sub_apply,
    neumannChartC2BilinOfEntries_single, neumannChartC2BilinOfEntries_single]

/-- **Ambient C²,α in a smooth chart.** The flat C² representative with bounded, α-Hölder
Hessian entries is pushed forward by the inverse chart. On `D ∩ B(p, δ)` for a small ball
around the boundary point, the ambient Hessian extends continuously to the closure and has a
finite α-Hölder norm; the classical Neumann condition holds on the boundary. -/
theorem neumannChartC2_pushforward_holder {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
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
    (hent : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ i j : Fin 3, ∃ Dij : AmbientSpace → ℝ,
      ContinuousOn Dij (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
      EqOn Dij (fun x => boundaryNeumannC2Entry u x i j)
        (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
      (∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))), |Dij x| ≤ Cb) ∧
      ∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))),
        ∀ y ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))), |Dij x - Dij y| ≤ Cb * dist x y ^ α)
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
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V) ∧
        HasFiniteHolderNormOn α Q (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  obtain ⟨Cb, hCb, hent⟩ := hent
  let Θ := neumannLocalizeMap c a ρ
  let V := Θ '' ball 0 (1 / 4 * (3 / 8) : ℝ)
  let v := u ∘ E.symm
  have hΘ : ContDiff ℝ 2 Θ :=
    (smooth_neumannLocalizeMap c hψ a ρ).of_le
      (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by norm_num)
  have hΘ3 : ContDiff ℝ 3 Θ :=
    (smooth_neumannLocalizeMap c hψ a ρ).of_le
      (by simp : (3 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
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
  have hsymm3 (x : AmbientSpace) (hx : E.symm x ∈ ball 0 2) : ContDiffAt ℝ 3 E.symm x := by
    have hnear : Θ =ᶠ[𝓝 (E.symm x)] E :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => hEq hy)
    obtain ⟨L, hL⟩ := hreg _ hx
    have hd : HasFDerivAt E (L : AmbientSpace →L[ℝ] AmbientSpace) (E.symm x) := by
      rw [hL]
      exact (hΘ1.differentiable one_ne_zero _).hasFDerivAt.congr_of_eventuallyEq hnear.symm
    exact E.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) hd
      (hΘ3.contDiffAt.congr_of_eventuallyEq hnear.symm)
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
  choose Dij hDc hDe hDb hDh using hent
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
  have hae : z =ᵐ[volume.restrict (D ∩ V)] v := by
    filter_upwards [hq.ae hzu, ae_restrict_mem (hD.inter hV).measurableSet] with x hx hxV
    change z (neumannLocalizeMap c a ρ (E.symm x)) = u (E.symm x) at hx
    rwa [hEq (hsmall (hinv x hxV.2)), E.apply_symm_apply] at hx
  have hneu : ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
    intro x hx
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
  -- Hölder bounds on a small convex ball around `p`.
  have hpV : p ∈ V := ⟨0, mem_ball_self (by norm_num), h0⟩
  obtain ⟨δ, hδ, hδV⟩ : ∃ δ > 0, closedBall p δ ⊆ V :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hpV)
  have hKc : IsCompact (closedBall p δ) := isCompact_closedBall p δ
  have hKv : Convex ℝ (closedBall p δ) := convex_closedBall p δ
  have hs3 : ContDiffOn ℝ 3 E.symm V := fun x hx =>
    (hsymm3 x (hsmall (hinv x hx))).contDiffWithinAt
  have hg1 : ContDiffOn ℝ 2 (fderiv ℝ E.symm) V := hs3.fderiv_of_isOpen hV (by norm_num)
  have hg2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ E.symm)) V :=
    hg1.fderiv_of_isOpen hV (by norm_num)
  have hH1 : HasFiniteHolderNormOn α (fderiv ℝ E.symm) (closedBall p δ) :=
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα.le hα1 hKc hKv hV hδV
      (hg1.of_le (by norm_num))
  have hH2 : HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ E.symm)) (closedBall p δ) :=
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα.le hα1 hKc hKv hV hδV hg2
  have hLip : HasFiniteHolderNormOn 1 E.symm (closedBall p δ) :=
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn zero_le_one le_rfl hKc hKv hV hδV
      (hs3.of_le (by norm_num))
  set S := D ∩ ball p δ with hS_def
  have hSK : S ⊆ closedBall p δ := fun x hx => ball_subset_closedBall hx.2
  have hSV : S ⊆ D ∩ V := fun x hx => ⟨hx.1, hδV (ball_subset_closedBall hx.2)⟩
  set L := max (holderSeminorm 1 E.symm (closedBall p δ)) 1 with hL_def
  have hL1 : 1 ≤ L := le_max_right _ _
  have hEL : ∀ x ∈ S, ∀ y ∈ S, ‖E.symm x - E.symm y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have h1 := hLip.nondiv_norm_sub_le (hSK hx) (hSK hy)
    rw [Real.rpow_one] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hmS : MapsTo E.symm S (boundaryHalfBall (1 / 4 * (3 / 8))) := fun x hx => hmaps (hSV hx)
  have hmS' : MapsTo E.symm S (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) :=
    fun x hx => subset_closure (hmS hx)
  -- the flat gradient is bounded and Lipschitz on the flat half ball
  have hdiam : ∀ x ∈ boundaryHalfBall (1 / 4 * (3 / 8) : ℝ),
      ∀ y ∈ boundaryHalfBall (1 / 4 * (3 / 8) : ℝ), ‖x - y‖ ≤ 1 := by
    intro x hx y hy
    have h1 := mem_ball_zero_iff.mp hx.1
    have h2 := mem_ball_zero_iff.mp hy.1
    linarith [norm_sub_le x y]
  obtain ⟨Bu, hBu⟩ :=
    (isCompact_closedBall (0 : AmbientSpace) (1 / 4 * (3 / 8))).exists_bound_of_continuousOn
    ((hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono
      (closedBall_subset_ball (by norm_num)))
  have hlip := boundary_c2a_fderiv_lipschitz_of_entry (isOpen_boundaryHalfBall _)
    (convex_boundaryHalfBall _) hu2 hCb
    (fun x hx i j => by
      have h := hDb i j x (subset_closure hx)
      rwa [hDe i j hx] at h)
  have hDu : HasFiniteHolderNormOn α (fderiv ℝ u) (boundaryHalfBall (1 / 4 * (3 / 8))) := by
    refine neumannAmbient_holder_of_pointwise (A := max Bu 0) (B := 9 * Cb) (le_max_right _ _)
      (by positivity) (fun x hx => (hBu x (ball_subset_closedBall hx.1)).trans
        (le_max_left _ _)) fun x hx y hy => (hlip x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one (norm_nonneg _)
      (hdiam x hx y hy) hα1) (by positivity)
  obtain ⟨hDuE, -⟩ := nondiv_holder_comp_expansion hα.le hα1 hL1 hDu hmS hEL
  -- the flat Hessian as a bilinear form
  have hBil : HasFiniteHolderNormOn α
      (fun y => neumannChartC2BilinOfEntries (fun i j => Dij i j y))
      (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) := by
    refine neumannAmbient_holder_of_pointwise (A := 9 * Cb) (B := 9 * Cb) (by positivity)
      (by positivity) (fun y hy => ?_) fun y hy y' hy' => ?_
    · refine (neumannAmbient_bilinOfEntries_norm_le _).trans ?_
      calc ∑ i, ∑ j, |Dij i j y| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, Cb :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hDb i j y hy
        _ = 9 * Cb := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]; ring
    · rw [neumannAmbient_bilinOfEntries_sub]
      refine (neumannAmbient_bilinOfEntries_norm_le _).trans ?_
      calc ∑ i, ∑ j, |Dij i j y - Dij i j y'| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, Cb * ‖y - y'‖ ^ α :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              rw [← dist_eq_norm]; exact hDh i j y hy y' hy'
        _ = 9 * Cb * ‖y - y'‖ ^ α := by simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨hBilE, -⟩ := nondiv_holder_comp_expansion hα.le hα1 hL1 hBil hmS' hEL
  obtain ⟨hA1, -⟩ := schauder_holder_mono hH1 hSK
  obtain ⟨hA2, -⟩ := schauder_holder_mono hH2 hSK
  let B1 : (AmbientSpace →L[ℝ] ℝ) →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] AmbientSpace)
      →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ AmbientSpace (AmbientSpace →L[ℝ] AmbientSpace)
      (AmbientSpace →L[ℝ] ℝ)).comp (ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ)
  let B2 : (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace)
      →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace (AmbientSpace →L[ℝ] ℝ)
  let B3 : (AmbientSpace →L[ℝ] AmbientSpace) →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ)
      →L[ℝ] (AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ AmbientSpace (AmbientSpace →L[ℝ] ℝ)
      (AmbientSpace →L[ℝ] ℝ)).comp (ContinuousLinearMap.compL ℝ AmbientSpace AmbientSpace ℝ).flip
  have hT1 := (nondiv_holder_bilinear hDuE hA2 B1).1
  have hT2 := (nondiv_holder_bilinear hBilE hA1 B2).1
  have hT3 := (nondiv_holder_bilinear hA1 hT2 B3).1
  have hsum := (schauder_holder_add hT1 hT3).1
  have hQh : HasFiniteHolderNormOn α Q S := by
    refine (boundaryNeumann_holder_congr hsum fun x _ => ?_).1
    rfl
  refine ⟨ball p δ, v, isOpen_ball, mem_ball_self hδ,
    ((ball_subset_closedBall.trans hδV).trans ((image_mono hsmall).trans hregion)),
    hv.mono (ball_subset_closedBall.trans hδV), hv2.mono hSV,
    ae_restrict_of_ae_restrict_of_subset hSV hae,
    ⟨Q, hQ.mono (closure_mono hSV), hQeq.mono hSV, hQh⟩,
    fun x hx => hneu x ⟨hx.1, hδV (ball_subset_closedBall hx.2)⟩⟩

/-- **Local ambient C²,α up to the boundary at a point of a smooth chart.** For a weak Neumann
solution with smooth data, near a boundary point the representative is C¹, C² inside the
domain, its Hessian extends continuously to the closure and is bounded and α-Hölder on the part
inside the domain, and the classical Neumann condition holds with the chart outward normal. -/
theorem IsWeakNeumannSolution.exists_boundary_chart_c2_holder
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
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
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V) ∧
        HasFiniteHolderNormOn α Q (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V, fderiv ℝ v x (c.outwardNormal x) = h₀ x := by
  obtain ⟨ρ, hρ, h0, -, -, hreg, hregion, hupper, hlower, hface, -, E, C, K,
    hE, hEi, hEq⟩ := hc.exists_neumannLocalizeMap hψ hp hpc
  have hH1 := neumannLocalize_hasH1GradientOn hD z E hE hEi hEq
    ((image_mono (boundaryHalfBall_mono (by norm_num : (1 : ℝ) ≤ 2))).trans hupper)
  have hweak := fun φ hφ hcφ hsφ =>
    hz.normal_chart_test_eq hf hh hc hψ _ hρ E hEq hreg hregion hupper hlower hface
      (φ := φ) hφ hcφ hsφ
  obtain ⟨u, hu, hu2, hzu, -, ⟨Cb, hCb, hent⟩, hcon⟩ :=
    neumannChartC2Holder_flat_representative hα hα1 c hψ _ hρ hreg hfs hhs hH1 hweak
  exact neumannChartC2_pushforward_holder hα hα1.le hD c hψ _ hρ h0 E hE hEq hreg
    hregion hupper hlower hface hu hu2 hzu ⟨Cb, hCb.le, hent⟩ hcon

/-- The same with the chart-independent outward normal of a smooth domain. -/
theorem IsWeakNeumannSolution.exists_boundary_c2_holder
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
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
        ContinuousOn Q (closure (D ∩ V)) ∧ EqOn Q (fderiv ℝ (fderiv ℝ v)) (D ∩ V) ∧
        HasFiniteHolderNormOn α Q (D ∩ V)) ∧
      ∀ x ∈ frontier D ∩ V,
        fderiv ℝ v x (hGs.hasC1Boundary.outwardNormal x) = h₀ x := by
  obtain ⟨c, hc, hpc, hψ⟩ := hGs p hp
  obtain ⟨V, v, hV, hpV, hVc, hv, hv2, hzv, hQ, hn⟩ :=
    hz.exists_boundary_chart_c2_holder hα hα1 hf hh hfs hhs hc hψ hp hpc
  refine ⟨V, v, hV, hpV, hv, hv2, hzv, hQ, fun x hx => ?_⟩
  rw [hGs.hasC1Boundary.outwardNormal_eq_chart hc hx.1 (hVc hx.2)]
  exact hn x hx

end LiquidDrop
