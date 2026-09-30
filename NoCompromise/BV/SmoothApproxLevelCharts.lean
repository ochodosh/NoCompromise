module

public import NoCompromise.BV.SmoothApproxBoundary
public import NoCompromise.BV.LineDistribution

@[expose] public section

/-!
# One-sided smooth charts at regular scalar levels

Inverse-function level heights retain all derivatives. A negative final
partial derivative makes vertical slices strictly decreasing, identifying the
superlevel side of the graph without any geometric boundary premise.
-/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma ScalarCoareaChart.contDiffOn_inverse_smooth {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (d : ScalarCoareaChart u)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiffOn ℝ (⊤ : ℕ∞) d.chart.symm d.chart.target := by
  intro y hy
  have hx := d.chart.map_target hy
  apply (d.chart.contDiffAt_symm hy (d.hasFDerivAt_forward hx) ?_).contDiffWithinAt
  rw [d.forward_eq]
  exact (contDiffOn_coareaCoordinateMap hu.contDiffOn).contDiffAt
    (d.chart.open_source.mem_nhds hx)

lemma ScalarCoareaChart.contDiffOn_levelHeight_smooth {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (d : ScalarCoareaChart u)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (d.levelHeight t) (d.levelDomain t) := by
  change ContDiffOn ℝ (⊤ : ℕ∞)
    ((EuclideanSpace.proj (Fin.last k) : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ) ∘
      d.chart.symm ∘ fun z => graphAppendN z t) (d.levelDomain t)
  exact (EuclideanSpace.proj (Fin.last k)).contDiff.comp_contDiffOn
    ((d.contDiffOn_inverse_smooth hu).comp (contDiff_graphAppendN t).contDiffOn (fun _ hz => hz))

lemma convex_verticalSlice_ball {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1)))
    (R : ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    Convex ℝ {s : ℝ | graphAppendN y s ∈ ball x R} := by
  have hh := ((convex_ball x R).translate_preimage_right (graphBaseN k y)).linear_preimage
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (Fin.last k) 1)).toLinearMap
  exact hh

lemma deriv_verticalSlice_eq {k : ℕ} {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hu : Differentiable ℝ u) (y : EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    deriv (fun q => u (graphAppendN y q)) s = gradient u (graphAppendN y s) (Fin.last k) := by
  have hline : HasDerivAt (fun q : ℝ => graphAppendN y q)
      (EuclideanSpace.single (Fin.last k) 1) s := by
    simpa only [graphAppendN, zero_add, Pi.add_apply, id_eq, one_smul] using!
      (hasDerivAt_const s (graphBaseN k y)).add
        ((hasDerivAt_id s).smul_const (EuclideanSpace.single (Fin.last k) 1))
  have hh := (hu _).hasFDerivAt.comp_hasDerivAt s hline
  change deriv (u ∘ fun q => graphAppendN y q) s = _
  rw [hh.deriv]
  exact (gradient_apply_eq_fderiv_single u _ _).symm

/-- A negative final partial produces the actual one-sided superlevel graph
on an open neighborhood, with a height smooth on its open base. -/
theorem exists_smooth_superlevel_graph_of_last_neg {u : AmbientSpace → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {x : AmbientSpace}
    (hx : gradient u x (Fin.last 2) < 0) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ)
      (U : Set (EuclideanSpace ℝ (Fin 2))) (W : Set AmbientSpace),
      IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ graphProjectionN 2 x ∈ U ∧
      IsOpen W ∧ x ∈ W ∧
      ∀ z ∈ W, u x < u z ↔ z (Fin.last 2) < f (graphProjectionN 2 z) := by
  have hg : Continuous (fun z => gradient u z (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2)).continuous.comp
      (continuous_gradient_of_contDiff (hu.of_le (by simp)))
  have hV : IsOpen {z | gradient u z (Fin.last 2) < 0} := isOpen_lt hg continuous_const
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨d, hxd, hdb⟩ := exists_scalarCoareaChart isOpen_ball
    ((hu.of_le (by simp)).contDiffOn) (mem_ball_self hR) hx.ne
  have hxD : graphProjectionN 2 x ∈ d.levelDomain (u x) := by
    change graphAppendN (graphProjectionN 2 x) (u x) ∈ d.chart.target
    rw [← coareaCoordinateMap, ← d.forward_eq]
    exact d.chart.map_source hxd
  let W : Set AmbientSpace := ball x R ∩ (graphProjectionN 2) ⁻¹' d.levelDomain (u x)
  have hW : IsOpen W := isOpen_ball.inter
    ((d.isOpen_levelDomain (u x)).preimage (graphProjectionN 2).continuous)
  refine ⟨d.levelHeight (u x), d.levelDomain (u x), W, d.isOpen_levelDomain _,
    d.contDiffOn_levelHeight_smooth hu _, hxD, hW, ⟨mem_ball_self hR, hxD⟩, ?_⟩
  intro z hz
  let y := graphProjectionN 2 z
  let I : Set ℝ := {s | graphAppendN y s ∈ ball x R}
  have hy : y ∈ d.levelDomain (u x) := hz.2
  have hgraph : graphAppendN y (d.levelHeight (u x) y) ∈ ball x R := by
    change graphMapN (d.levelHeight (u x)) y ∈ ball x R
    rw [← d.inverse_eq_graphMapN hy]
    exact hdb (d.chart.map_target hy)
  have hstrict : StrictAntiOn (fun s => u (graphAppendN y s)) I := by
    apply strictAntiOn_of_deriv_neg (convex_verticalSlice_ball x R y)
      (hu.continuous.comp (by unfold graphAppendN; fun_prop)).continuousOn
    intro s hs
    change deriv (fun q => u (graphAppendN y q)) s < 0
    rw [deriv_verticalSlice_eq (hu.differentiable (by simp))]
    exact hRV ((interior_subset : interior I ⊆ I) hs)
  have hzI : z (Fin.last 2) ∈ I := by
    dsimp only [I, y, mem_ofPred_eq]
    rw [graphAppendN_projection]
    exact hz.1
  have hgI : d.levelHeight (u x) y ∈ I := hgraph
  have hlevel : u (graphAppendN y (d.levelHeight (u x) y)) = u x := by
    change u (graphMapN (d.levelHeight (u x)) y) = u x
    rw [← d.inverse_eq_graphMapN hy]
    exact d.u_inverse_eq hy
  have heq := hstrict.lt_iff_gt hgI hzI
  rw [hlevel] at heq
  simpa only [y, graphAppendN_projection] using heq

lemma exists_frame_with_negative_last_gradient {u : AmbientSpace → ℝ}
    {x : AmbientSpace} (hu : DifferentiableAt ℝ u x) (hx : gradient u x ≠ 0) :
    ∃ e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace,
      gradient (u ∘ e) (e.symm x) (Fin.last 2) < 0 := by
  let ν : AmbientSpace := -(‖gradient u x‖⁻¹ • gradient u x)
  have hg : 0 < ‖gradient u x‖ := norm_pos_iff.mpr hx
  have hν : ‖ν‖ = 1 := by
    dsimp only [ν]
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hg.le),
      inv_mul_cancel₀ hg.ne']
  obtain ⟨e, he⟩ := exists_line_direction_frame hν
  refine ⟨e, ?_⟩
  have hd : HasFDerivAt (u ∘ e)
      ((fderiv ℝ u x).comp e.toContinuousLinearEquiv.toContinuousLinearMap) (e.symm x) := by
    have hdu : HasFDerivAt u (fderiv ℝ u x) (e (e.symm x)) := by
      simpa only [e.apply_symm_apply] using hu.hasFDerivAt
    exact hdu.comp (e.symm x) e.toContinuousLinearEquiv.hasFDerivAt
  rw [gradient_apply_eq_fderiv_single, hd.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ u x (e (EuclideanSpace.single (Fin.last 2) 1)) < 0
  rw [he, ← inner_gradient_left]
  change inner ℝ (gradient u x) (-(‖gradient u x‖⁻¹ • gradient u x)) < 0
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have hh : ‖gradient u x‖⁻¹ * ‖gradient u x‖ ^ 2 = ‖gradient u x‖ := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul]
  rw [hh]
  exact neg_neg_of_pos hg

/-- Every regular level of a globally smooth scalar function bounds a genuine
smooth one-sided domain, in the fixed rigid graph-chart convention. -/
theorem hasSmoothBoundary_superlevel_of_regular {u : AmbientSpace → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {t : ℝ}
    (ht : ∀ x, u x = t → gradient u x ≠ 0) : HasSmoothBoundary {x | t < u x} := by
  apply hasSmoothBoundary_of_local_graphs
  intro x hx
  have hux : u x = t := (frontier_lt_subset_eq continuous_const hu.continuous hx).symm
  obtain ⟨e, he⟩ := exists_frame_with_negative_last_gradient
    (hu.differentiable (by simp) x) (ht x hux)
  obtain ⟨f, U, W, hU, hf, hxU, hW, hxW, hgraph⟩ :=
    exists_smooth_superlevel_graph_of_last_neg
      (hu.comp e.toContinuousLinearEquiv.contDiff) he
  refine ⟨e.toAffineIsometryEquiv, f, U, e '' W, hU, hf, hxU,
    e.toHomeomorph.isOpenMap _ hW, ⟨e.symm x, hxW, e.apply_symm_apply x⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change (t < u (e z)) ↔
    e.symm (e z) (Fin.last 2) < f (graphProjectionN 2 (e.symm (e z)))
  have hh := hgraph z hz
  change (u (e (e.symm x)) < u (e z)) ↔
    z (Fin.last 2) < f (graphProjectionN 2 z) at hh
  simpa only [e.apply_symm_apply, e.symm_apply_apply, hux] using hh

end LiquidDrop
