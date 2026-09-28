import NoCompromise.Stationary.Defs
import NoCompromise.Stationary.EulerLagrange
import Mathlib.LinearAlgebra.PID
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Mean curvature of a boundary chart

Towards blueprint `cor:EL-pointwise`: for a boundary chart with `C²` height, the
intrinsic mean curvature (`conv:curvature`, outward normal) of the boundary at a
chart point equals minus the divergence of the planar flux `∇f / √(1+|∇f|²)`.
-/

noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace ContDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A field of unit length near `p` has derivative orthogonal to itself at `p`. -/
lemma inner_fderiv_self_eq_zero_of_unit {n : E₃ → E₃} {p : E₃}
    (hn : DifferentiableAt ℝ n p) (hunit : ∀ᶠ z in 𝓝 p, ‖n z‖ = 1) (v : E₃) :
    inner ℝ (n p) (fderiv ℝ n p v) = 0 := by
  have hd := hn.hasFDerivAt.inner ℝ hn.hasFDerivAt
  have hconst : (fun z => inner ℝ (n z) (n z)) =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
    filter_upwards [hunit] with z hz
    rw [real_inner_self_eq_norm_sq, hz, one_pow]
  have h0 : HasFDerivAt (fun z => inner ℝ (n z) (n z)) (0 : E₃ →L[ℝ] ℝ) p :=
    (hasFDerivAt_const (1 : ℝ) p).congr_of_eventuallyEq hconst
  have hv := congrArg (fun L : E₃ →L[ℝ] ℝ => L v) (hd.unique h0)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, zero_apply] at hv
  rw [real_inner_comm (n p) (fderiv ℝ n p v)] at hv
  linarith

/-- For a unit normal field whose normal line is the orthogonal complement of the
tangent plane, the intrinsic mean curvature is the full ambient trace. -/
theorem meanCurvature_eq_trace_fderiv {S : Set E₃} {n : E₃ → E₃} {p : E₃}
    (hT : tangentPlane S p = (ℝ ∙ n p)ᗮ) (hn : DifferentiableAt ℝ n p)
    (hunit : ∀ᶠ z in 𝓝 p, ‖n z‖ = 1) :
    meanCurvature S n p =
      LinearMap.trace ℝ E₃ ((fderiv ℝ n p : E₃ →L[ℝ] E₃) : E₃ →ₗ[ℝ] E₃) := by
  have hmem : ∀ v, (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) v ∈ tangentPlane S p := by
    intro v
    rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_fderiv_self_eq_zero_of_unit hn hunit v
  rw [← LinearMap.trace_restrict_eq_of_forall_mem (tangentPlane S p) _ hmem]
  unfold meanCurvature
  congr 1
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  change ((tangentPlane S p).orthogonalProjectionOnto (fderiv ℝ n p X) : E₃) = fderiv ℝ n p X
  exact (tangentPlane S p).starProjection_eq_self_iff.mpr (hmem X)

/-- The planar flux map `q ↦ q / √(1+|q|²)`. -/
def graphFluxMap (q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt (1 + ‖q‖ ^ 2))⁻¹ • q

/-- The planar flux `∇f / √(1+|∇f|²)` of the graph mean-curvature operator. -/
def graphFlux (f : EuclideanSpace ℝ (Fin 2) → ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  graphFluxMap (gradient f y)

private lemma contDiff_sqrt_one_add_norm_sq {k : ℕ} :
    ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin k) => Real.sqrt (1 + ‖q‖ ^ 2)) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun q =>
    (by positivity : (1 + ‖q‖ ^ 2 : ℝ) ≠ 0)

lemma contDiff_graphFluxMap : ContDiff ℝ ∞ graphFluxMap :=
  (contDiff_sqrt_one_add_norm_sq.inv fun q =>
    (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2)).ne').smul contDiff_id

lemma contDiff_smoothGraphUnitNormal_two : ContDiff ℝ ∞ (@smoothGraphUnitNormal 2) := by
  unfold smoothGraphUnitNormal graphAppendN
  exact (contDiff_sqrt_one_add_norm_sq.inv fun q =>
    (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2)).ne').smul
      (((graphBaseN 2).contDiff.comp contDiff_neg).add contDiff_const)

lemma graphProjectionN_smoothGraphUnitNormal (q : EuclideanSpace ℝ (Fin 2)) :
    graphProjectionN 2 (smoothGraphUnitNormal q) = -graphFluxMap q := by
  rw [smoothGraphUnitNormal, map_smul, graphProjectionN_append, graphFluxMap, smul_neg]

lemma contDiff_gradient_of_contDiff_two {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp
    (hf.fderiv_right (m := 1) (by norm_num))

/-- The trace of the derivative of the vertically constant graph normal is minus
the planar divergence of the graph flux. -/
theorem trace_fderiv_smoothSubgraphNormal {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 2 f) (w : EuclideanSpace ℝ (Fin 3)) :
    LinearMap.trace ℝ _ ((fderiv ℝ (smoothSubgraphNormal f) w :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
          EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) =
      -LinearMap.trace ℝ _ ((fderiv ℝ (graphFlux f) (graphProjectionN 2 w) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  set y := graphProjectionN 2 w
  set q := gradient f y
  have hgrad : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) y) y :=
    ((contDiff_gradient_of_contDiff_two hf).differentiable one_ne_zero y).hasFDerivAt
  have hG : HasFDerivAt (@smoothGraphUnitNormal 2) (fderiv ℝ (@smoothGraphUnitNormal 2) q) q :=
    (contDiff_smoothGraphUnitNormal_two.differentiable (by simp) q).hasFDerivAt
  have hM : HasFDerivAt graphFluxMap (fderiv ℝ graphFluxMap q) q :=
    (contDiff_graphFluxMap.differentiable (by simp) q).hasFDerivAt
  have hπG : HasFDerivAt (fun r => graphProjectionN 2 (smoothGraphUnitNormal r))
      ((graphProjectionN 2).comp (fderiv ℝ (@smoothGraphUnitNormal 2) q)) q :=
    (graphProjectionN 2).hasFDerivAt.comp q hG
  have hfun : (fun r => graphProjectionN 2 (smoothGraphUnitNormal r)) =
      fun r => -graphFluxMap r := by
    funext r
    exact graphProjectionN_smoothGraphUnitNormal r
  rw [hfun] at hπG
  have hπG' := hπG.unique hM.neg
  have hN : HasFDerivAt (smoothSubgraphNormal f)
      ((fderiv ℝ (@smoothGraphUnitNormal 2) q).comp
        ((fderiv ℝ (gradient f) y).comp (graphProjectionN 2))) w := by
    have h1 := hgrad.comp w (graphProjectionN 2).hasFDerivAt
    exact hG.comp w h1
  have hF : HasFDerivAt (graphFlux f) ((fderiv ℝ graphFluxMap q).comp
      (fderiv ℝ (gradient f) y)) y :=
    hM.comp y hgrad
  rw [hN.fderiv, hF.fderiv, ← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp,
    ← ContinuousLinearMap.comp_assoc, hπG', ContinuousLinearMap.neg_comp,
    ContinuousLinearMap.toLinearMap_neg, map_neg]

/-- Rigid placement does not change the trace of the normal derivative. -/
theorem C1BoundaryChart.trace_fderiv_outwardNormal (c : C1BoundaryChart)
    (hf : ContDiff ℝ 2 c.height) (z : AmbientSpace) :
    LinearMap.trace ℝ AmbientSpace ((fderiv ℝ c.outwardNormal z :
        AmbientSpace →L[ℝ] AmbientSpace) : AmbientSpace →ₗ[ℝ] AmbientSpace) =
      LinearMap.trace ℝ AmbientSpace ((fderiv ℝ (smoothSubgraphNormal c.height)
        (c.placement.symm z) : AmbientSpace →L[ℝ] AmbientSpace) :
          AmbientSpace →ₗ[ℝ] AmbientSpace) := by
  set L := c.placement.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  set M := c.placement.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hNd : DifferentiableAt ℝ (smoothSubgraphNormal c.height) (c.placement.symm z) := by
    have h1 : ContDiff ℝ 1 (smoothSubgraphNormal c.height) :=
      (contDiff_smoothGraphUnitNormal_two.of_le (by simp)).comp
        ((contDiff_gradient_of_contDiff_two hf).comp (graphProjectionN 2).contDiff)
    exact h1.differentiable one_ne_zero _
  have hout : HasFDerivAt c.outwardNormal
      (L.comp ((fderiv ℝ (smoothSubgraphNormal c.height) (c.placement.symm z)).comp M)) z :=
    L.hasFDerivAt.comp z (hNd.hasFDerivAt.comp z (hasFDerivAt_rigidPlacement c.placement.symm z))
  have hML : M.comp L = ContinuousLinearMap.id ℝ AmbientSpace := by
    have h1 : HasFDerivAt (fun x => c.placement.symm (c.placement x)) (M.comp L) 0 :=
      (hasFDerivAt_rigidPlacement c.placement.symm (c.placement 0)).comp 0
        (hasFDerivAt_rigidPlacement c.placement 0)
    have h2 : (fun x => c.placement.symm (c.placement x)) = id := by
      funext x
      exact c.placement.symm_apply_apply x
    rw [h2] at h1
    exact h1.unique (hasFDerivAt_id 0)
  rw [hout.fderiv, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_assoc, hML,
    ContinuousLinearMap.comp_id]

private lemma C1BoundaryChart.placement_linear_symm (c : C1BoundaryChart) (v : AmbientSpace) :
    c.placement.linearIsometryEquiv (c.placement.symm.linearIsometryEquiv v) = v := by
  set L := c.placement.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  set M := c.placement.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h1 : HasFDerivAt (fun x => c.placement (c.placement.symm x)) (L.comp M) 0 :=
    (hasFDerivAt_rigidPlacement c.placement (c.placement.symm 0)).comp 0
      (hasFDerivAt_rigidPlacement c.placement.symm 0)
  have h2 : (fun x => c.placement (c.placement.symm x)) = id := by
    funext x
    exact c.placement.apply_symm_apply x
  rw [h2] at h1
  have h3 := congrArg (fun T : AmbientSpace →L[ℝ] AmbientSpace => T v)
    (h1.unique (hasFDerivAt_id 0))
  simpa [L, M] using h3

/-- In a `C²` boundary chart the tangent plane of the boundary is the orthogonal
complement of the chart's outward normal. -/
theorem C1BoundaryChart.IsChartFor.tangentPlane_frontier_eq {c : C1BoundaryChart}
    {Ω : Set AmbientSpace} (hc : c.IsChartFor Ω) (hf : ContDiff ℝ 2 c.height)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region) :
    tangentPlane (frontier Ω) p = (ℝ ∙ c.outwardNormal p)ᗮ := by
  let φ : AmbientSpace → ℝ := fun z => smoothGraphDefining c.height (c.placement.symm z)
  have hφc : ContDiff ℝ 2 φ :=
    (contDiff_smoothGraphDefining hf).comp
      c.placement.symm.toAffineIsometry.toContinuousAffineMap.contDiff
  have hzero : frontier Ω ∩ c.region = {x ∈ c.region | φ x = 0} := by
    rw [hc.frontier_inter_eq]
    ext z
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨w, ⟨y, rfl⟩, rfl⟩, hr⟩
      refine ⟨hr, ?_⟩
      simp only [φ, c.placement.symm_apply_apply, smoothGraphDefining, graphMapN_last]
      have hy : graphProjectionN 2 (graphMapN c.height y) = y := by
        change graphProjectionN 2 (graphAppendN y (c.height y)) = y
        simp
      rw [hy, sub_self]
    · rintro ⟨hr, h0⟩
      refine ⟨⟨c.placement.symm z, ⟨graphProjectionN 2 (c.placement.symm z), ?_⟩,
        c.placement.apply_symm_apply z⟩, hr⟩
      have h0' : (c.placement.symm z) (Fin.last 2) =
          c.height (graphProjectionN 2 (c.placement.symm z)) := by
        have := h0
        simp only [φ, smoothGraphDefining] at this
        linarith
      change graphAppendN (graphProjectionN 2 (c.placement.symm z))
        (c.height (graphProjectionN 2 (c.placement.symm z))) = _
      rw [← h0', graphAppendN_projection]
  set Q := Real.sqrt (1 + ‖gradient c.height (graphProjectionN 2 (c.placement.symm p))‖ ^ 2)
  have hQ : Q ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hφd : HasFDerivAt φ ((fderiv ℝ (smoothGraphDefining c.height) (c.placement.symm p)).comp
      c.placement.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap) p :=
    ((contDiff_smoothGraphDefining hf).differentiable (by norm_num) _).hasFDerivAt.comp p
      (hasFDerivAt_rigidPlacement c.placement.symm p)
  have hgrad : gradient φ p = Q • c.outwardNormal p := by
    have key : fderiv ℝ φ p = toDual ℝ AmbientSpace (Q • c.outwardNormal p) := by
      rw [hφd.fderiv]
      ext v
      simp only [ContinuousLinearMap.comp_apply, toDual_apply_apply]
      rw [fderiv_smoothGraphDefining hf, inner_smul_left, C1BoundaryChart.outwardNormal]
      simp only [RCLike.conj_to_real]
      congr 1
      conv_rhs => rw [← c.placement_linear_symm v]
      rw [LinearIsometryEquiv.inner_map_map]
      rfl
    rw [gradient, key, LinearIsometryEquiv.symm_apply_apply]
  have hn : c.outwardNormal p ≠ 0 := by
    intro h0
    have := c.norm_outwardNormal p
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [tangentPlane_eq c.isOpen_region hpc (hφc.of_le (by norm_num)).contDiffAt hzero hp
      (by rw [hgrad]; exact smul_ne_zero hQ hn), hgrad,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 Q hQ)]

/-- The mean curvature of the boundary in a `C²` chart is minus the planar
divergence of the graph flux at the chart point. -/
theorem C1BoundaryChart.IsChartFor.meanCurvature_eq_neg_div {c : C1BoundaryChart}
    {Ω : Set AmbientSpace} (hc : c.IsChartFor Ω) (hf : ContDiff ℝ 2 c.height)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region) :
    meanCurvature (frontier Ω) c.outwardNormal p =
      -LinearMap.trace ℝ _ ((fderiv ℝ (graphFlux c.height)
        (graphProjectionN 2 (c.placement.symm p)) :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
            EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  have hnd : DifferentiableAt ℝ c.outwardNormal p := by
    have h1 : ContDiff ℝ 1 (smoothSubgraphNormal c.height) :=
      (contDiff_smoothGraphUnitNormal_two.of_le (by simp)).comp
        ((contDiff_gradient_of_contDiff_two hf).comp (graphProjectionN 2).contDiff)
    have h2 : ContDiff ℝ 1 c.outwardNormal :=
      c.placement.linearIsometryEquiv.contDiff.comp
        (h1.comp c.placement.symm.toAffineIsometry.toContinuousAffineMap.contDiff)
    exact h2.differentiable one_ne_zero p
  rw [meanCurvature_eq_trace_fderiv (hc.tangentPlane_frontier_eq hf hp hpc) hnd
      (Eventually.of_forall fun z => c.norm_outwardNormal z),
    c.trace_fderiv_outwardNormal hf, trace_fderiv_smoothSubgraphNormal hf]

end LiquidDrop
