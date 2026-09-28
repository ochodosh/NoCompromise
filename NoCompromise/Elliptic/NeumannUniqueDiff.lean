import NoCompromise.Elliptic.ClassicalNormal
import NoCompromise.BV.ExteriorGeometry

/-!
# Unique differentiability of the closure of a C¹ domain

At a boundary point, the closure of a C¹ domain is, inside a chart, the image of a closed
half-space under the C¹ shear `u ↦ u + ψ(u') e₃` (whose derivative is onto) followed by the rigid
placement. Hence derivatives within `closure G` are unique at every point of `closure G`. This is
the geometric input needed to evaluate `fderivWithin ℝ v (closure G)` on the boundary.
-/

noncomputable section
open Filter Metric Set
open scoped Topology

namespace LiquidDrop

lemma c1Boundary_graphProjection_last :
    graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) = 0 := by
  ext i
  fin_cases i <;> simp [graphProjectionN_apply]

lemma c1Boundary_shear_hasFDerivAt {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hψ : Differentiable ℝ ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 3) =>
        u + ψ (graphProjectionN 2 u) • EuclideanSpace.single (Fin.last 2) (1 : ℝ))
      (ContinuousLinearMap.id ℝ _ +
        ((fderiv ℝ ψ (graphProjectionN 2 u)).comp (graphProjectionN 2)).smulRight
          (EuclideanSpace.single (Fin.last 2) (1 : ℝ))) u := by
  have h1 := (hψ (graphProjectionN 2 u)).hasFDerivAt.comp u (graphProjectionN 2).hasFDerivAt
  exact (hasFDerivAt_id u).add (h1.smul_const _)

lemma c1Boundary_shear_derivative_surjective (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
    Function.Surjective (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
      (L.comp (graphProjectionN 2)).smulRight (EuclideanSpace.single (Fin.last 2) (1 : ℝ))) := by
  intro k
  refine ⟨k - L (graphProjectionN 2 k) • EuclideanSpace.single (Fin.last 2) (1 : ℝ), ?_⟩
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul,
    c1Boundary_graphProjection_last, map_zero, zero_smul, add_zero]
  abel

/-- The closure of an open set with C¹ boundary has unique derivatives at each boundary point. -/
theorem HasC1Boundary.uniqueDiffWithinAt_closure {G : Set AmbientSpace} (hG : HasC1Boundary G)
    {x : AmbientSpace} (hx : x ∈ frontier G) : UniqueDiffWithinAt ℝ (closure G) x := by
  obtain ⟨c, hc, hxc⟩ := hG x hx
  let e₃ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  let T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun u => u + c.height (graphProjectionN 2 u) • e₃
  let L : Set (EuclideanSpace ℝ (Fin 3)) := {u | u (Fin.last 2) ≤ 0}
  let y := c.placement.symm x
  let u₀ := y - c.height (graphProjectionN 2 y) • e₃
  have hpu : graphProjectionN 2 u₀ = graphProjectionN 2 y := by
    simp only [u₀, e₃, map_sub, map_smul, c1Boundary_graphProjection_last, smul_zero, sub_zero]
  have hTu : T u₀ = y := by
    change u₀ + c.height (graphProjectionN 2 u₀) • e₃ = y
    rw [hpu]
    simp [u₀]
  have hxcl : x ∈ closure c.graphDomain := by
    have h : x ∈ closure G ∩ c.region := ⟨frontier_subset_closure hx, hxc⟩
    rw [hc.closure_inter_eq] at h
    exact h.1
  have hy : y (Fin.last 2) ≤ c.height (graphProjectionN 2 y) :=
    (c.mem_closure_graphDomain_iff x).mp hxcl
  have hu₀ : u₀ ∈ L := by
    change (y - c.height (graphProjectionN 2 y) • e₃) (Fin.last 2) ≤ 0
    simp only [e₃, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
      ite_true, smul_eq_mul, mul_one]
    linarith
  have hLconv : Convex ℝ L :=
    convex_halfSpace_le (EuclideanSpace.proj (Fin.last 2) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap.isLinear 0
  have hLint : (interior L).Nonempty := by
    refine ⟨-e₃, mem_interior_iff_mem_nhds.mpr ?_⟩
    have ho : IsOpen {u : EuclideanSpace ℝ (Fin 3) | u (Fin.last 2) < 0} :=
      isOpen_lt (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const
    exact Filter.mem_of_superset (ho.mem_nhds (by simp [e₃]))
      (fun u hu => show u (Fin.last 2) ≤ 0 from le_of_lt hu)
  have hL : UniqueDiffWithinAt ℝ L u₀ :=
    uniqueDiffWithinAt_convex hLconv hLint (subset_closure hu₀)
  have hψ : Differentiable ℝ c.height := c.height_contDiff.differentiable one_ne_zero
  have hTL : UniqueDiffWithinAt ℝ (T '' L) y := by
    have h : UniqueDiffWithinAt ℝ (T '' L) (T u₀) :=
      ((c1Boundary_shear_hasFDerivAt hψ u₀).hasFDerivWithinAt (s := L)).uniqueDiffWithinAt
        hL (c1Boundary_shear_derivative_surjective _).denseRange
    rwa [hTu] at h
  have hsub : T '' L ⊆ closure (smoothSubgraph c.height) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_closure_smoothSubgraph_iff c.height_contDiff.continuous]
    have hp : graphProjectionN 2 (T u) = graphProjectionN 2 u := by
      simp only [T, e₃, map_add, map_smul, c1Boundary_graphProjection_last, smul_zero, add_zero]
    rw [hp]
    change (u + c.height (graphProjectionN 2 u) • e₃) (Fin.last 2) ≤ _
    simp only [e₃, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      ite_true, smul_eq_mul, mul_one]
    have : u (Fin.last 2) ≤ 0 := hu
    linarith
  have hsg : UniqueDiffWithinAt ℝ (closure (smoothSubgraph c.height)) y := hTL.mono hsub
  have hP := ((hasFDerivAt_rigidPlacement c.placement y).hasFDerivWithinAt
    (s := closure (smoothSubgraph c.height))).uniqueDiffWithinAt_of_continuousLinearEquiv
      c.placement.linearIsometryEquiv.toContinuousLinearEquiv hsg
  have hxy : c.placement y = x := c.placement.apply_symm_apply x
  rw [hxy] at hP
  have himg : c.placement '' closure (smoothSubgraph c.height) = closure c.graphDomain := by
    change c.placement.toHomeomorph '' closure (smoothSubgraph c.height) =
      closure (c.placement.toHomeomorph '' smoothSubgraph c.height)
    exact c.placement.toHomeomorph.image_closure _
  rw [himg] at hP
  have hloc := hP.inter (c.isOpen_region.mem_nhds hxc)
  rw [← hc.closure_inter_eq] at hloc
  exact hloc.mono inter_subset_left

/-- For an open set with C¹ boundary, `closure G` is a set of unique differentiability. -/
theorem HasC1Boundary.uniqueDiffOn_closure {G : Set AmbientSpace} (hGo : IsOpen G)
    (hG : HasC1Boundary G) : UniqueDiffOn ℝ (closure G) := by
  intro x hx
  by_cases hxG : x ∈ G
  · exact uniqueDiffWithinAt_of_mem_nhds
      (Filter.mem_of_superset (hGo.mem_nhds hxG) subset_closure)
  · exact hG.uniqueDiffWithinAt_closure (by rw [hGo.frontier_eq]; exact ⟨hx, hxG⟩)

end LiquidDrop
