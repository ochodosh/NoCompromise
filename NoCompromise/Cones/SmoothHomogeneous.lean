import NoCompromise.Cones.SmoothGraph
import NoCompromise.Cones.LinkNonempty

/-!
# Homogeneity of the boundary graph of a cone about the vertex (toward `lem:cone-link-great-circle`)

In the coordinates `y ↦ p + s • Q y` of `Cones/SmoothGraph.lean` (`Q = verticalAxisIsometry ν`,
`ν ⊥ p`), the vertex `0` of the cone sits at `y₀ = -(s⁻¹) • Q⁻¹ p`, a horizontal point
(`y₀ 2 = 0`) with base `v = graphProjectionN 2 y₀` of norm `‖p‖ / s`.  Dilation invariance of the
cone makes the boundary graph `f` homogeneous of degree one about `v`:
`f (v + l • (x' - v)) = l * f x'` whenever both graph points lie in the cylinder.

* `coneVertexBase` : the base point `v`;
* `norm_coneVertexBase` : `‖v‖ = ‖p‖ / s`;
* `cone_graph_homogeneous` : the homogeneity identity.
-/

noncomputable section
open Set Metric

namespace LiquidDrop

/-- The cone vertex in the chart `y ↦ p + s • Q y`. -/
def coneVertex (p ν : AmbientSpace) (s : ℝ) : AmbientSpace :=
  -(s⁻¹) • (verticalAxisIsometry ν).symm p

/-- Its base point in the horizontal plane. -/
def coneVertexBase (p ν : AmbientSpace) (s : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  graphProjectionN 2 (coneVertex p ν s)

lemma coneVertex_height {p ν : AmbientSpace} (hν : ‖ν‖ = 1) (hνp : inner ℝ ν p = 0) (s : ℝ) :
    coneVertex p ν s 2 = 0 := by
  have h : inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      ((verticalAxisIsometry ν).symm p) = 0 := by
    rw [← (verticalAxisIsometry ν).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
      verticalAxisIsometry_apply_vertical hν, hνp]
  rw [EuclideanSpace.inner_single_left] at h
  simp only [coneVertex, PiLp.smul_apply, smul_eq_mul]
  simpa using Or.inr h

lemma coneVertex_eq {p ν : AmbientSpace} (hν : ‖ν‖ = 1) (hνp : inner ℝ ν p = 0) (s : ℝ) :
    coneVertex p ν s = graphAppendN (coneVertexBase p ν s) 0 := by
  conv_lhs => rw [← graphAppendN_projection (coneVertex p ν s)]
  rw [coneVertexBase]
  congr 1
  exact coneVertex_height hν hνp s

lemma norm_coneVertexBase {p ν : AmbientSpace} (hν : ‖ν‖ = 1) (hνp : inner ℝ ν p = 0)
    {s : ℝ} (hs : 0 < s) : ‖coneVertexBase p ν s‖ = ‖p‖ / s := by
  have h := norm_sq_graphProjectionN (coneVertex p ν s)
  have h2 : coneVertex p ν s (Fin.last 2) = 0 := coneVertex_height hν hνp s
  have h' : ‖coneVertex p ν s‖ ^ 2 = ‖graphProjectionN 2 (coneVertex p ν s)‖ ^ 2 := by
    rw [h, h2]; ring
  have hn : ‖coneVertex p ν s‖ = ‖p‖ / s := by
    rw [coneVertex, norm_smul, LinearIsometryEquiv.norm_map, norm_neg, norm_inv,
      Real.norm_eq_abs, abs_of_pos hs, inv_mul_eq_div]
  have h0 : 0 ≤ ‖coneVertexBase p ν s‖ := norm_nonneg _
  have h1 : 0 ≤ ‖p‖ / s := by positivity
  rw [coneVertexBase]
  rw [hn] at h'
  have h0' : 0 ≤ ‖graphProjectionN 2 (coneVertex p ν s)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖graphProjectionN 2 (coneVertex p ν s)‖ - ‖p‖ / s),
    sq_nonneg (‖graphProjectionN 2 (coneVertex p ν s)‖ + ‖p‖ / s)]

/-- Dilating a chart point about the vertex dilates its image about the origin. -/
lemma chart_smul_vertex (p ν : AmbientSpace) {s : ℝ} (hs : 0 < s) (y : AmbientSpace) (l : ℝ) :
    p + s • verticalAxisIsometry ν (coneVertex p ν s + l • (y - coneVertex p ν s)) =
      l • (p + s • verticalAxisIsometry ν y) := by
  have hQ : s • verticalAxisIsometry ν (coneVertex p ν s) = -p := by
    rw [coneVertex, map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul, mul_neg,
      mul_inv_cancel₀ hs.ne', neg_smul, one_smul]
  rw [map_add, map_smul, map_sub]
  set A := verticalAxisIsometry ν (coneVertex p ν s)
  set B := verticalAxisIsometry ν y
  have e : p + s • (A + l • (B - A)) = p + s • A + l • (s • B) - l • (s • A) := by module
  rw [e, hQ]
  module

/-- **Homogeneity of the boundary graph of a cone about the vertex.** -/
theorem cone_graph_homogeneous {C : Set AmbientSpace} (hC : IsNontrivialMinimizingCone C)
    {p ν : AmbientSpace} (hν : ‖ν‖ = 1) (hνp : inner ℝ ν p = 0) {s ρ : ℝ} (hs : 0 < s)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hiff : ∀ y ∈ standardCylinder ρ,
      (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
        ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, graphAppendN x' (f x') = y))
    (hcyl : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      graphAppendN x' (f x') ∈ standardCylinder ρ)
    {x' : EuclideanSpace ℝ (Fin 2)} (hx' : x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    {l : ℝ} (hl : 0 < l)
    (hl' : graphAppendN (coneVertexBase p ν s + l • (x' - coneVertexBase p ν s)) (l * f x') ∈
      standardCylinder ρ) :
    f (coneVertexBase p ν s + l • (x' - coneVertexBase p ν s)) = l * f x' := by
  set v := coneVertexBase p ν s
  set y := graphAppendN x' (f x')
  have hy : p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) :=
    (hiff y (hcyl x' hx')).2 ⟨x', hx', rfl⟩
  have hly : l • (p + s • verticalAxisIsometry ν y) ∈ frontier (densityOne C) :=
    hC.smul_mem_frontier hy hl
  have hy' : coneVertex p ν s + l • (y - coneVertex p ν s) =
      graphAppendN (v + l • (x' - v)) (l * f x') := by
    rw [← graphAppendN_projection (coneVertex p ν s + l • (y - coneVertex p ν s))]
    congr 1
    · rw [map_add, map_smul, map_sub]
      simp only [y, graphProjectionN_append, v, coneVertexBase]
    · have h0 := coneVertex_height hν hνp s
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [show (Fin.last 2) = (2 : Fin 3) from rfl, h0]
      simp [y]
  rw [← chart_smul_vertex p ν hs, hy'] at hly
  obtain ⟨x'', _, hx''⟩ := (hiff _ hl').1 hly
  have hb := congrArg (graphProjectionN 2) hx''
  have ht := congrArg (fun z : AmbientSpace => z 2) hx''
  simp only [graphProjectionN_append] at hb
  simp only [graphAppendN_height_three] at ht
  rw [← hb]
  exact ht

end LiquidDrop
