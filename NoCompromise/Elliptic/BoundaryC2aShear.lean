module

public import NoCompromise.BV.ExteriorGeometry

@[expose] public section

/-!
# Shear flattening of a rigid graph chart (`thm:boundary-C2a`, application)

For a rigid graph chart `c` (height `h`, placement `P`) and a base point `a`, the map
`y ↦ P (a + ρ y', h (a + ρ y') - ρ yₙ)` is a global diffeomorphism of `ℝ³` of the same
regularity as `h`, with an explicit inverse. It sends the flat face `{yₙ = 0}` to the graph,
and, inside the chart region, the upper half space to the subgraph side (the domain).
Unlike the normal chart it loses no derivative: a `C³` height gives a `C³` flattening.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace LiquidDrop

/-- The unscaled shear chart `w ↦ P (a + w', h (a + w') - wₙ)`. -/
def boundaryShearBase (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (w : AmbientSpace) : AmbientSpace :=
  c.placement (graphAppendN (a + graphProjectionN 2 w)
    (c.height (a + graphProjectionN 2 w) - w (Fin.last 2)))

/-- The shear chart at scale `ρ`: `y ↦ P (a + ρ y', h (a + ρ y') - ρ yₙ)`. -/
def boundaryShearMap (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (y : AmbientSpace) : AmbientSpace :=
  boundaryShearBase c a (ρ • y)

/-- The explicit inverse of the shear chart. -/
def boundaryShearInv (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (z : AmbientSpace) : AmbientSpace :=
  ρ⁻¹ • graphAppendN (graphProjectionN 2 (c.placement.symm z) - a)
    (c.height (graphProjectionN 2 (c.placement.symm z)) - c.placement.symm z (Fin.last 2))

lemma boundaryShear_graphAppendN_smul (x : EuclideanSpace ℝ (Fin 2)) (t ρ : ℝ) :
    graphAppendN (ρ • x) (ρ * t) = ρ • graphAppendN x t := by
  simp only [graphAppendN, map_smul, smul_add, smul_smul]

lemma boundaryShear_graphAppendN_add (x x' : EuclideanSpace ℝ (Fin 2)) (t t' : ℝ) :
    graphAppendN (x + x') (t + t') = graphAppendN x t + graphAppendN x' t' := by
  simp only [graphAppendN, map_add, add_smul]
  abel

lemma boundaryShearMap_symm_apply (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (y : AmbientSpace) :
    c.placement.symm (boundaryShearMap c a ρ y) =
      graphAppendN (a + ρ • graphProjectionN 2 y)
        (c.height (a + ρ • graphProjectionN 2 y) - ρ * y (Fin.last 2)) := by
  simp [boundaryShearMap, boundaryShearBase, map_smul]

lemma boundaryShearMap_leftInverse (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    Function.LeftInverse (boundaryShearInv c a ρ) (boundaryShearMap c a ρ) := by
  intro y
  simp only [boundaryShearInv, boundaryShearMap_symm_apply, graphProjectionN_append,
    graphAppendN_last, add_sub_cancel_left, sub_sub_cancel]
  rw [boundaryShear_graphAppendN_smul, smul_smul, inv_mul_cancel₀ hρ, one_smul,
    graphAppendN_projection]

lemma boundaryShearMap_rightInverse (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    Function.RightInverse (boundaryShearInv c a ρ) (boundaryShearMap c a ρ) := by
  intro z
  simp only [boundaryShearMap, boundaryShearBase, boundaryShearInv, smul_smul,
    mul_inv_cancel₀ hρ, one_smul, graphProjectionN_append, graphAppendN_last,
    add_sub_cancel, sub_sub_cancel, graphAppendN_projection, AffineIsometryEquiv.apply_symm_apply]

/-- A rigid placement is smooth of every finite order. -/
lemma boundaryShear_contDiff_placement (P : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {n : ℕ} :
    ContDiff ℝ n P := by
  have heq : (P : AmbientSpace → AmbientSpace) = fun x => P.linearIsometryEquiv x + P 0 := by
    funext x
    simpa using P.map_vadd (0 : AmbientSpace) x
  rw [heq]
  exact P.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const

lemma boundaryShear_contDiff_graphAppendN {n : ℕ} :
    ContDiff ℝ n (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => graphAppendN p.1 p.2) := by
  unfold graphAppendN
  exact ((graphBaseN 2).contDiff.comp contDiff_fst).add (contDiff_snd.smul contDiff_const)

lemma contDiff_boundaryShearMap (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {n : ℕ} (hh : ContDiff ℝ n c.height) : ContDiff ℝ n (boundaryShearMap c a ρ) := by
  have hs : ContDiff ℝ n (fun y : AmbientSpace => ρ • y) := contDiff_id.const_smul ρ
  have hx : ContDiff ℝ n (fun y : AmbientSpace => a + graphProjectionN 2 (ρ • y)) :=
    contDiff_const.add ((graphProjectionN 2).contDiff.comp hs)
  have hl : ContDiff ℝ n (fun y : AmbientSpace => (ρ • y) (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2) : AmbientSpace →L[ℝ] ℝ).contDiff.comp hs
  have hg := (boundaryShear_contDiff_graphAppendN (n := n)).comp
    (hx.prodMk ((hh.comp hx).sub hl))
  have h5 := (boundaryShear_contDiff_placement c.placement (n := n)).comp hg
  have heq : boundaryShearMap c a ρ = fun y => c.placement (graphAppendN
      (a + graphProjectionN 2 (ρ • y))
      (c.height (a + graphProjectionN 2 (ρ • y)) - (ρ • y) (Fin.last 2))) := by
    funext y; rfl
  rw [heq]
  exact h5

lemma contDiff_boundaryShearInv (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {n : ℕ} (hh : ContDiff ℝ n c.height) : ContDiff ℝ n (boundaryShearInv c a ρ) := by
  have hs : ContDiff ℝ n (fun z : AmbientSpace => c.placement.symm z) :=
    boundaryShear_contDiff_placement c.placement.symm
  have hx : ContDiff ℝ n (fun z : AmbientSpace => graphProjectionN 2 (c.placement.symm z)) :=
    (graphProjectionN 2).contDiff.comp hs
  have hl : ContDiff ℝ n (fun z : AmbientSpace => c.placement.symm z (Fin.last 2)) := by
    have := (EuclideanSpace.proj (Fin.last 2) : AmbientSpace →L[ℝ] ℝ).contDiff.comp hs
    simpa [Function.comp_def] using this
  unfold boundaryShearInv
  exact (boundaryShear_contDiff_graphAppendN.comp
    ((hx.sub contDiff_const).prodMk ((hh.comp hx).sub hl))).const_smul ρ⁻¹

/-- In the chart region, the shear chart sends the upper half space into the domain side. -/
lemma boundaryShearMap_mem_iff {c : C1BoundaryChart} {D : Set AmbientSpace}
    (hc : c.IsChartFor D) (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    {y : AmbientSpace} (hy : boundaryShearMap c a ρ y ∈ c.region) :
    boundaryShearMap c a ρ y ∈ D ↔ 0 < y (Fin.last 2) := by
  rw [hc _ hy, boundaryShearMap_symm_apply]
  simp only [smoothSubgraph, Set.mem_ofPred_eq, graphAppendN_last, graphProjectionN_append]
  constructor
  · intro h
    have : 0 < ρ * y (Fin.last 2) := by linarith
    exact pos_of_mul_pos_right this hρ.le
  · intro h
    have : 0 < ρ * y (Fin.last 2) := mul_pos hρ h
    linarith

/-- In the chart region, the shear chart sends the closed upper half space onto the closure side. -/
lemma boundaryShearMap_mem_closure_iff {c : C1BoundaryChart} {D : Set AmbientSpace}
    (hc : c.IsChartFor D) (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    {y : AmbientSpace} (hy : boundaryShearMap c a ρ y ∈ c.region) :
    boundaryShearMap c a ρ y ∈ closure D ↔ 0 ≤ y (Fin.last 2) := by
  have hcl : boundaryShearMap c a ρ y ∈ closure D ↔
      boundaryShearMap c a ρ y ∈ closure c.graphDomain := by
    constructor
    · intro h
      exact (hc.closure_inter_eq ▸ (show _ ∈ closure D ∩ c.region from ⟨h, hy⟩)).1
    · intro h
      exact (hc.closure_inter_eq.symm ▸
        (show _ ∈ closure c.graphDomain ∩ c.region from ⟨h, hy⟩)).1
  rw [hcl, c.mem_closure_graphDomain_iff, boundaryShearMap_symm_apply]
  simp only [graphAppendN_last, graphProjectionN_append]
  constructor
  · intro h
    have : 0 ≤ ρ * y (Fin.last 2) := by linarith
    exact (mul_nonneg_iff_of_pos_left hρ).mp this
  · intro h
    have : 0 ≤ ρ * y (Fin.last 2) := mul_nonneg hρ.le h
    linarith

/-- A chart point on the frontier lies on the graph over its projection. -/
lemma boundaryShear_frontier_last {c : C1BoundaryChart} {D : Set AmbientSpace}
    (hc : c.IsChartFor D) {p : AmbientSpace} (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    c.placement.symm p (Fin.last 2) = c.height (graphProjectionN 2 (c.placement.symm p)) := by
  have hpg : p ∈ c.graphSurface :=
    (hc.frontier_inter_eq ▸ (show p ∈ frontier D ∩ c.region from ⟨hp, hpc⟩)).1
  obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hpg
  rw [c.placement.symm_apply_apply]
  change graphAppendN x (c.height x) (Fin.last 2) =
    c.height (graphProjectionN 2 (graphAppendN x (c.height x)))
  rw [graphAppendN_last, graphProjectionN_append]

/-- The shear chart centred at a frontier point sends the origin to that point. -/
lemma boundaryShearMap_zero {c : C1BoundaryChart} {D : Set AmbientSpace}
    (hc : c.IsChartFor D) {p : AmbientSpace} (hp : p ∈ frontier D) (hpc : p ∈ c.region)
    (ρ : ℝ) :
    boundaryShearMap c (graphProjectionN 2 (c.placement.symm p)) ρ 0 = p := by
  have hl := boundaryShear_frontier_last hc hp hpc
  simp only [boundaryShearMap, boundaryShearBase, smul_zero, map_zero, add_zero,
    PiLp.zero_apply, sub_zero]
  rw [← hl, graphAppendN_projection, AffineIsometryEquiv.apply_symm_apply]

/-- For a small scale the shear chart maps `closedBall 0 2` into the chart region. -/
lemma exists_boundaryShearMap_region {c : C1BoundaryChart} {D : Set AmbientSpace}
    (hc : c.IsChartFor D) {p : AmbientSpace} (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0, ∀ y ∈ closedBall (0 : AmbientSpace) 2,
      boundaryShearMap c (graphProjectionN 2 (c.placement.symm p)) ρ y ∈ c.region := by
  set a := graphProjectionN 2 (c.placement.symm p)
  have hcont : Continuous (boundaryShearBase c a) := by
    have := contDiff_boundaryShearMap c a 1 (n := 0) (c.height_contDiff.of_le (by simp))
    have heq : boundaryShearMap c a 1 = boundaryShearBase c a := by
      funext y; simp [boundaryShearMap]
    rw [← heq]
    exact this.continuous
  have h0 : boundaryShearBase c a 0 = p := by
    have := boundaryShearMap_zero hc hp hpc 1
    simpa [boundaryShearMap] using this
  have hmem : boundaryShearBase c a ⁻¹' c.region ∈ 𝓝 (0 : AmbientSpace) :=
    hcont.continuousAt.preimage_mem_nhds (c.isOpen_region.mem_nhds (h0.symm ▸ hpc))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨δ / 3, by positivity, fun y hy => hball ?_⟩
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity)]
  have : ‖y‖ ≤ 2 := mem_closedBall_zero_iff.mp hy
  nlinarith

end LiquidDrop
