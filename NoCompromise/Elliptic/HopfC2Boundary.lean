module

public import NoCompromise.Elliptic.HopfGeometry
public import NoCompromise.BV.ExteriorGeometry

@[expose] public section

/-!
# Tangent balls from C² boundary charts

C² boundary uses the existing one-sided rigid graph convention, with the
graph height twice continuously differentiable. Exterior balls are derived
from these charts and have centers on the actual geometric normal.
-/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def HasC2Boundary (D : Set AmbientSpace) : Prop :=
  ∀ p ∈ frontier D, ∃ c : C1BoundaryChart,
    c.IsChartFor D ∧ p ∈ c.region ∧ ContDiff ℝ 2 c.height

theorem HasC2Boundary.hasC1Boundary {D : Set AmbientSpace} (hD : HasC2Boundary D) :
    HasC1Boundary D := by
  intro p hp
  obtain ⟨c, hc, hp, _⟩ := hD p hp
  exact ⟨c, hc, hp⟩

def smoothGraphDefining (f : EuclideanSpace ℝ (Fin 2) → ℝ) (z : AmbientSpace) : ℝ :=
  z (Fin.last 2) - f (graphProjectionN 2 z)

theorem contDiff_smoothGraphDefining {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (smoothGraphDefining f) :=
  (EuclideanSpace.proj (Fin.last 2)).contDiff.sub (hf.comp (graphProjectionN 2).contDiff)

theorem fderiv_smoothGraphDefining {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 2 f) (z v : AmbientSpace) :
    fderiv ℝ (smoothGraphDefining f) z v =
      Real.sqrt (1 + ‖gradient f (graphProjectionN 2 z)‖ ^ 2) *
        inner ℝ (smoothSubgraphNormal f z) v := by
  have hd : HasFDerivAt (smoothGraphDefining f)
      ((EuclideanSpace.proj (Fin.last 2)) -
        (fderiv ℝ f (graphProjectionN 2 z)).comp (graphProjectionN 2)) z :=
    (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt.sub
      ((hf.differentiable (by norm_num) _).hasFDerivAt.comp z (graphProjectionN 2).hasFDerivAt)
  rw [hd.fderiv]
  change v (Fin.last 2) - fderiv ℝ f (graphProjectionN 2 z) (graphProjectionN 2 v) = _
  rw [← inner_gradient_left]
  exact (inner_smoothGraphUnitNormal (gradient f (graphProjectionN 2 z)) v).symm.trans
    (by rw [smoothSubgraphNormal, real_inner_comm])

theorem C1BoundaryChart.IsChartFor.exists_exterior_tangent_ball
    {c : C1BoundaryChart} {D : Set AmbientSpace} (hc : c.IsChartFor D)
    (hC2 : ContDiff ℝ 2 c.height) {p : AmbientSpace} (hp : p ∈ frontier D)
    (hpr : p ∈ c.region) :
    ∃ R : ℝ, 0 < R ∧ ball (p + R • c.outwardNormal p) R ⊆ (closure D)ᶜ ∧
      p ∈ sphere (p + R • c.outwardNormal p) R := by
  let z := c.placement.symm p
  let ν := smoothSubgraphNormal c.height z
  have hz : smoothGraphDefining c.height z = 0 := by
    have hg : p ∈ c.graphSurface :=
      (hc.frontier_inter_eq ▸ (show p ∈ frontier D ∩ c.region from ⟨hp, hpr⟩)).1
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hg
    dsimp only [z]
    rw [← ht, c.placement.symm_apply_apply]
    change (graphMapN c.height t) (Fin.last 2) -
      c.height (graphProjectionN 2 (graphMapN c.height t)) = 0
    rw [graphMapN_last]
    change c.height t - c.height (graphProjectionN 2 (graphAppendN t (c.height t))) = 0
    simp
  have hν : ‖ν‖ = 1 := norm_smoothGraphUnitNormal _
  obtain ⟨R, hR, hball, hsp⟩ := exists_tangent_ball_of_contDiff
    (contDiff_smoothGraphDefining hC2) hz hν
    (show 0 < Real.sqrt (1 + ‖gradient c.height (graphProjectionN 2 z)‖ ^ 2) by positivity)
    (fderiv_smoothGraphDefining hC2 z)
    (c.isOpen_region.preimage c.placement.continuous)
    (show z ∈ c.placement ⁻¹' c.region by simpa [z] using hpr)
  have heq : c.placement (z + R • ν) = p + R • c.outwardNormal p := by
    have hh := c.placement.map_vadd z (R • ν)
    simpa only [vadd_eq_add, map_smul, add_comm, z, c.placement.apply_symm_apply,
      C1BoundaryChart.outwardNormal, ν] using hh
  refine ⟨R, hR, ?_, ?_⟩
  · intro y hy
    have hy' : c.placement.symm y ∈ ball (z + R • ν) R := by
      change dist (c.placement.symm y) (z + R • ν) < R
      rw [← c.placement.isometry.dist_eq, c.placement.apply_symm_apply, heq]
      exact hy
    have hh := hball hy'
    have hyr : y ∈ c.region := by simpa using hh.1
    intro hycl
    have hgc : y ∈ closure c.graphDomain :=
      (hc.closure_inter_eq ▸ (show y ∈ closure D ∩ c.region from ⟨hycl, hyr⟩)).1
    have hle := (c.mem_closure_graphDomain_iff y).mp hgc
    have hpos : 0 < c.placement.symm y (Fin.last 2) -
        c.height (graphProjectionN 2 (c.placement.symm y)) := hh.2
    linarith
  · change dist p (p + R • c.outwardNormal p) = R
    rw [← heq, ← show c.placement z = p from c.placement.apply_symm_apply p,
      c.placement.isometry.dist_eq]
    exact hsp

end LiquidDrop
