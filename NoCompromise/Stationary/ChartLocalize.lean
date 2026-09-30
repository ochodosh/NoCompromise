module

public import NoCompromise.Stationary.Defs
public import NoCompromise.Elliptic.NondivSchauderNorm
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# Localizing boundary charts

A smooth cutoff turns local regularity of a chart height into global regularity,
while preserving the chart on a smaller neighborhood.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace LiquidDrop

/-- Local regularity of the height can be made global by shrinking the chart. -/
theorem C1BoundaryChart.exists_localized {D : Set AmbientSpace} {c : C1BoundaryChart}
    (hc : c.IsChartFor D) {p : AmbientSpace} (hpc : p ∈ c.region) {ρ : ℝ} (hρ : 0 < ρ)
    {k : ℕ∞} (hk : ContDiffOn ℝ k c.height
      (Metric.ball (graphProjectionN 2 (c.placement.symm p)) ρ)) :
    ∃ c' : C1BoundaryChart, c'.IsChartFor D ∧ p ∈ c'.region ∧ ContDiff ℝ k c'.height ∧
      c'.placement = c.placement ∧ c'.region ⊆ c.region ∧
      Set.EqOn c'.height c.height
        (Metric.ball (graphProjectionN 2 (c.placement.symm p)) (ρ / 2)) := by
  let y1 := graphProjectionN 2 (c.placement.symm p)
  let χ : ContDiffBump y1 :=
    { rIn := ρ / 2
      rOut := 3 * ρ / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g := fun y => χ y * c.height y
  have hg1 : ContDiff ℝ 1 g := χ.contDiff.mul c.height_contDiff
  have hgk : ContDiff ℝ k g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ ball y1 ρ
    · exact χ.contDiffAt.mul (hk.contDiffAt (isOpen_ball.mem_nhds hy))
    · have hy' : ρ ≤ dist y y1 := le_of_not_gt hy
      have hdist : χ.rOut < dist y y1 := by dsimp [χ]; linarith
      have hevent : ∀ᶠ z in 𝓝 y, χ.rOut < dist z y1 :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hdist
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hevent] with z hz
      simp only [g, χ.zero_of_le_dist hz.le, zero_mul]
  have hgeq : EqOn g c.height (ball y1 (ρ / 2)) := by
    intro y hy
    have hχ : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp only [g, hχ, one_mul]
  let c' : C1BoundaryChart :=
    { height := g
      height_contDiff := hg1
      placement := c.placement
      region := c.region ∩
        (fun z => graphProjectionN 2 (c.placement.symm z)) ⁻¹' ball y1 (ρ / 2)
      isOpen_region := c.isOpen_region.inter
        (isOpen_ball.preimage
          ((graphProjectionN 2).continuous.comp c.placement.symm.continuous))
      bounded_region := c.bounded_region.subset inter_subset_left }
  refine ⟨c', ?_, ?_, hgk, rfl, inter_subset_left, hgeq⟩
  · intro z hz
    change z ∈ D ↔ c.placement.symm z ∈ smoothSubgraph g
    rw [hc z hz.1]
    change (c.placement.symm z (Fin.last 2) < c.height (graphProjectionN 2
      (c.placement.symm z))) ↔
      c.placement.symm z (Fin.last 2) < g (graphProjectionN 2 (c.placement.symm z))
    rw [hgeq hz.2]
  · change p ∈ c.region ∧ y1 ∈ ball y1 (ρ / 2)
    exact ⟨hpc, mem_ball_self (by positivity)⟩

/-- Local `C^k` regularity of chart heights suffices for `C^k` boundary. -/
theorem hasCkBoundary_of_local {D : Set AmbientSpace} {k : ℕ∞}
    (h : ∀ p ∈ frontier D, ∃ c : C1BoundaryChart, c.IsChartFor D ∧ p ∈ c.region ∧
      ∃ ρ > 0, ContDiffOn ℝ k c.height
        (Metric.ball (graphProjectionN 2 (c.placement.symm p)) ρ)) :
    HasCkBoundary k D := by
  intro p hp
  obtain ⟨c, hc, hpc, ρ, hρ, hk⟩ := h p hp
  obtain ⟨c', hc', hpc', hk', _⟩ := C1BoundaryChart.exists_localized hc hpc hρ hk
  exact ⟨c', hc', hpc', hk'⟩

/-- Local `C^{1,a}` boundary charts: every boundary point lies in a chart whose height is
`C^{1,a}` on a disk around the base point. -/
def HasC1HolderBoundary (a : ℝ) (D : Set AmbientSpace) : Prop :=
  ∀ p ∈ frontier D, ∃ c : C1BoundaryChart, c.IsChartFor D ∧ p ∈ c.region ∧
    ∃ ρ > 0, HasC1HolderOn a c.height
      (Metric.ball (graphProjectionN 2 (c.placement.symm p)) ρ)

theorem HasC1HolderBoundary.hasC1Boundary {a : ℝ} {D : Set AmbientSpace}
    (h : HasC1HolderBoundary a D) : HasC1Boundary D := by
  intro p hp
  obtain ⟨c, hc, hpc, _⟩ := h p hp
  exact ⟨c, hc, hpc⟩

end LiquidDrop
