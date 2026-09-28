import NoCompromise.DeGiorgi.SmoothBoundary
import NoCompromise.Sard.LevelCharts

/-!
# Smooth one-sided boundary charts

The smooth-boundary convention uses the established rigid C¹ graph charts,
with globally C∞ heights. Local C∞ heights on an open base give precisely this
convention after multiplication by a compact cutoff near the chart center.
-/

noncomputable section
open Set Filter Metric
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Smooth boundary in the same one-sided affine-isometry graph convention as
`HasC1Boundary`, retaining all orders of differentiability of the height. -/
def HasSmoothBoundary (D : Set AmbientSpace) : Prop :=
  ∀ p ∈ frontier D, ∃ c : C1BoundaryChart,
    c.IsChartFor D ∧ p ∈ c.region ∧ ContDiff ℝ (⊤ : ℕ∞) c.height

theorem HasSmoothBoundary.hasC1Boundary {D : Set AmbientSpace} (hD : HasSmoothBoundary D) :
    HasC1Boundary D := by
  intro p hp
  obtain ⟨c, hc, hp, _⟩ := hD p hp
  exact ⟨c, hc, hp⟩

lemma exists_smooth_height_eq_near_compact {k : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ g : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨ζ, hζ, _, hsζ, hζone, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  refine ⟨fun x => f x * ζ x, contDiff_smul_of_tsupport_subset hU hf hζ hsζ, ?_⟩
  intro x hx
  have hz := hζone.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [hz] with y hy
  simp only [hy, mul_one]

/-- A global smooth height in the chart definition adds no restriction: a
height smooth only on its open base is cut off away from the chart center. -/
theorem hasSmoothBoundary_of_local_graphs {E : Set AmbientSpace}
    (h : ∀ x ∈ frontier E,
      ∃ (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (f : EuclideanSpace ℝ (Fin 2) → ℝ)
        (U : Set (EuclideanSpace ℝ (Fin 2))) (W : Set AmbientSpace),
        IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ graphProjectionN 2 (a.symm x) ∈ U ∧
        IsOpen W ∧ x ∈ W ∧
        ∀ z ∈ W, z ∈ E ↔ a.symm z (Fin.last 2) < f (graphProjectionN 2 (a.symm z))) :
    HasSmoothBoundary E := by
  intro x hx
  obtain ⟨a, f, U, W, hU, hf, hxU, hW, hxW, hgraph⟩ := h x hx
  obtain ⟨g, hg, hgf⟩ := exists_smooth_height_eq_near_compact hU
    (isCompact_singleton (x := graphProjectionN 2 (a.symm x))) (singleton_subset_iff.mpr hxU) hf
  have hnear := hgf _ (mem_singleton _)
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.mp hnear
  let N := W ∩ (fun z => graphProjectionN 2 (a.symm z)) ⁻¹' V ∩ ball x 1
  have hN : IsOpen N :=
    (hW.inter (hVo.preimage ((graphProjectionN 2).continuous.comp a.symm.continuous))).inter
      isOpen_ball
  let c : C1BoundaryChart :=
    ⟨g, hg.of_le (by simp), a, N, hN, isBounded_ball.subset inter_subset_right⟩
  refine ⟨c, ?_, ⟨⟨hxW, hxV⟩, mem_ball_self zero_lt_one⟩, hg⟩
  intro z hz
  rw [hgraph z hz.1.1]
  change (a.symm z (Fin.last 2) < f (graphProjectionN 2 (a.symm z))) ↔
    a.symm z (Fin.last 2) < g (graphProjectionN 2 (a.symm z))
  rw [hV hz.1.2]

end LiquidDrop
