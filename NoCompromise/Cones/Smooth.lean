import NoCompromise.Cones.ThreeDim
import NoCompromise.Regularity.FirstVariation
import NoCompromise.Regularity.DensityEstimates
import NoCompromise.Regularity.RepresentativeBoundary

/-!
# Supporting steps toward `lem:cone-smooth` (chapter 25)

* `cone_exists_nontrivial_tangent` : at every boundary point of the density-one representative of
  a nontrivial minimising cone (the vertex included) there is a tangent limit which is itself a
  nontrivial minimising cone (both phases of positive volume) with the origin on its boundary.
* `cone_first_variation_eq_zero` : exact minimality gives vanishing first variation of the reduced
  boundary for `C¹` compactly supported fields supported in a unit ball (`eq:bounded-H`, `ω = 0`).

Neither the halfspace classification of these tangents (which needs `lem:cone-descent` and
`lem:cone-2d`) nor `thm:eps-regularity` is used or assumed here.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Tangent existence supplies a nontrivial cone, including both positive-volume phases, at every
boundary point of the density-one representative. The vertex is not excluded. -/
theorem cone_exists_nontrivial_tangent {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) :
    ∃ F : Set AmbientSpace, IsConeTangentLimit C p F ∧
      IsNontrivialMinimizingCone F ∧ (0 : AmbientSpace) ∈ frontier (densityOne F) := by
  obtain ⟨θ, _hθ, _hθlim, htangent⟩ := hC.minimizing.isOmegaMinimal.exists_tangent_limit hp
  let r : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hr (j) : 0 < r j := by dsimp [r]; positivity
  have ht : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨F, hmF, _hlocal, hmin, hb, σ, hσ, hl1, _hweak, hd, _hper⟩ :=
    htangent r hr ht
  have he : (0 : AmbientSpace) ∈ essentialBoundary F := by
    rwa [hmin.isOmegaMinimal.frontier_densityOne] at hb
  have hec : (0 : AmbientSpace) ∈ essentialBoundary Fᶜ := by
    rwa [essentialBoundary_compl hmF.nullMeasurableSet]
  have hFpos : 0 < volume F := by
    have hv := radialVolume_pos_at_essentialBoundary he (r := 1) (by norm_num)
    exact ((ENNReal.toReal_pos_iff.mp hv).1).trans_le
      (measure_mono (inter_subset_left : F ∩ ball 0 1 ⊆ F))
  have hFcpos : 0 < volume Fᶜ := by
    have hv := radialVolume_pos_at_essentialBoundary hec (r := 1) (by norm_num)
    exact ((ENNReal.toReal_pos_iff.mp hv).1).trans_le
      (measure_mono (inter_subset_left : Fᶜ ∩ ball 0 1 ⊆ Fᶜ))
  refine ⟨F, ⟨hmF, hmin, ⟨θ, hd⟩, ?_⟩,
    ⟨hmin, hmF, (hmin.tangent_is_cone hd).2, hFpos, hFcpos⟩, hb⟩
  exact ⟨fun j => r (σ j), fun j => hr (σ j), ht.comp hσ.tendsto_atTop, hl1⟩

/-- Zero-error perimeter minimality gives vanishing weak mean curvature, expressed by the actual
reduced-boundary first variation. No smoothness is assumed. -/
theorem cone_first_variation_eq_zero {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) {x : AmbientSpace}
    (hXs : tsupport X ⊆ ball x 1) :
    (∫ z in reducedBoundary C hC.minimizing.isOmegaMinimal.locallyFinite
        hC.minimizing.isOmegaMinimal.nullMeasurable,
      tangentialDivergence X
        (reducedNormal C hC.minimizing.isOmegaMinimal.locallyFinite
          hC.minimizing.isOmegaMinimal.nullMeasurable) z
        ∂hausdorffMeasure2 3) = 0 := by
  have h := hC.minimizing.isOmegaMinimal.bounded_first_variation hX hcX hXs
  rw [zero_mul] at h
  exact abs_nonpos_iff.mp h

end LiquidDrop
