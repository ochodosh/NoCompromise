import NoCompromise.Cones.ThreeDimFinal
import NoCompromise.Cones.SmoothExcess

/-!
# Vanishing cylindrical excess at every boundary point of an `ω`-minimal set

First step of blueprint `prop:no-singular-points` (chapter 26): at every point `x` of the
boundary of the density-one representative of an `ω`-minimal set `E ⊂ ℝ³`,
`lem:tangent-cone-minimizing` gives a locally perimeter-minimising tangent limit `F` along a
subsequence of the scales `1/(j+1)`, `prop:tangent-is-cone` makes it a cone, it is nontrivial
because `0 ∈ ∂*_e F`, and `thm:cone-3d` (`cone3d_halfspace`) makes it a halfspace.
Perimeter-measure convergence along the tangent sequence and
`lem:fixed-normal-excess-convergence` then force the cylindrical excess of `E` at `x`, relative to
the outward normal of the limiting halfspace, to tend to zero.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- **Excess decay at every boundary point** (toward `prop:no-singular-points`).  At every
boundary point `x` of the density-one representative of an `ω`-minimal set there are a unit
axis `ν` and positive scales `r j → 0` along which the cylindrical excess
`Exc(E, x, r j, ν)` tends to zero. -/
theorem IsOmegaMinimal.tendsto_cylindricalExcess_halfspace {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ frontier (densityOne E)) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧
      ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Tendsto r atTop (𝓝 0) ∧
        Tendsto (fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r j) ν)
          atTop (𝓝 0) := by
  obtain ⟨θ, _, _, htangent⟩ := hE.exists_tangent_limit hx
  let r : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hr (j) : 0 < r j := by dsimp [r]; positivity
  have ht : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨F, hmF, hlocal, hmin, hb, σ, hσ, hl1, hweak, hd, _⟩ := htangent r hr ht
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
  have hC : IsNontrivialMinimizingCone F :=
    ⟨hmin, hmF, (hmin.tangent_is_cone hd).2, hFpos, hFcpos⟩
  obtain ⟨μ, hμ, hhalf⟩ := cone3d_halfspace hC
  have hn : ‖-μ‖ = 1 := by simpa only [norm_neg] using hμ
  have hhalf' : F =ᵐ[volume] negativeHalfspace (-μ) := by
    have hae := (densityOne_ae_eq (by norm_num : 0 < 3) hmF.nullMeasurableSet).symm
    rw [hhalf] at hae
    simpa only [negativeHalfspace, inner_neg_left, neg_lt_zero] using hae
  refine ⟨-μ, hn, fun j => r (σ j), fun j => hr (σ j), ht.comp hσ.tendsto_atTop, ?_⟩
  have hex := tendsto_normalExcessIntegral_of_local_halfspace
    (fun j => (hE.blowupSet x (hr (σ j))).locallyFinite)
    (fun j => (hE.blowupSet x (hr (σ j))).nullMeasurable)
    hlocal.locallyBV hmF.nullMeasurableSet hl1 hweak hn hhalf'
    (isBounded_cylinder 0 1 hn) (isOpen_cylinder 0 1 (-μ)).measurableSet
  have heq (j) : normalExcessIntegral (LiquidDrop.blowupSet E x (r (σ j)))
      (hE.blowupSet x (hr (σ j))).locallyFinite
      (hE.blowupSet x (hr (σ j))).nullMeasurable
      (cylinder 0 1 (-μ)) (-μ) =
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r (σ j)) (-μ) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      cylindricalExcess_blowupSet_unit E hE.locallyFinite hE.nullMeasurable x (hr (σ j)) (-μ)
  simpa only [heq] using hex

end LiquidDrop
