module

public import NoCompromise.Regularity.ZeroExcessMollification

@[expose] public section

/-! # Almost-everywhere height ordering from a local constant normal -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient CompactlySupported Convolution
namespace LiquidDrop

/-- Constant outward normal on a convex open region forces the actual
indicator to decrease with height on one common full-measure set. -/
theorem HasLocalConstantIndicatorPolar.ae_height_order
    {E U : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasLocalConstantIndicatorPolar E U μ ν) (hE : NullMeasurableSet E volume)
    (hU : IsOpen U) (hcU : Convex ℝ U) :
    ∃ S : Set AmbientSpace, (∀ᵐ x : AmbientSpace, x ∈ S) ∧
      ∀ x ∈ S ∩ U, ∀ y ∈ S ∩ U, inner ℝ ν x ≤ inner ℝ ν y →
        E.indicator (fun _ => (1 : ℝ)) y ≤ E.indicator (fun _ => (1 : ℝ)) x := by
  let φ (j : ℕ) : ContDiffBump (0 : AmbientSpace) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hratio : ∀ᶠ j in atTop, (φ j).rOut ≤ 2 * (φ j).rIn := by
    filter_upwards with j
    dsimp only [φ]
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hlim hratio
    (locallyIntegrable_indicator_one hE)
  let S := {x : AmbientSpace | Tendsto
    (fun j => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      E.indicator (fun _ => (1 : ℝ))) x) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) x))}
  refine ⟨S, hae, ?_⟩
  intro x hx y hy hxy
  have hcseg : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hsδ⟩ := hcseg.exists_cthickening_subset_open hU
    (hcU.segment_subset hx.2 hy.2)
  apply le_of_tendsto_of_tendsto hy.1 hx.1
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with j hj
  apply h.bump_height_order hE (φ j) _ hxy
  intro z hz w hw
  apply hsδ
  apply closedBall_subset_cthickening hz δ
  have hw' : z - w ∈ tsupport ((φ j).normed volume) := by
    have he := tsupport_comp_eq_preimage ((φ j).normed volume) (Homeomorph.subLeft z)
    change w ∈ tsupport (((φ j).normed volume) ∘ (Homeomorph.subLeft z)) at hw
    rw [he] at hw
    exact hw
  rw [(φ j).tsupport_normed_eq] at hw'
  have hd : dist (z - w) 0 ≤ δ := hw'.trans hj.le
  simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm z w] using hd

end LiquidDrop
