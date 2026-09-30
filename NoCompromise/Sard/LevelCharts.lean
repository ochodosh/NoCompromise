module

public import NoCompromise.BV.CoareaCharts
public import NoCompromise.BV.CoareaIsometry

@[expose] public section

/-!
# Regular scalar level charts with their full differentiability order

A coordinate swap and the ordinary inverse function theorem parametrize a
regular scalar level by an open subset of one lower-dimensional Euclidean
space. The parametrization retains every available differentiability order.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A regular scalar zero level has a local parametrization of the same
regularity as the defining function. -/
lemma exists_contDiff_zero_level_parametrization {k : ℕ} {r : WithTop ℕ∞}
    (hr : 1 ≤ r) {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U)
    {h : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hh : ContDiffOn ℝ r h U)
    {x : EuclideanSpace ℝ (Fin (k + 1))} (hx : x ∈ U) (hhx : gradient h x ≠ 0) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin (k + 1))))
      (W : Set (EuclideanSpace ℝ (Fin k)))
      (γ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin (k + 1))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsOpen W ∧ ContDiffOn ℝ r γ W ∧ MapsTo γ W U ∧
        V ∩ h ⁻¹' {(0 : ℝ)} ⊆ γ '' W := by
  have hhd := (hh.differentiableOn (ne_of_gt (lt_of_lt_of_le (by norm_num) hr))
    x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨i, hi⟩ := exists_coareaSwap_nonzero_last hhd hhx
  let e := coareaSwap i
  have hUe : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hhe : ContDiffOn ℝ r (h ∘ e) (e ⁻¹' U) :=
    hh.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hy => hy)
  have hxe : e.symm x ∈ e ⁻¹' U := by simpa using hx
  obtain ⟨d, hxd, hds⟩ := exists_scalarCoareaChart hUe (hhe.of_le hr) hxe hi
  have hinv : ContDiffOn ℝ r d.chart.symm d.chart.target := by
    intro y hy
    have hys := d.chart.map_target hy
    apply (d.chart.contDiffAt_symm hy (d.hasFDerivAt_forward hys) ?_).contDiffWithinAt
    rw [d.forward_eq]
    exact (contDiffOn_coareaCoordinateMap (hhe.mono hds)).contDiffAt
      (d.chart.open_source.mem_nhds hys)
  let γ := e ∘ d.chart.symm ∘ fun z => graphAppendN z 0
  have hγ : ContDiffOn ℝ r γ (d.levelDomain 0) :=
    e.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hinv.comp (contDiff_graphAppendN 0).contDiffOn (fun _ hy => hy))
  refine ⟨e '' d.chart.source, d.levelDomain 0, γ,
    e.toHomeomorph.isOpenMap _ d.chart.open_source,
    ⟨e.symm x, hxd, e.apply_symm_apply x⟩, ?_, d.isOpen_levelDomain 0, hγ, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hds hy
  · intro y hy
    exact hds (d.chart.map_target hy)
  · rintro z ⟨⟨y, hy, rfl⟩, hy0⟩
    have hylevel : y ∈ d.chart.source ∩ (h ∘ e) ⁻¹' {(0 : ℝ)} := ⟨hy, hy0⟩
    rw [← d.graphMapN_levelPatch (A := d.chart.source) (Subset.refl _) 0] at hylevel
    obtain ⟨w, hw, heq⟩ := hylevel
    have hwD := d.levelPatch_subset_levelDomain (Subset.refl _) 0 hw
    refine ⟨w, hwD, ?_⟩
    dsimp only [γ, comp_apply]
    rw [d.inverse_eq_graphMapN hwD, heq]

end LiquidDrop
