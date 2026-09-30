module

public import NoCompromise.CapacitaryK.SlabGaussGreen

@[expose] public section

/-!
# Area of regular levels (chapter 31, inputs to `prop:K-measure-inequality`)

The boundary levels of a bounded regular slab have finite `H²`-measure, continuous functions on them
are integrable, and a nonempty regular level has positive `H²`-measure.
-/

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Both boundary levels of a bounded regular slab have finite area. -/
theorem slab_level_measure_lt_top {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    Measure.euclideanHausdorffMeasure 2 (U ∩ u ⁻¹' {a}) < ⊤ ∧
      Measure.euclideanHausdorffMeasure 2 (U ∩ u ⁻¹' {b}) < ⊤ := by
  let S := U ∩ u ⁻¹' Ioo a b
  have hS : IsOpen S := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo
  have hC1 : HasC1Boundary S := slab_hasC1Boundary hU hu hab hcl hreg
  obtain ⟨φ, hφ, hcφ, _, hone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hbdd.isCompact_closure hU hcl
  obtain ⟨_, _, ht⟩ := exists_global_w11_boundary_restriction_bound hS hbdd
    hC1.hasLipschitzBoundary
  have hi : IntegrableOn φ (frontier S) (Measure.euclideanHausdorffMeasure 2) :=
    memLp_one_iff_integrable.mp (ht φ (gradient φ)
      (hasW11GradientOn_of_contDiff_compact (hφ.of_le (by simp)) hcφ) hφ.continuous).1
  have h1 : IntegrableOn (fun _ : E3 => (1 : ℝ)) (frontier S)
      (Measure.euclideanHausdorffMeasure 2) := hi.congr_fun (fun x hx =>
        (hone.filter_mono (nhds_le_nhdsSet (frontier_subset_closure hx))).self_of_nhds)
      isClosed_frontier.measurableSet
  have hfinite : Measure.euclideanHausdorffMeasure 2 (frontier S) < ⊤ := by
    exact ((integrableOn_const_iff (C := (1 : ℝ))).mp h1).resolve_left (by simp)
  have hfront := slab_frontier_eq hU hu hab hcl hreg
  exact ⟨(measure_mono (hfront.symm ▸ subset_union_left)).trans_lt hfinite,
    (measure_mono (hfront.symm ▸ subset_union_right)).trans_lt hfinite⟩

/-- Continuous functions on a boundary level are integrable. -/
theorem slab_level_integrableOn {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0)
    {t : ℝ} (ht : t = a ∨ t = b) {g : E3 → ℝ} (hg : ContinuousOn g (U ∩ u ⁻¹' {t})) :
    IntegrableOn g (U ∩ u ⁻¹' {t}) (Measure.euclideanHausdorffMeasure 2) := by
  have hsub : U ∩ u ⁻¹' {t} ⊆ frontier (U ∩ u ⁻¹' Ioo a b) := by
    rw [slab_frontier_eq hU hu hab hcl hreg]
    rcases ht with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have heq : U ∩ u ⁻¹' {t} = closure (U ∩ u ⁻¹' Ioo a b) ∩ u ⁻¹' {t} := by
    apply Subset.antisymm
    · exact fun x hx => ⟨frontier_subset_closure (hsub hx), hx.2⟩
    · exact fun x hx => ⟨hcl hx.1, hx.2⟩
  have hclosed : IsClosed (U ∩ u ⁻¹' {t}) := by
    rw [heq]
    exact (hu.continuousOn.mono hcl).preimage_isClosed_of_isClosed
      isClosed_closure isClosed_singleton
  have hcompact : IsCompact (U ∩ u ⁻¹' {t}) :=
    hbdd.isCompact_closure.of_isClosed_subset hclosed
      (hsub.trans frontier_subset_closure)
  have hfinite : Measure.euclideanHausdorffMeasure 2 (U ∩ u ⁻¹' {t}) < ⊤ := by
    rcases ht with rfl | rfl
    · exact (slab_level_measure_lt_top hU hu hab hbdd hcl hreg).1
    · exact (slab_level_measure_lt_top hU hu hab hbdd hcl hreg).2
  exact hg.integrableOn_of_subset_isCompact hcompact hclosed.measurableSet
    Subset.rfl hfinite.ne

/-- A nonempty regular level has positive area. -/
theorem level_measure_pos {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {t : ℝ} {x : E3} (hx : x ∈ U) (hxt : u x = t) (hreg : gradient u x ≠ 0) :
    0 < Measure.euclideanHausdorffMeasure 2 (U ∩ u ⁻¹' {t}) := by
  have hux := (hu.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨i, hi⟩ := exists_coareaSwap_nonzero_last hux hreg
  let e := coareaSwap i
  have hUe : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hue : ContDiffOn ℝ 1 (u ∘ e) (e ⁻¹' U) :=
    hu.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hy => hy)
  have hxe : e.symm x ∈ e ⁻¹' U := by simpa using hx
  obtain ⟨d, hxd, hds⟩ := exists_scalarCoareaChart hUe hue hxe hi
  have hxD : graphProjectionN 2 (e.symm x) ∈ d.levelDomain t := by
    change graphAppendN (graphProjectionN 2 (e.symm x)) t ∈ d.chart.target
    have ht : (u ∘ e) (e.symm x) = t := by simpa using hxt
    rw [← ht, ← coareaCoordinateMap, ← d.forward_eq]
    exact d.chart.map_source hxd
  let P : E3 → EuclideanSpace ℝ (Fin 2) := fun z => graphProjectionN 2 (e.symm z)
  have hP : LipschitzWith 1 P := by
    have hp : LipschitzWith 1 (graphProjectionN 2) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      simp only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
      have hh := norm_sq_graphProjectionN (y - z)
      nlinarith only [hh, sq_nonneg ((y - z) (Fin.last 2)), norm_nonneg (y - z),
        norm_nonneg (graphProjectionN 2 (y - z))]
    simpa only [one_mul, Function.comp_def] using
      hp.comp e.symm.isometry.lipschitzWith
  have hcover : d.levelDomain t ⊆ P '' (U ∩ u ⁻¹' {t}) := by
    intro y hy
    refine ⟨e (d.chart.symm (graphAppendN y t)),
      ⟨hds (d.chart.map_target hy), d.u_inverse_eq hy⟩, ?_⟩
    simp only [P, e.symm_apply_apply, d.inverse_eq_graphMapN hy]
    exact graphProjectionN_append y (d.levelHeight t y)
  have hpos : 0 < Measure.euclideanHausdorffMeasure 2 (d.levelDomain t) := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact (d.isOpen_levelDomain t).measure_pos volume ⟨_, hxD⟩
  have hle : Measure.euclideanHausdorffMeasure 2 (P '' (U ∩ u ⁻¹' {t})) ≤
      Measure.euclideanHausdorffMeasure 2 (U ∩ u ⁻¹' {t}) := by
    have hh := hP.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
      (U ∩ u ⁻¹' {t})
    simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hh
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    exact mul_le_mul' le_rfl hh
  exact hpos.trans_le ((measure_mono hcover).trans hle)

end LiquidDrop.CapacitaryK
