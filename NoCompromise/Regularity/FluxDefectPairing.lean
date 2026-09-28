import NoCompromise.Regularity.FluxDefectTests

/-! # The signed vertical flux against compact horizontal test functions -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Actual slab and cap phases determine the positive signed vertical flux.
This is proved from the genuine compact-C¹ distributional identities. -/
theorem IsSlabCapConfiguration.vertical_flux_test
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {β : EuclideanSpace ℝ (Fin 2) → ℝ} (hβ : ContDiff ℝ 1 β)
    (hcβ : HasCompactSupport β) (hsβ : tsupport β ⊆ ball 0 r) :
    (∫ x in standardCylinder r, β (graphProjectionN 2 x) * reducedNormal E hE hmE x 2
      ∂canonicalPerimeterMeasure E hE hmE) = ∫ p, β p := by
  obtain ⟨ψ, hψ, hcψ, hsψ, hψone⟩ :=
    exists_slab_flux_cutoff h.1.1 h.1.2.1 h.1.2.2.2.1
  let f : AmbientSpace → ℝ := fun x => β (graphProjectionN 2 x) * ψ (x 2)
  have hf : ContDiff ℝ 1 f :=
    (hβ.comp (graphProjectionN 2).contDiff).mul
      (hψ.comp (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).contDiff)
  have hcf : HasCompactSupport f := hasCompactSupport_vertical_tensor hcβ hcψ
  let φ : CompactlySupportedContinuousMap AmbientSpace ℝ := ⟨⟨f, hf.continuous⟩, hcf⟩
  have hφ : ContDiff ℝ 1 φ := hf
  have hs : Function.support f ⊆ standardCylinder r := by
    intro x hx
    have hm := mul_ne_zero_iff.mp hx
    have hb : graphProjectionN 2 x ∈ ball 0 r := hsβ (subset_tsupport β hm.1)
    have hh := hsψ (subset_tsupport ψ hm.2)
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hb, abs_lt.mpr hh⟩
  have hp : IsAmbientOutwardPerimeterPolar E (canonicalPerimeterMeasure E hE hmE)
      (reducedNormal E hE hmE) := by
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE]
    exact reducedBoundary_outwardPerimeterPolar E hE hmE
  have hpair := hp.coordinate_eq 2 φ hφ
  simp only [mul_neg, integral_neg, neg_inj] at hpair
  have hleft : (∫ x in standardCylinder r,
      β (graphProjectionN 2 x) * reducedNormal E hE hmE x 2
        ∂canonicalPerimeterMeasure E hE hmE) =
      ∫ x, φ x * reducedNormal E hE hmE x 2 ∂canonicalPerimeterMeasure E hE hmE := by
    rw [← integral_indicator (isOpen_standardCylinder r).measurableSet]
    apply integral_congr_ae
    filter_upwards [ae_mem_reducedBoundary E hE hmE] with x hx
    by_cases hxC : x ∈ standardCylinder r
    · rw [indicator_of_mem hxC]
      have hh := (hψone (x 2) (h.1.2.2.2.2 x ⟨hx, hxC⟩).le).1
      change _ = (β (graphProjectionN 2 x) * ψ (x 2)) * _
      rw [hh, mul_one]
    · rw [indicator_of_notMem hxC]
      have hz : f x = 0 := Function.notMem_support.mp (fun hh => hxC (hs hh))
      change 0 = f x * _
      rw [hz, zero_mul]
  have hder (x : AmbientSpace) : fderiv ℝ φ x (EuclideanSpace.single 2 1) =
      β (graphProjectionN 2 x) * deriv ψ (x 2) := fderiv_vertical_tensor_last hβ hψ x
  let H := smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin 2) => c)
  have hcompare : (fun x => E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single 2 1)) =ᵐ[volume]
      (fun x => H.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single 2 1)) := by
    obtain ⟨hl, hu⟩ := h.phases_off_slab
    have hl' := (ae_restrict_iff' (isOpen_lowerSlabRegion r c η).measurableSet).mp hl
    have hu' := (ae_restrict_iff' (isOpen_upperSlabRegion r c η).measurableSet).mp hu
    filter_upwards [hl', hu'] with x hxL hxU
    rw [hder]
    by_cases hb : β (graphProjectionN 2 x) = 0
    · simp only [hb, zero_mul, mul_zero]
    by_cases hd : deriv ψ (x 2) = 0
    · simp only [hd, mul_zero]
    have hbase : graphProjectionN 2 x ∈ ball 0 r := hsβ (subset_tsupport β hb)
    have hheight : x 2 ∈ Ioo (-r) r := hsψ (support_deriv_subset hd)
    have hout : ¬ |x 2 - c| ≤ η * r := fun hh => hd (hψone (x 2) hh).2
    have hηr : 0 < η * r := mul_pos h.1.2.1 h.1.1
    rcases lt_or_gt_of_ne (show x 2 - c ≠ 0 from fun he => hout (by rw [he, abs_zero]; positivity))
      with hneg | hpos
    · have hh : x 2 < c - η * r := by
        rw [abs_of_neg hneg] at hout
        linarith
      have he := hxL ⟨hbase, hheight.1, hh⟩
      have hxH : x ∈ H := by change x 2 < c; linarith
      rw [he, indicator_of_mem hxH]
    · have hh : c + η * r < x 2 := by
        rw [abs_of_pos hpos] at hout
        linarith
      have he := hxU ⟨hbase, hh, hheight.2⟩
      have hxH : x ∉ H := by change ¬ x 2 < c; linarith
      rw [he, indicator_of_notMem hxH]
  have hH : (∫ x, H.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single 2 1)) = ∫ p, β p := by
    have he : (fun x => H.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single 2 1)) =
        H.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single 2 1)) := by
      funext x
      by_cases hx : x ∈ H <;> simp [hx]
    rw [he, integral_indicator (isOpen_smoothSubgraph continuous_const).measurableSet]
    rw [smoothSubgraph_directional_pairing (f := fun _ : EuclideanSpace ℝ (Fin 2) => c)
      contDiff_const hφ hcf]
    have hψc : ψ c = 1 := (hψone c (by simpa only [sub_self, abs_zero] using
      (mul_pos h.1.2.1 h.1.1).le)).1
    apply integral_congr_ae
    filter_upwards with p
    simp only [fderiv_const_apply, zero_apply, sub_zero]
    change (β (graphProjectionN 2 (graphAppendN p c)) * ψ ((graphAppendN p c) 2)) * 1 = β p
    rw [graphProjectionN_append, graphAppendN_height_three, hψc, mul_one, mul_one]
  exact hleft.trans (hpair.symm.trans ((integral_congr_ae hcompare).trans hH))

end LiquidDrop
