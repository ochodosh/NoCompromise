import NoCompromise.Regularity.DeformationLimitPhases
import NoCompromise.Regularity.SlabCapArea

/-! # No inner-wall perimeter survives the degenerate compression -/

noncomputable section
open Set MeasureTheory Filter Metric
namespace LiquidDrop

lemma not_mem_reducedBoundary_of_constant_phase {F U : Set AmbientSpace}
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (hU : IsOpen U) {a : ℝ}
    (hphase : F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => a)
    {x : AmbientSpace} (hx : x ∈ U) : x ∉ reducedBoundary F hF hmF := by
  have hz : canonicalPerimeterMeasure F hF hmF U = 0 := by
    rw [canonicalPerimeterMeasure_open F hF hmF hU]
    change variation _ U = 0
    rw [variation_congr_ae U hphase, variation_const_eq_zero]
  intro hred
  have hp := ((canonicalPerimeterMeasure F hF hmF).mem_support_iff_forall x).mp
    hred.1 U (hU.mem_nhds hx)
  rw [hz] at hp
  exact (lt_irrefl 0) hp

lemma hausdorffMeasure2_horizontal_circle (σ c : ℝ) :
    hausdorffMeasure2 3 {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ x 2 = c} = 0 := by
  have he : {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ x 2 = c} =
      (fun p : EuclideanSpace ℝ (Fin 2) => graphAppendN p c) '' sphere 0 σ := by
    ext x
    constructor
    · intro hx
      refine ⟨graphProjectionN 2 x, ?_, ?_⟩
      · simpa only [mem_sphere, dist_zero_right] using hx.1
      · rw [← hx.2]
        exact graphAppendN_projection x
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa only [mem_sphere, dist_zero_right, graphProjectionN_append] using hp,
        graphAppendN_height_three p c⟩
  rw [he]
  have hh : hausdorffMeasure2 3
      ((fun p : EuclideanSpace ℝ (Fin 2) => graphAppendN p c) '' sphere 0 σ) =
      volume (sphere (0 : EuclideanSpace ℝ (Fin 2)) σ) :=
    ((isometry_graphAppendN 2 c).euclideanHausdorffMeasure_image _).trans
      (congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) => μ (sphere 0 σ))
        hausdorffMeasure2_plane)
  rw [hh, Measure.addHaar_sphere]

theorem reducedBoundary_within_compression_envelope
    {F : Set AmbientSpace} (hF : HasLocallyFinitePerimeter F)
    (hmF : NullMeasurableSet F volume) {r σ τ c δ : ℝ}
    (hσ : 0 < σ) (hst : σ < τ)
    (hphase : ∀ᵐ x : AmbientSpace ∂volume, x ∈ standardCylinder r →
      (x 2 < c - compressionProfile σ τ (graphProjectionN 2 x) * δ →
        F.indicator (fun _ => (1 : ℝ)) x = 1) ∧
      (c + compressionProfile σ τ (graphProjectionN 2 x) * δ < x 2 →
        F.indicator (fun _ => (1 : ℝ)) x = 0)) :
    ∀ x ∈ reducedBoundary F hF hmF ∩ standardCylinder r,
      c - compressionProfile σ τ (graphProjectionN 2 x) * δ ≤ x 2 ∧
        x 2 ≤ c + compressionProfile σ τ (graphProjectionN 2 x) * δ := by
  have hp : Continuous
      (fun x : AmbientSpace => compressionProfile σ τ (graphProjectionN 2 x) * δ) :=
    ((contDiff_compressionProfile hσ hst).continuous.comp
      (graphProjectionN 2).continuous).mul_const δ
  have hz : Continuous (fun x : AmbientSpace => x 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous
  let L : Set AmbientSpace := standardCylinder r ∩
    {x | x 2 < c - compressionProfile σ τ (graphProjectionN 2 x) * δ}
  let U : Set AmbientSpace := standardCylinder r ∩
    {x | c + compressionProfile σ τ (graphProjectionN 2 x) * δ < x 2}
  have hL : IsOpen L := (isOpen_standardCylinder r).inter (isOpen_lt hz (continuous_const.sub hp))
  have hU : IsOpen U := (isOpen_standardCylinder r).inter (isOpen_lt (continuous_const.add hp) hz)
  have hl : F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict L] fun _ => 1 := by
    apply (ae_restrict_iff' hL.measurableSet).mpr
    filter_upwards [hphase] with x hx
    intro hxL
    exact (hx hxL.1).1 hxL.2
  have hu : F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 0 := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hphase] with x hx
    intro hxU
    exact (hx hxU.1).2 hxU.2
  intro x hx
  constructor
  · exact le_of_not_gt (fun hh =>
      not_mem_reducedBoundary_of_constant_phase hF hmF hL hl ⟨hx.2, hh⟩ hx.1)
  · exact le_of_not_gt (fun hh =>
      not_mem_reducedBoundary_of_constant_phase hF hmF hU hu ⟨hx.2, hh⟩ hx.1)

theorem compression_inner_wall_perimeter_zero
    {F : Set AmbientSpace} (hF : HasLocallyFinitePerimeter F)
    (hmF : NullMeasurableSet F volume) {r σ τ c δ : ℝ}
    (hσ : 0 < σ) (hst : σ < τ) (hσr : σ < r)
    (hphase : ∀ᵐ x : AmbientSpace ∂volume, x ∈ standardCylinder r →
      (x 2 < c - compressionProfile σ τ (graphProjectionN 2 x) * δ →
        F.indicator (fun _ => (1 : ℝ)) x = 1) ∧
      (c + compressionProfile σ τ (graphProjectionN 2 x) * δ < x 2 →
        F.indicator (fun _ => (1 : ℝ)) x = 0)) :
    canonicalPerimeterMeasure F hF hmF
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ |x 2| < r} = 0 := by
  have hm : MeasurableSet {x : AmbientSpace | ‖graphProjectionN 2 x‖ = σ ∧ |x 2| < r} :=
    (measurableSet_eq_fun (graphProjectionN 2).measurable.norm measurable_const).inter
      (measurableSet_lt
        (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous.abs.measurable
        measurable_const)
  rw [canonicalPerimeterMeasure_apply_eq_reducedBoundary_area F hF hmF hm]
  apply measure_mono_null _ (hausdorffMeasure2_horizontal_circle σ c)
  intro x hx
  have hxc : x ∈ standardCylinder r := ⟨hx.1.1 ▸ hσr, hx.1.2⟩
  have hb := reducedBoundary_within_compression_envelope hF hmF hσ hst hphase x ⟨hx.2, hxc⟩
  have hp : compressionProfile σ τ (graphProjectionN 2 x) = 0 :=
    compressionRadialProfile_zero hst hx.1.1.le
  rw [hp, zero_mul, sub_zero, add_zero] at hb
  exact ⟨hx.1.1, le_antisymm hb.2 hb.1⟩

end LiquidDrop
