module

public import NoCompromise.Regularity.IsometryPolar
public import NoCompromise.Regularity.Excess

@[expose] public section

/-! # Canonical perimeter measure and reduced-normal covariance under isometries -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem canonicalPerimeterMeasure_preimage_affineIsometry
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    canonicalPerimeterMeasure (a ⁻¹' E) (hE.preimage_affineIsometry hmE a)
      (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving) =
        Measure.map a.symm.toHomeomorph (canonicalPerimeterMeasure E hE hmE) := by
  have h := (canonicalPerimeterPolar E hE hmE).preimage_affineIsometry hmE a
  exact h.canonicalPerimeterMeasure_eq _ _

theorem reducedNormal_preimage_affineIsometry_ae
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    reducedNormal (a ⁻¹' E) (hE.preimage_affineIsometry hmE a)
      (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving) =ᵐ[
        Measure.map a.symm.toHomeomorph (canonicalPerimeterMeasure E hE hmE)]
      (fun y => a.linearIsometryEquiv.symm (reducedNormal E hE hmE (a y))) := by
  have hp := (reducedBoundary_outwardPerimeterPolar E hE hmE).preimage_affineIsometry hmE a
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE] at hp
  have hpol := hp.ae_eq_canonicalOutwardPolarDensity
    (hE.preimage_affineIsometry hmE a)
    (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)
  have hn := reducedNormal_ae_eq_polarDensity (a ⁻¹' E)
    (hE.preimage_affineIsometry hmE a)
    (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)
  rw [canonicalPerimeterMeasure_preimage_affineIsometry E hE hmE a] at hn
  exact hn.trans hpol.symm

lemma setIntegral_preimage_affineIsometry_perimeter
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    (f : AmbientSpace → ℝ) (U : Set AmbientSpace) :
    (∫ y in U, f y ∂canonicalPerimeterMeasure (a ⁻¹' E)
      (hE.preimage_affineIsometry hmE a)
      (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)) =
        ∫ y in a '' U, f (a.symm y) ∂canonicalPerimeterMeasure E hE hmE := by
  rw [canonicalPerimeterMeasure_preimage_affineIsometry E hE hmE a,
    a.symm.toHomeomorph.measurableEmbedding.setIntegral_map]
  have hs : a.symm ⁻¹' U = a '' U := by
    ext y
    constructor
    · intro hy
      exact ⟨a.symm y, hy, a.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_preimage, a.symm_apply_apply] using hx
  exact congrArg (fun A => ∫ y in A, f (a.symm y) ∂canonicalPerimeterMeasure E hE hmE) hs

/-- Exact normal excess covariance under any rigid coordinate change. -/
theorem normalExcessIntegral_preimage_affineIsometry
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    (U : Set AmbientSpace) (ν : AmbientSpace) :
    normalExcessIntegral (a ⁻¹' E) (hE.preimage_affineIsometry hmE a)
      (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving) U ν =
        normalExcessIntegral E hE hmE (a '' U) (a.linearIsometryEquiv ν) := by
  let hB := hE.preimage_affineIsometry hmE a
  let hmB := hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving
  have hnorm (y : AmbientSpace) :
      ‖a.linearIsometryEquiv.symm (reducedNormal E hE hmE (a y)) - ν‖ =
        ‖reducedNormal E hE hmE (a y) - a.linearIsometryEquiv ν‖ := by
    rw [← a.linearIsometryEquiv.norm_map
      (a.linearIsometryEquiv.symm (reducedNormal E hE hmE (a y)) - ν), map_sub,
      a.linearIsometryEquiv.apply_symm_apply]
  calc
    _ = ∫ y in U, ‖reducedNormal (a ⁻¹' E) hB hmB y - ν‖ ^ 2
        ∂canonicalPerimeterMeasure (a ⁻¹' E) hB hmB := by
      rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]
      rfl
    _ = ∫ y in U, ‖reducedNormal E hE hmE (a y) - a.linearIsometryEquiv ν‖ ^ 2
        ∂canonicalPerimeterMeasure (a ⁻¹' E) hB hmB := by
      apply integral_congr_ae
      have ha := reducedNormal_preimage_affineIsometry_ae E hE hmE a
      rw [← canonicalPerimeterMeasure_preimage_affineIsometry E hE hmE a] at ha
      filter_upwards [ae_restrict_of_ae ha] with y hy
      rw [hy, hnorm]
    _ = ∫ y in a '' U, ‖reducedNormal E hE hmE y - a.linearIsometryEquiv ν‖ ^ 2
        ∂canonicalPerimeterMeasure E hE hmE := by
      rw [setIntegral_preimage_affineIsometry_perimeter E hE hmE a]
      simp only [a.apply_symm_apply]
    _ = _ := by rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]; rfl

end LiquidDrop
