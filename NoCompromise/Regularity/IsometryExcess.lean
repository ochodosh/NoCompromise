module

public import NoCompromise.Regularity.IsometryExcessPolar
public import NoCompromise.Regularity.IsometryCylinders
public import NoCompromise.Sobolev.LipschitzDomains

@[expose] public section

/-! # Actual cylindrical excess in orthogonal coordinates -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- A specified orthogonal map carrying the vertical axis to a given unit axis. -/
def verticalAxisIsometry (ν : AmbientSpace) : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.single 2 1 - ν))ᗮ

lemma verticalAxisIsometry_apply_vertical {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    verticalAxisIsometry ν (EuclideanSpace.single 2 1) = ν :=
  Submodule.reflection_sub (by simpa only [PiLp.norm_single, norm_one] using hν.symm)

theorem cylindricalExcess_preimage_linearIsometry
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) :
    cylindricalExcess (Q.toAffineIsometryEquiv ⁻¹' E)
      (hE.preimage_affineIsometry hmE Q.toAffineIsometryEquiv)
      (hmE.preimage
        (measurePreserving_affineIsometry Q.toAffineIsometryEquiv).quasiMeasurePreserving)
        x r ν = cylindricalExcess E hE hmE (Q x) r (Q ν) := by
  let a := Q.toAffineIsometryEquiv
  change cylindricalExcess (a ⁻¹' E) _ _ x r ν = _
  change normalExcessIntegral (a ⁻¹' E)
    (hE.preimage_affineIsometry hmE a)
    (hmE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)
    (cylinder x r ν) ν / r ^ 2 = _
  rw [normalExcessIntegral_preimage_affineIsometry E hE hmE a]
  have he : a '' cylinder x r ν = cylinder (Q x) r (Q ν) :=
    image_cylinder_linearIsometry Q x ν r
  rw [he]
  rfl

lemma linearIsometry_inverse_vertical (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (y : AmbientSpace) :
    Q.symm y 2 = inner ℝ (Q (EuclideanSpace.single 2 1)) y := by
  have he := Q.inner_map_map (EuclideanSpace.single 2 1) (Q.symm y)
  simpa only [Q.apply_symm_apply, EuclideanSpace.inner_single_left,
    one_mul, conj_trivial] using he.symm

end LiquidDrop
