module

public import NoCompromise.Regularity.TiltCaps
public import NoCompromise.Regularity.TiltPlane
public import NoCompromise.Regularity.IsometryExcess

@[expose] public section

/-! # The actual slab-and-cap configuration around the new affine plane -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem IsOmegaMinimal.tilted_slab {E : Set AmbientSpace} {ω τ θ η b : ℝ}
    (hE : IsOmegaMinimal E ω) (p : EuclideanSpace ℝ (Fin 2))
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (hQ : Q (EuclideanSpace.single 2 1) = graphUnitNormal p)
    (hθ : 0 < θ) (hθ4 : 3 * θ ≤ 3 / 4) (hη : 0 < η) (hη1 : η < 1)
    (hclear : |b| + η * (2 * θ) < 2 * θ)
    (hsmall : τ + |b| + ‖p‖ * (3 * θ) < η * (2 * θ))
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ) :
    HasCylindricalSlab (Q.toAffineIsometryEquiv ⁻¹' E)
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).locallyFinite
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).nullMeasurable
      (2 * θ) (b / Real.sqrt (1 + ‖p‖ ^ 2)) η := by
  refine ⟨by positivity, hη, hη1, ?_, ?_⟩
  · have hb := graphUnitNormal_affine_offset_le p b
    linarith
  · intro x hx
    have hF := hE.preimage_affineIsometry Q.toAffineIsometryEquiv
    have hxf := hF.reducedBoundary_subset_frontier hx.1
    rw [frontier_densityOne_preimage_affineIsometry] at hxf
    have hrot : Q x ∈ cylinder 0 (2 * θ) (graphUnitNormal p) := by
      have h := (mem_cylinder_linearIsometry Q 0 x (EuclideanSpace.single 2 1)
        (2 * θ)).mpr ((standardCylinder_eq_cylinder (2 * θ)) ▸ hx.2)
      simpa only [map_zero, hQ] using h
    have hthree := rotated_cylinder_two_subset_standard_three (norm_graphUnitNormal p) hθ hrot
    have houter : Q x ∈ standardCylinder (3 / 4) :=
      ⟨hthree.1.trans_le hθ4, hthree.2.trans_le hθ4⟩
    have hheight := hh (Q x) ⟨hxf, houter⟩
    have hb := graphUnitNormal_affine_height_le p (Q x) b
    have hp := mul_le_mul_of_nonneg_left hthree.1.le (norm_nonneg p)
    have hid : x 2 = inner ℝ (graphUnitNormal p) (Q x) := by
      simpa only [Q.symm_apply_apply, hQ] using linearIsometry_inverse_vertical Q (Q x)
    rw [hid]
    exact hb.trans_lt (by linarith)

theorem HasGraphCapPhases.tilted_slab_cap_configuration
    {E : Set AmbientSpace} {ω τ θ η b : ℝ}
    (h : HasGraphCapPhases E) (hE : IsOmegaMinimal E ω)
    (p : EuclideanSpace ℝ (Fin 2)) (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (hQ : Q (EuclideanSpace.single 2 1) = graphUnitNormal p)
    (hθ : 0 < θ) (hθ4 : 4 * θ < 3 / 4)
    (hη : 0 < η) (hη1 : η < 1)
    (hτ : 0 < τ) (hτ4 : τ < 1 / 4) (hτθ : τ < θ)
    (hclose : ‖graphUnitNormal p - EuclideanSpace.single 2 1‖ ≤ 1 / 8)
    (hclear : |b| + η * (2 * θ) < 2 * θ)
    (hsmall : τ + |b| + ‖p‖ * (3 * θ) < η * (2 * θ))
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ) :
    IsSlabCapConfiguration (Q.toAffineIsometryEquiv ⁻¹' E)
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).locallyFinite
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).nullMeasurable
      (2 * θ) (b / Real.sqrt (1 + ‖p‖ ^ 2)) η := by
  obtain ⟨hl, hu⟩ := h.tilted_cap_subsets hE Q (by positivity : 0 < 2 * θ)
    (by linarith) hτ hτ4 (by linarith) (by rwa [hQ]) hh
  refine ⟨hE.tilted_slab p Q hQ hθ (by linarith) hη hη1 hclear hsmall hh, ?_, ?_⟩
  · rw [sdiff_eq_empty.mpr hl, measure_empty]
  · rw [sdiff_eq_empty.mpr hu, measure_empty]

end LiquidDrop
