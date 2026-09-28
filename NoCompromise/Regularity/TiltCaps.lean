import NoCompromise.Regularity.TiltCapsGeometry
import NoCompromise.Regularity.TiltPhases
import NoCompromise.Regularity.IsometryDensity

/-! # Correct density phases on the actual tilted caps -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem HasGraphCapPhases.tilted_cap_subsets {E : Set AmbientSpace} {ω τ r : ℝ}
    (h : HasGraphCapPhases E) (hE : IsOmegaMinimal E ω)
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (hr : 0 < r) (hr4 : 2 * r < 3 / 4)
    (hτ : 0 < τ) (hτ4 : τ < 1 / 4) (hτr : τ < r / 2)
    (hclose : ‖Q (EuclideanSpace.single 2 1) - EuclideanSpace.single 2 1‖ ≤ 1 / 8)
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ) :
    cylindricalCap r (-r) ⊆ densityOne (Q.toAffineIsometryEquiv ⁻¹' E) ∧
      cylindricalCap r r ⊆ densityZero (Q.toAffineIsometryEquiv ⁻¹' E) := by
  obtain ⟨hl, hu⟩ := h.narrow_slab_density hE hτ hτ4 hh
  rw [densityOne_preimage_affineIsometry, densityZero_preimage_affineIsometry]
  constructor
  · rintro x ⟨p, hp, rfl⟩
    apply hl
    have hn := (linearIsometry_cap_norm_lt Q hr hp).2.trans hr4
    have hz := (linearIsometry_cap_heights Q hr hp hclose).2
    have hb := (norm_graphProjectionN_le (Q (graphAppendN p (-r)))).trans_lt hn
    have ha : |Q (graphAppendN p (-r)) 2| < 3 / 4 :=
      (abs_last_le_norm (Q (graphAppendN p (-r)))).trans_lt hn
    change graphProjectionN 2 (Q (graphAppendN p (-r))) ∈ ball 0 (3 / 4) ∧
      -(3 / 4 : ℝ) < Q (graphAppendN p (-r)) 2 ∧
      Q (graphAppendN p (-r)) 2 < 0 - (4 * τ / 3) * (3 / 4)
    refine ⟨mem_ball_zero_iff.mpr hb, (abs_lt.mp ha).1, ?_⟩
    linarith
  · rintro x ⟨p, hp, rfl⟩
    apply hu
    have hn := (linearIsometry_cap_norm_lt Q hr hp).1.trans hr4
    have hz := (linearIsometry_cap_heights Q hr hp hclose).1
    have hb := (norm_graphProjectionN_le (Q (graphAppendN p r))).trans_lt hn
    have ha : |Q (graphAppendN p r) 2| < 3 / 4 :=
      (abs_last_le_norm (Q (graphAppendN p r))).trans_lt hn
    change graphProjectionN 2 (Q (graphAppendN p r)) ∈ ball 0 (3 / 4) ∧
      0 + (4 * τ / 3) * (3 / 4) < Q (graphAppendN p r) 2 ∧
      Q (graphAppendN p r) 2 < 3 / 4
    refine ⟨mem_ball_zero_iff.mpr hb, ?_, (abs_lt.mp ha).2⟩
    linarith

end LiquidDrop
