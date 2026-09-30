module

public import NoCompromise.Regularity.IsometryExcess
public import NoCompromise.Regularity.IsometryDensity
public import NoCompromise.Regularity.ExcessScaling

@[expose] public section

/-!
# Genuine coordinates for excess decay

Translation and positive dilation put the chosen boundary point and radius at
zero and one. An orthogonal change of coordinates puts the chosen unit axis at
the vertical axis. Quasiminimality, the actual density-one frontier, and the
canonical cylindrical excess are transported exactly.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal Topology
namespace LiquidDrop

def excessDecayCoordinates (E : Set AmbientSpace) (x : AmbientSpace) (r : ℝ)
    (ν : AmbientSpace) : Set AmbientSpace :=
  (verticalAxisIsometry ν).toAffineIsometryEquiv ⁻¹' blowupSet E x r

theorem IsOmegaMinimal.excessDecayCoordinates {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ν : AmbientSpace) : IsOmegaMinimal (LiquidDrop.excessDecayCoordinates E x r ν) (ω * r) := by
  have hB : IsOmegaMinimal (LiquidDrop.blowupSet E x r) (ω * r) := by
    apply IsOmegaMinimalAtScales.blowupSet hE x hr (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  exact hB.preimage_affineIsometry (verticalAxisIsometry ν).toAffineIsometryEquiv

lemma excessDecayCoordinates_origin_frontier (E : Set AmbientSpace) (x ν : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    (0 : AmbientSpace) ∈ frontier (densityOne (excessDecayCoordinates E x r ν)) ↔
      x ∈ frontier (densityOne E) := by
  rw [excessDecayCoordinates, frontier_densityOne_preimage_affineIsometry]
  change verticalAxisIsometry ν 0 ∈ frontier (densityOne (blowupSet E x r)) ↔ _
  rw [map_zero, mem_frontier_densityOne_blowupSet E x 0 hr]
  simp only [smul_zero, add_zero]

theorem cylindricalExcess_excessDecayCoordinates {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x ν : AmbientSpace) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (R : ℝ) (ξ : AmbientSpace) :
    cylindricalExcess (excessDecayCoordinates E x r ν)
      (hE.excessDecayCoordinates x hr hr1 ν).locallyFinite
      (hE.excessDecayCoordinates x hr hr1 ν).nullMeasurable 0 R ξ =
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (r * R)
        (verticalAxisIsometry ν ξ) := by
  unfold LiquidDrop.excessDecayCoordinates
  rw [cylindricalExcess_preimage_linearIsometry (blowupSet E x r)
      (hE.locallyFinite.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hE.nullMeasurable x hr),
    map_zero, cylindricalExcess_blowupSet E hE.locallyFinite hE.nullMeasurable x hr]
  simp only [smul_zero, add_zero]

theorem cylindricalExcess_excessDecayCoordinates_unit {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x ν : AmbientSpace) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hν : ‖ν‖ = 1) :
    cylindricalExcess (excessDecayCoordinates E x r ν)
      (hE.excessDecayCoordinates x hr hr1 ν).locallyFinite
      (hE.excessDecayCoordinates x hr hr1 ν).nullMeasurable 0 1
        (EuclideanSpace.single 2 1) =
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν := by
  rw [cylindricalExcess_excessDecayCoordinates hE x ν hr hr1, mul_one,
    verticalAxisIsometry_apply_vertical hν]

end LiquidDrop
