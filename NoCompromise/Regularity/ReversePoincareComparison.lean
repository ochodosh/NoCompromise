import NoCompromise.Regularity.ReversePoincareGeometry
import NoCompromise.Regularity.ReversePoincareLocalization
import NoCompromise.Regularity.FluxDefect

/-! # The actual compression comparison bounds the flat-disk perimeter defect -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma perimeterIn_core_add_transition_le {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r σ τ : ℝ} (hst : σ < τ) :
    perimeterIn E (cylindricalCore r σ) + perimeterIn E (cylindricalTransition r σ τ) ≤
      perimeterIn E (cylindricalCore r τ) := by
  have hd : Disjoint (cylindricalCore r σ) (cylindricalTransition r σ τ) :=
    disjoint_left.mpr fun _ hx hy => hx.1.not_gt hy.1.1
  have hs : cylindricalCore r σ ∪ cylindricalTransition r σ τ ⊆ cylindricalCore r τ := by
    rintro x (hx | hx)
    · exact ⟨hx.1.trans hst, hx.2⟩
    · exact ⟨hx.1.2, hx.2⟩
  rw [← canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalCore r σ),
    ← canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalTransition r σ τ),
    ← canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalCore r τ),
    ← measure_union hd (isOpen_cylindricalTransition r σ τ).measurableSet]
  exact measure_mono hs

/-- Quasiminimality of the actual deformation, followed by finite exterior and
annular cancellation, bounds the core perimeter by its disk and height moment. -/
theorem IsOmegaMinimal.perimeter_core_le_disk_add_height
    {E : Set AmbientSpace} {ω r c η : ℝ} (hE : IsOmegaMinimal E ω)
    (h : IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η)
    (hr1 : r ≤ 1 / Real.sqrt 2)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ < r)
    (hzero : canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = τ ∧ |x 2| < r} = 0) :
    perimeterIn E (cylindricalCore r σ) ≤ ENNReal.ofReal (Real.pi * σ ^ 2) +
      ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
        ∫⁻ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
          ENNReal.ofReal ((x 2 - c) ^ 2) ∂hausdorffMeasure2 3 +
      ENNReal.ofReal ω * volume (cylindricalCore r τ) := by
  obtain ⟨F, hF, hmF, hext, _, hL, hU, hb, hw⟩ :=
    phase_preserving_cylindrical_deformation_with_outer_wall h hσ hst hτr hzero
  have hfront := canonicalPerimeterMeasure_frontier_core_zero hF hmF hτr hL hU hw
  have hcomp := hE.perimeterIn_le_of_null_frontier hF hmF (isOpen_cylindricalCore r τ)
    ((isBounded_standardCylinder r).subset inter_subset_right)
    (closure_cylindricalCore_subset_unit_ball h.1.1 hr1 hτr) hext hfront
  have hsum := perimeterIn_core_add_transition_le hE.locallyFinite hE.nullMeasurable
    (r := r) hst
  have hfin : perimeterIn E (cylindricalTransition r σ τ) < ∞ :=
    (variation_mono (isOpen_standardCylinder r).measurableSet inter_subset_right).trans_lt
      (hE.locallyFinite _ (isOpen_standardCylinder r)
        (isBounded_standardCylinder r).isCompact_closure)
  apply ENNReal.le_of_add_le_add_left hfin.ne
  have hh := hsum.trans (hcomp.trans (add_le_add hb le_rfl))
  simpa only [add_assoc, add_comm, add_left_comm] using hh

end LiquidDrop
