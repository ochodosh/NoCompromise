import NoCompromise.Regularity.SlabCapArea
import NoCompromise.Regularity.SlabGeometry
import NoCompromise.Regularity.SlabDensity

/-! # The cap hypotheses determine the actual phases outside the slab -/

noncomputable section
open Set MeasureTheory Metric Filter
namespace LiquidDrop

theorem IsSlabCapConfiguration.phases_off_slab
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) :
    (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (lowerSlabRegion r c η)] fun _ => 1) ∧
      (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (upperSlabRegion r c η)] fun _ => 0) := by
  obtain ⟨hperL, hperU⟩ := h.1.perimeter_lower_upper_eq_zero
  obtain ⟨⟨p, hp, hpE⟩, ⟨q, hq, hqE⟩⟩ := h.exists_cap_phase_points
  have hgapL : -r < c - η * r := by
    linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by
    linarith [le_abs_self c, h.1.2.2.2.1]
  constructor
  · rcases indicator_ae_constant_phase_of_perimeter_zero hmE (isOpen_lowerSlabRegion r c η)
      (convex_lowerSlabRegion r c η).isPreconnected hperL with hz | ho
    · obtain ⟨δ, hδ, hballs⟩ := interior_balls_cylindricalStrip_lower hp hgapL
      exact False.elim (not_densityOne_of_zero_phase_and_interior_balls hmE
        (isOpen_lowerSlabRegion r c η).measurableSet hz hδ hballs hpE)
    · exact ho
  · rcases indicator_ae_constant_phase_of_perimeter_zero hmE (isOpen_upperSlabRegion r c η)
      (convex_upperSlabRegion r c η).isPreconnected hperU with hz | ho
    · exact hz
    · have hz : Eᶜ.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (upperSlabRegion r c η)]
          fun _ => 0 := by
        filter_upwards [ho] with x hx
        by_cases hxE : x ∈ E
        · simp [hxE]
        · simp [hxE] at hx
      have hq' : graphAppendN q r ∈ densityOne Eᶜ := by
        rw [densityOne_compl hmE]
        exact hqE
      obtain ⟨δ, hδ, hballs⟩ := interior_balls_cylindricalStrip_upper hq hgapU
      exact False.elim (not_densityOne_of_zero_phase_and_interior_balls hmE.compl
        (isOpen_upperSlabRegion r c η).measurableSet hz hδ hballs hq')

end LiquidDrop
