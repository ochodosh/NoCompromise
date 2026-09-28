import NoCompromise.Regularity.GraphPhaseCapsCompactness

/-!
# The oriented cap conclusion in the graph approximation

The lower cap consists entirely of density-one points and the upper cap entirely
of density-zero points. This is stronger than the blueprint's conclusion modulo
Hausdorff-null sets. The actual one/zero phase bands are retained for BV slicing.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- The actual phase bands determine every point on the two interior horizontal caps. -/
theorem HasGraphCapPhases.cap_subsets {E : Set AmbientSpace}
    (h : HasGraphCapPhases E) (hmE : NullMeasurableSet E volume) :
    cylindricalCap (1 / 2) (-(1 / 2 : ℝ)) ⊆ densityOne E ∧
      cylindricalCap (1 / 2) (1 / 2) ⊆ densityZero E := by
  constructor
  · rintro x ⟨p, hp, rfl⟩
    exact graphPhaseCaps_densityOne_of_one_phase hmE isOpen_graphLowerCapRegion h.1
      (graphAppend_mem_graphLowerCapRegion hp)
  · rintro x ⟨p, hp, rfl⟩
    exact graphPhaseCaps_densityZero_of_zero_phase hmE isOpen_graphUpperCapRegion h.2
      (graphAppend_mem_graphUpperCapRegion hp)

/-- The full cap conclusion, with a genuine slab-cap configuration and actual open phase bands.
Its threshold is chosen before the set and quasiminimality coefficient. -/
theorem graph_phase_caps :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      HasGraphCapPhases E ∧
        cylindricalCap (1 / 2) (-(1 / 2 : ℝ)) ⊆ densityOne E ∧
        cylindricalCap (1 / 2) (1 / 2) ⊆ densityZero E ∧
        IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable (1 / 2) 0 (1 / 2) := by
  obtain ⟨εp, hεp, hp⟩ := graph_phase_caps_phases
  obtain ⟨εh, hεh, hh⟩ := height_bound (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨min εp εh, lt_min hεp hεh, fun E ω hE h0 he => ?_⟩
  have hphase := hp E ω hE h0 (he.trans (min_le_left _ _))
  obtain ⟨hL, hU⟩ := hphase.cap_subsets hE.nullMeasurable
  have hheight : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < 1 / 4 := by
    have ht := hh E ω hE h0 1 (by norm_num) le_rfl
      (by simpa only [mul_one] using he.trans (min_le_right _ _))
    simpa only [mul_one] using ht
  have hslab : HasCylindricalSlab E hE.locallyFinite hE.nullMeasurable
      (1 / 2) 0 (1 / 2) := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun x hx => ?_⟩
    have hx' : x ∈ frontier (densityOne E) := by
      rw [hE.frontier_densityOne]
      exact reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable hx.1
    have hs : standardCylinder (1 / 2) ⊆ standardCylinder (3 / 4) := by
      rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
      exact cylinder_mono (by norm_num)
    simpa only [sub_zero, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] using
      hheight x ⟨hx', hs hx.2⟩
  refine ⟨hphase, hL, hU, hslab, ?_, ?_⟩
  · rw [sdiff_eq_empty.mpr hL, measure_empty]
  · rw [sdiff_eq_empty.mpr hU, measure_empty]

end LiquidDrop
