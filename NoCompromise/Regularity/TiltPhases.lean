module

public import NoCompromise.Regularity.GraphPhaseCaps

@[expose] public section

/-! # The fixed oriented phases extend to every cleared thinner slab -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma HasGraphCapPhases.narrow_slab_phases {E : Set AmbientSpace} {ω τ : ℝ}
    (h : HasGraphCapPhases E) (hE : IsOmegaMinimal E ω)
    (hτ : 0 < τ) (hτ4 : τ < 1 / 4)
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ) :
    (E.indicator (fun _ => (1 : ℝ)) =ᵐ[
      volume.restrict (lowerSlabRegion (3 / 4) 0 (4 * τ / 3))] fun _ => 1) ∧
    (E.indicator (fun _ => (1 : ℝ)) =ᵐ[
      volume.restrict (upperSlabRegion (3 / 4) 0 (4 * τ / 3))] fun _ => 0) := by
  have hslab : HasCylindricalSlab E hE.locallyFinite hE.nullMeasurable
      (3 / 4) 0 (4 * τ / 3) := by
    refine ⟨by norm_num, by positivity, by linarith, ?_, ?_⟩
    · simp only [abs_zero, zero_add]
      nlinarith
    · intro x hx
      have hxf : x ∈ frontier (densityOne E) := by
        rw [hE.frontier_densityOne]
        exact reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable hx.1
      have hs := hh x ⟨hxf, hx.2⟩
      simpa only [sub_zero, show 4 * τ / 3 * (3 / 4) = τ by ring] using hs
  obtain ⟨hl, hu⟩ := hslab.perimeter_lower_upper_eq_zero
  obtain ⟨hcapL, hcapU⟩ := h.cap_subsets hE.nullMeasurable
  have hmemL : graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (-(1 / 2 : ℝ)) ∈
      lowerSlabRegion (3 / 4) 0 (4 * τ / 3) := by
    change graphProjectionN 2 (graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (-(1 / 2 : ℝ))) ∈
      ball 0 (3 / 4) ∧ _
    rw [graphProjectionN_append]
    constructor
    · exact mem_ball_self (by norm_num)
    · change -(3 / 4 : ℝ) < graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (-(1 / 2 : ℝ)) 2 ∧
        graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (-(1 / 2 : ℝ)) 2 < 0 - 4 * τ / 3 * (3 / 4)
      rw [graphAppendN_height_three]
      constructor <;> linarith
  have hmemU : graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) ∈
      upperSlabRegion (3 / 4) 0 (4 * τ / 3) := by
    change graphProjectionN 2 (graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ)) ∈
      ball 0 (3 / 4) ∧ _
    rw [graphProjectionN_append]
    constructor
    · exact mem_ball_self (by norm_num)
    · change 0 + 4 * τ / 3 * (3 / 4) <
        graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) 2 ∧
        graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) 2 < 3 / 4
      rw [graphAppendN_height_three]
      constructor <;> linarith
  constructor
  · rcases indicator_ae_constant_phase_of_perimeter_zero hE.nullMeasurable
      (isOpen_lowerSlabRegion _ _ _) (convex_lowerSlabRegion _ _ _).isPreconnected hl with hz | ho
    · have hz0 := graphPhaseCaps_densityZero_of_zero_phase hE.nullMeasurable
        (isOpen_lowerSlabRegion _ _ _) hz hmemL
      have ho0 := hcapL ⟨0, mem_ball_self (by norm_num), rfl⟩
      exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) hz0 ho0)
    · exact ho
  · rcases indicator_ae_constant_phase_of_perimeter_zero hE.nullMeasurable
      (isOpen_upperSlabRegion _ _ _) (convex_upperSlabRegion _ _ _).isPreconnected hu with hz | ho
    · exact hz
    · have ho0 := graphPhaseCaps_densityOne_of_one_phase hE.nullMeasurable
        (isOpen_upperSlabRegion _ _ _) ho hmemU
      have hz0 := hcapU ⟨0, mem_ball_self (by norm_num), rfl⟩
      exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) hz0 ho0)

lemma HasGraphCapPhases.narrow_slab_density {E : Set AmbientSpace} {ω τ : ℝ}
    (h : HasGraphCapPhases E) (hE : IsOmegaMinimal E ω)
    (hτ : 0 < τ) (hτ4 : τ < 1 / 4)
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ) :
    lowerSlabRegion (3 / 4) 0 (4 * τ / 3) ⊆ densityOne E ∧
      upperSlabRegion (3 / 4) 0 (4 * τ / 3) ⊆ densityZero E := by
  obtain ⟨hl, hu⟩ := h.narrow_slab_phases hE hτ hτ4 hh
  exact ⟨graphPhaseCaps_densityOne_of_one_phase hE.nullMeasurable (isOpen_lowerSlabRegion _ _ _) hl,
    graphPhaseCaps_densityZero_of_zero_phase hE.nullMeasurable (isOpen_upperSlabRegion _ _ _) hu⟩

end LiquidDrop
