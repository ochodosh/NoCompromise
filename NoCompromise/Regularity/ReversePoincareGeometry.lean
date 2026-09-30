module

public import NoCompromise.Regularity.DeformationOuterWall
public import NoCompromise.Regularity.RepresentativeDensity

@[expose] public section

/-! # Boundary regularity and containment of comparison cylinders -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma cylindricalCap_eq_base_height (r c : ℝ) :
    cylindricalCap r c = {x : AmbientSpace | ‖graphProjectionN 2 x‖ < r ∧ x 2 = c} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa only [mem_ofPred_eq, graphProjectionN_append, graphAppendN_height_three, mem_ball,
      dist_zero_right, and_true] using hp
  · intro hx
    refine ⟨graphProjectionN 2 x, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using hx.1
    · rw [← hx.2]
      exact graphAppendN_projection x

lemma measurableSet_cylindricalCap (r c : ℝ) : MeasurableSet (cylindricalCap r c) := by
  rw [cylindricalCap_eq_base_height]
  exact (measurableSet_lt (graphProjectionN 2).measurable.norm measurable_const).inter
    (measurableSet_eq_fun (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).measurable
      measurable_const)

lemma canonicalPerimeterMeasure_cylindricalCap_zero_of_phase
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {r c : ℝ}
    (hphase : hausdorffMeasure2 3 (cylindricalCap r c \ densityOne E) = 0 ∨
      hausdorffMeasure2 3 (cylindricalCap r c \ densityZero E) = 0) :
    canonicalPerimeterMeasure E hE hmE (cylindricalCap r c) = 0 := by
  rw [canonicalPerimeterMeasure_apply_eq_reducedBoundary_area E hE hmE
    (measurableSet_cylindricalCap r c)]
  rcases hphase with hl | hu
  · apply measure_mono_null _ hl
    intro x hx
    exact ⟨hx.1, fun hh => reducedBoundary_subset_essentialBoundary hE hmE hx.2 (Or.inr hh)⟩
  · apply measure_mono_null _ hu
    intro x hx
    exact ⟨hx.1, fun hh => reducedBoundary_subset_essentialBoundary hE hmE hx.2 (Or.inl hh)⟩

lemma closure_cylindricalCore_subset {r s : ℝ} :
    closure (cylindricalCore r s) ⊆
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ ≤ s ∧ |x 2| ≤ r} := by
  apply closure_minimal
  · intro x hx
    exact ⟨hx.1.le, hx.2.2.le⟩
  · exact (isClosed_le (graphProjectionN 2).continuous.norm continuous_const).inter
      (isClosed_le
        (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous.abs continuous_const)

lemma frontier_cylindricalCore_subset {r s : ℝ} (hsr : s < r) :
    frontier (cylindricalCore r s) ⊆
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} ∪
        cylindricalCap r (-r) ∪ cylindricalCap r r := by
  intro x hx
  rw [(isOpen_cylindricalCore r s).frontier_eq] at hx
  have hh := closure_cylindricalCore_subset hx.1
  by_cases ht : |x 2| < r
  · have he : ‖graphProjectionN 2 x‖ = s := by
      apply le_antisymm hh.1
      by_contra hn
      have hp : ‖graphProjectionN 2 x‖ < s := lt_of_not_ge hn
      exact hx.2 ⟨hp, hp.trans hsr, ht⟩
    exact Or.inl (Or.inl ⟨he, ht⟩)
  · have he : |x 2| = r := le_antisymm hh.2 (le_of_not_gt ht)
    have hb : ‖graphProjectionN 2 x‖ < r := hh.1.trans_lt hsr
    rcases (abs_eq (show 0 ≤ r from (abs_nonneg _).trans hh.2)).mp he with hp | hn
    · exact Or.inr ((cylindricalCap_eq_base_height r r).symm ▸ ⟨hb, hp⟩)
    · exact Or.inl (Or.inr ((cylindricalCap_eq_base_height r (-r)).symm ▸ ⟨hb, hn⟩))

/-- Signed cap phases and a regular outer wall make the complete cylinder
boundary null for the actual perimeter measure. -/
theorem canonicalPerimeterMeasure_frontier_core_zero
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {r s : ℝ} (hsr : s < r)
    (hL : hausdorffMeasure2 3 (cylindricalCap r (-r) \ densityOne E) = 0)
    (hU : hausdorffMeasure2 3 (cylindricalCap r r \ densityZero E) = 0)
    (hwall : canonicalPerimeterMeasure E hE hmE
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0) :
    canonicalPerimeterMeasure E hE hmE (frontier (cylindricalCore r s)) = 0 := by
  apply measure_mono_null (frontier_cylindricalCore_subset hsr)
  exact measure_union_null (measure_union_null hwall
    (canonicalPerimeterMeasure_cylindricalCap_zero_of_phase hE hmE (Or.inl hL)))
    (canonicalPerimeterMeasure_cylindricalCap_zero_of_phase hE hmE (Or.inr hU))

lemma closure_cylindricalCore_subset_unit_ball {r s : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1 / Real.sqrt 2) (hsr : s < r) :
    closure (cylindricalCore r s) ⊆ ball (0 : AmbientSpace) 1 := by
  intro x hx
  have hh := closure_cylindricalCore_subset hx
  have hn := norm_sq_graphProjectionN x
  have ht : (x 2) ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr.le).mpr hh.2
  have hp : ‖graphProjectionN 2 x‖ ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (hh.1.trans_lt hsr)
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrm : r * Real.sqrt 2 ≤ 1 := (le_div_iff₀ hsqrt).mp hr1
  have hr2 : 2 * r ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (mul_nonneg hr.le hsqrt.le) zero_le_one).mpr hrm
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
    nlinarith
  change ‖x - 0‖ < 1
  rw [sub_zero]
  change ‖x‖ ^ 2 = ‖graphProjectionN 2 x‖ ^ 2 + (x 2) ^ 2 at hn
  nlinarith [norm_nonneg x]

end LiquidDrop
